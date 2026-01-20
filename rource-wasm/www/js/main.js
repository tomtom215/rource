/**
 * Rource - Main Entry Point
 *
 * Initializes the WASM application and coordinates all modules.
 */

import init, { Rource } from '../pkg/rource_wasm.js';

// Core modules
import { CONFIG, getExtensionColor } from './config.js';
import { telemetry, debugLog, validateSpeed } from './telemetry.js';
import { debounce, escapeHtml } from './utils.js';
import {
    setState, get, getRource, setRource,
    getAnimationId, setAnimationId, hasData,
    isContextLost, addManagedEventListener
} from './state.js';
import { initDomElements, getElement, getAllElements } from './dom.js';
import {
    loadPreferences, updatePreference, getPreference,
    applyPanelPreferences, setupPanelToggleHandlers
} from './preferences.js';
import { parseUrlParams, updateUrlState } from './url-state.js';
import { safeWasmCall, safeWasmVoid } from './wasm-api.js';
import { ROURCE_STATS, getFullCachedData, setAdditionalCommits, getAdditionalCommits } from './cached-data.js';

// Application modules
import { showToast, hideToast, initToast } from './toast.js';
import {
    initAnimation, resizeCanvas, startAnimation, stopAnimation,
    animate, updatePlaybackUI, setUIUpdateCallback, isAtEnd, restartAnimation
} from './animation.js';
import { loadLogData, analyzeLogData, loadRourceData, setOnDataLoadedCallback, parseCommits } from './data-loader.js';

// Feature modules
import { initScreenshot, setAnimateCallback, captureScreenshot } from './features/screenshot.js';
import { initFullscreen, toggleFullscreen } from './features/fullscreen.js';
import { initTheme, toggleTheme } from './features/theme.js';
import { initHelp, maybeShowFirstTimeHelp, showHelp } from './features/help.js';
import { initKeyboard } from './features/keyboard.js';
import { fetchGitHubWithProgress, parseGitHubUrl } from './github-fetch.js';

// ============================================================
// Initialization
// ============================================================

let parsedCommits = [];

/**
 * Main initialization function.
 */
async function main() {
    console.log('Rource: Initializing...');
    telemetry.initTime = Date.now();

    try {
        // Initialize WASM
        await init();

        // Initialize DOM references
        initDomElements();
        const elements = getAllElements();

        // Get canvas and create Rource instance
        const canvas = getElement('canvas');
        if (!canvas) {
            throw new Error('Canvas element not found');
        }

        const rource = new Rource(canvas);
        setRource(rource);

        // Check renderer type
        const isWebGL2 = rource.isWebGL2();
        const rendererType = rource.getRendererType();
        console.log(`Rource: Using ${rendererType} renderer`);

        // Update renderer badge
        if (elements.techRenderer) {
            elements.techRenderer.textContent = isWebGL2 ? 'WebGL2' : 'CPU';
        }

        // Initialize modules
        initToast();
        initTheme();
        initAnimation();
        initFullscreen();
        initHelp();
        initKeyboard();

        // Set up animation callback for screenshot
        setAnimateCallback(animate);

        // Set up UI update callback
        setUIUpdateCallback(updatePlaybackUI);

        // Set up data loaded callback
        setOnDataLoadedCallback(handleDataLoaded);

        // Apply saved preferences
        applyPanelPreferences();
        setupPanelToggleHandlers();

        // Apply saved speed preference
        const prefs = loadPreferences();
        if (elements.speedSelect) {
            elements.speedSelect.value = prefs.speed || '10';
            const speed = validateSpeed(prefs.speed || 10);
            safeWasmCall('setSpeed', () => rource.setSpeed(speed), undefined);
        }

        // Apply saved labels preference
        if (prefs.showLabels === false) {
            safeWasmCall('setShowLabels', () => rource.setShowLabels(false), undefined);
            if (elements.labelsText) elements.labelsText.textContent = 'Off';
            if (elements.btnLabels) elements.btnLabels.classList.remove('active');
        }

        // Set up event listeners
        setupEventListeners(elements, rource);

        // Enable buttons
        enableControls(elements);

        // Update showcase stats
        if (elements.showcaseCommits) elements.showcaseCommits.textContent = ROURCE_STATS.commits.toLocaleString();
        if (elements.showcaseFiles) elements.showcaseFiles.textContent = ROURCE_STATS.files.toLocaleString();
        if (elements.showcaseAuthors) elements.showcaseAuthors.textContent = ROURCE_STATS.authors.toLocaleString();

        // Start animation loop
        startAnimation();

        // Hide loading overlay
        if (elements.loadingEl) elements.loadingEl.classList.add('hidden');

        // Check URL parameters
        const urlParams = parseUrlParams();

        // Apply speed from URL
        if (urlParams.speed) {
            const speedValue = validateSpeed(urlParams.speed);
            if (elements.speedSelect) elements.speedSelect.value = String(speedValue);
            safeWasmCall('setSpeed', () => rource.setSpeed(speedValue), undefined);
        }

        // Load data based on URL params or default
        setTimeout(async () => {
            if (urlParams.repo) {
                // Load from URL param - fetch from GitHub
                console.log('Rource: Loading from URL repo param:', urlParams.repo);
                if (elements.githubUrlInput) {
                    elements.githubUrlInput.value = urlParams.repo;
                }
                if (elements.fetchStatus) {
                    elements.fetchStatus.classList.add('visible', 'loading');
                }
                const logData = await fetchGitHubWithProgress(urlParams.repo, {
                    statusEl: elements.fetchStatusText,
                });
                if (elements.fetchStatus) {
                    elements.fetchStatus.classList.remove('visible', 'loading');
                }
                if (logData) {
                    loadLogData(logData, 'custom');
                } else if (!hasData()) {
                    // Fall back to default if GitHub fetch failed
                    loadRourceData();
                }
            } else if (!hasData()) {
                // Auto-load Rource data if no URL param
                loadRourceData();
            }
        }, CONFIG.INIT_DELAY_MS);

        console.log('Rource: Initialization complete');

    } catch (error) {
        console.error('Rource: Initialization failed', error);
        showToast('Failed to initialize visualization: ' + error.message, 'error');
    }
}

/**
 * Handles data loaded event.
 */
function handleDataLoaded(content, stats) {
    const elements = getAllElements();

    // Parse commits for tooltip
    parsedCommits = parseCommits(content);

    // Update showcase stats with actual loaded data
    if (elements.showcaseCommits) elements.showcaseCommits.textContent = stats.commits.toLocaleString();
    if (elements.showcaseFiles) elements.showcaseFiles.textContent = stats.files.toLocaleString();
    if (elements.showcaseAuthors) elements.showcaseAuthors.textContent = stats.authors.size.toLocaleString();

    // Update legend with file counts
    updateLegend(content);

    // Update authors legend with commit counts
    updateAuthorsLegend(content);

    // Update timeline markers
    updateTimelineMarkers(content);

    // Show authors panel
    if (elements.authorsPanel) {
        elements.authorsPanel.classList.remove('hidden');
        elements.authorsPanel.classList.remove('collapsed');
        if (elements.authorsToggle) {
            elements.authorsToggle.setAttribute('aria-expanded', 'true');
        }
    }

    // Show legend panel
    if (elements.legendPanel) {
        elements.legendPanel.classList.remove('collapsed');
        if (elements.legendToggle) {
            elements.legendToggle.setAttribute('aria-expanded', 'true');
        }
    }

    // Auto-play the visualization
    const rource = getRource();
    if (rource) {
        safeWasmCall('play', () => rource.play(), undefined);
        updatePlaybackUI();
    }

    // Show first-time help
    maybeShowFirstTimeHelp();
}

/**
 * Enables controls after initialization.
 */
function enableControls(elements) {
    if (elements.btnPlayMain) {
        elements.btnPlayMain.disabled = false;
        elements.btnPlayMain.title = 'Play/Pause (Space)';
    }
    if (elements.btnResetBar) {
        elements.btnResetBar.disabled = false;
        elements.btnResetBar.title = 'Restart from beginning';
    }
    if (elements.btnLabels) {
        elements.btnLabels.disabled = false;
        elements.btnLabels.title = 'Toggle labels (L)';
    }
    if (elements.btnScreenshot) {
        elements.btnScreenshot.disabled = false;
        elements.btnScreenshot.title = 'Save screenshot (S)';
    }
    if (elements.btnLoad) elements.btnLoad.disabled = false;
    if (elements.btnFetchGithub) elements.btnFetchGithub.disabled = false;
    if (elements.btnVisualizeRource) elements.btnVisualizeRource.disabled = false;
}

/**
 * Sets up all event listeners.
 */
function setupEventListeners(elements, rource) {
    // Play button
    if (elements.btnPlayMain) {
        elements.btnPlayMain.addEventListener('click', () => {
            // If at end and paused, restart from beginning
            if (isAtEnd() && !safeWasmCall('isPlaying', () => rource.isPlaying(), false)) {
                safeWasmCall('seek', () => rource.seek(0), undefined);
            }
            safeWasmCall('togglePlay', () => rource.togglePlay(), undefined);
            updatePlaybackUI();
        });
    }

    // Navigation buttons
    if (elements.btnPrev) {
        elements.btnPrev.addEventListener('click', () => {
            safeWasmCall('stepBackward', () => rource.stepBackward(), undefined);
            updatePlaybackUI();
        });
    }

    if (elements.btnNext) {
        elements.btnNext.addEventListener('click', () => {
            safeWasmCall('stepForward', () => rource.stepForward(), undefined);
            updatePlaybackUI();
        });
    }

    // Reset button
    if (elements.btnResetBar) {
        elements.btnResetBar.addEventListener('click', () => {
            safeWasmCall('seek', () => rource.seek(0), undefined);
            updatePlaybackUI();
        });
    }

    // Labels toggle
    if (elements.btnLabels) {
        elements.btnLabels.addEventListener('click', () => {
            const currentState = safeWasmCall('getShowLabels', () => rource.getShowLabels(), true);
            const newState = !currentState;
            safeWasmCall('setShowLabels', () => rource.setShowLabels(newState), undefined);
            if (elements.labelsText) {
                elements.labelsText.textContent = newState ? 'On' : 'Off';
            }
            elements.btnLabels.classList.toggle('active', newState);
            updatePreference('showLabels', newState);
        });
    }

    // Screenshot button
    if (elements.btnScreenshot) {
        elements.btnScreenshot.addEventListener('click', captureScreenshot);
    }

    // Speed selector
    if (elements.speedSelect) {
        elements.speedSelect.addEventListener('change', (e) => {
            const speed = validateSpeed(e.target.value);
            safeWasmCall('setSpeed', () => rource.setSpeed(speed), undefined);
            updatePreference('speed', e.target.value);
            updateUrlState({ speed: e.target.value });
        });
    }

    // Timeline slider
    if (elements.timelineSlider) {
        elements.timelineSlider.addEventListener('input', (e) => {
            const commitIndex = parseInt(e.target.value, 10);
            safeWasmCall('pause', () => rource.pause(), undefined);
            safeWasmCall('seek', () => rource.seek(commitIndex), undefined);
            updatePlaybackUI();
        });
    }

    // Visualize Rource button
    if (elements.btnVisualizeRource) {
        elements.btnVisualizeRource.addEventListener('click', () => {
            loadRourceData();
        });
    }

    // Load button (from textarea)
    if (elements.btnLoad) {
        elements.btnLoad.addEventListener('click', () => {
            const logInput = getElement('logInput');
            if (logInput && logInput.value.trim()) {
                loadLogData(logInput.value, 'custom');
            } else {
                showToast('Please enter log data first', 'error');
            }
        });
    }

    // File input
    if (elements.fileInput) {
        elements.fileInput.addEventListener('change', handleFileSelect);
    }

    // Canvas mouse events
    setupCanvasEvents(elements.canvas, rource);

    // Window resize
    window.addEventListener('resize', debounce(resizeCanvas, CONFIG.DEBOUNCE_DELAY_MS));

    // WebGL context loss handling
    if (elements.canvas) {
        elements.canvas.addEventListener('webglcontextlost', (event) => {
            event.preventDefault();
            setState({ isContextLost: true });
            stopAnimation();
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.remove('hidden');
            }
        });

        elements.canvas.addEventListener('webglcontextrestored', () => {
            setState({ isContextLost: false });
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.add('hidden');
            }
            startAnimation();
        });
    }

    if (elements.btnRestoreContext) {
        elements.btnRestoreContext.addEventListener('click', () => {
            if (elements.contextLostOverlay) {
                elements.contextLostOverlay.classList.add('hidden');
            }
            showToast('Restoring visualization...', 'success');
            // Re-initialize after a short delay
            setTimeout(() => window.location.reload(), CONFIG.CONTEXT_RESTORE_DELAY_MS);
        });
    }

    // Legend panel toggle
    if (elements.legendToggle) {
        const toggleLegend = () => {
            if (elements.legendPanel) {
                elements.legendPanel.classList.toggle('collapsed');
                const isExpanded = !elements.legendPanel.classList.contains('collapsed');
                elements.legendToggle.setAttribute('aria-expanded', isExpanded.toString());
                updatePreference('panelStates.legend', !isExpanded);
            }
        };
        elements.legendToggle.addEventListener('click', toggleLegend);
        elements.legendToggle.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') {
                e.preventDefault();
                toggleLegend();
            }
        });
    }

    // Authors panel toggle
    if (elements.authorsToggle) {
        const toggleAuthorsPanel = () => {
            if (elements.authorsPanel) {
                elements.authorsPanel.classList.toggle('collapsed');
                const isExpanded = !elements.authorsPanel.classList.contains('collapsed');
                elements.authorsToggle.setAttribute('aria-expanded', isExpanded.toString());
                updatePreference('panelStates.authors', !isExpanded);
            }
        };
        elements.authorsToggle.addEventListener('click', toggleAuthorsPanel);
        elements.authorsToggle.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') {
                e.preventDefault();
                toggleAuthorsPanel();
            }
        });
    }

    // Performance overlay toggle
    if (elements.perfToggle) {
        const togglePerfOverlay = () => {
            if (elements.perfOverlay) {
                elements.perfOverlay.classList.toggle('collapsed');
                const isExpanded = !elements.perfOverlay.classList.contains('collapsed');
                elements.perfToggle.setAttribute('aria-expanded', isExpanded.toString());
                updatePreference('panelStates.perf', !isExpanded);
            }
        };
        elements.perfToggle.addEventListener('click', togglePerfOverlay);
        elements.perfToggle.addEventListener('keydown', (e) => {
            if (e.key === 'Enter' || e.key === ' ') {
                e.preventDefault();
                togglePerfOverlay();
            }
        });
    }

    // Uncapped FPS toggle
    if (elements.perfUncapped) {
        elements.perfUncapped.addEventListener('change', (e) => {
            const isUncapped = e.target.checked;
            setState({ uncappedFps: isUncapped });
            // Restart animation loop to switch between requestAnimationFrame and setTimeout
            restartAnimation();
            if (isUncapped) {
                showToast('Uncapped mode: Testing maximum frame rate', 'info');
            }
        });
    }

    // Tab switching (Git Command / Upload File / Paste Log)
    document.querySelectorAll('.tab-btn').forEach(btn => {
        btn.addEventListener('click', () => {
            const tab = btn.dataset.tab;
            document.querySelectorAll('.tab-btn').forEach(b => {
                b.classList.remove('active');
                b.setAttribute('aria-selected', 'false');
            });
            btn.classList.add('active');
            btn.setAttribute('aria-selected', 'true');

            document.querySelectorAll('.tab-content').forEach(c => {
                c.classList.remove('active');
                c.setAttribute('hidden', '');
            });
            const content = document.getElementById(`tab-${tab}`);
            if (content) {
                content.classList.add('active');
                content.removeAttribute('hidden');
            }
        });
    });

    // File drop zone
    if (elements.fileDropZone) {
        elements.fileDropZone.addEventListener('click', () => {
            if (elements.fileInput) elements.fileInput.click();
        });

        elements.fileDropZone.addEventListener('dragover', (e) => {
            e.preventDefault();
            elements.fileDropZone.classList.add('dragover');
        });

        elements.fileDropZone.addEventListener('dragleave', () => {
            elements.fileDropZone.classList.remove('dragover');
        });

        elements.fileDropZone.addEventListener('drop', (e) => {
            e.preventDefault();
            elements.fileDropZone.classList.remove('dragover');
            if (e.dataTransfer.files[0]) {
                handleFileUpload(e.dataTransfer.files[0]);
            }
        });
    }

    // Load file button
    if (elements.btnLoadFile) {
        elements.btnLoadFile.addEventListener('click', () => {
            if (uploadedFileContent) {
                loadLogData(uploadedFileContent, 'custom');
            } else {
                showToast('Please select a file first', 'error');
            }
        });
    }

    // GitHub fetch button
    if (elements.btnFetchGithub) {
        elements.btnFetchGithub.addEventListener('click', async () => {
            const url = elements.githubUrlInput?.value.trim();
            if (!url) {
                showToast('Please enter a GitHub repository URL.', 'error');
                return;
            }

            // Disable button during fetch
            elements.btnFetchGithub.disabled = true;
            const originalText = elements.btnFetchGithub.textContent;
            elements.btnFetchGithub.textContent = 'Fetching...';

            try {
                // Show status container and update text
                if (elements.fetchStatus) {
                    elements.fetchStatus.classList.add('visible', 'loading');
                }
                const logData = await fetchGitHubWithProgress(url, {
                    statusEl: elements.fetchStatusText,
                });

                if (logData) {
                    // Load the fetched data into visualization
                    const success = loadLogData(logData, 'custom');
                    if (success) {
                        const parsed = parseGitHubUrl(url);
                        showToast(`Loaded ${parsed?.owner}/${parsed?.repo} successfully!`, 'success');
                    }
                }
            } finally {
                elements.btnFetchGithub.disabled = false;
                elements.btnFetchGithub.textContent = originalText;
                if (elements.fetchStatus) {
                    elements.fetchStatus.classList.remove('visible', 'loading');
                }
            }
        });

        // Enter key to fetch
        if (elements.githubUrlInput) {
            elements.githubUrlInput.addEventListener('keypress', (e) => {
                if (e.key === 'Enter' && elements.btnFetchGithub) {
                    elements.btnFetchGithub.click();
                }
            });
        }
    }

    // Popular repo chips
    document.querySelectorAll('.repo-chip').forEach(chip => {
        chip.addEventListener('click', () => {
            const repo = chip.dataset.repo;
            if (elements.githubUrlInput) {
                elements.githubUrlInput.value = `https://github.com/${repo}`;
            }
            if (elements.btnFetchGithub) {
                elements.btnFetchGithub.click();
            }
        });
    });

    // Copy command button
    if (elements.btnCopyCommand) {
        elements.btnCopyCommand.addEventListener('click', async () => {
            const commandEl = document.getElementById('git-command');
            const command = commandEl?.textContent || '';
            try {
                await navigator.clipboard.writeText(command);
                elements.btnCopyCommand.innerHTML = '<svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z"/></svg> Copied!';
                setTimeout(() => {
                    elements.btnCopyCommand.innerHTML = '<svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/></svg> Copy Command';
                }, CONFIG.COPY_FEEDBACK_DELAY_MS || 2000);
            } catch (e) {
                showToast('Failed to copy. Please select and copy manually.', 'error');
            }
        });
    }

    // Share URL button
    if (elements.btnShare) {
        elements.btnShare.addEventListener('click', async () => {
            const url = generateShareableUrl();
            try {
                await navigator.clipboard.writeText(url);
                showToast('Shareable URL copied to clipboard!', 'success', 3000);
            } catch (error) {
                // Fallback for browsers without clipboard API
                const textArea = document.createElement('textarea');
                textArea.value = url;
                textArea.style.position = 'fixed';
                textArea.style.opacity = '0';
                document.body.appendChild(textArea);
                textArea.select();
                try {
                    document.execCommand('copy');
                    showToast('Shareable URL copied to clipboard!', 'success', 3000);
                } catch (e) {
                    showToast('Could not copy URL. Please copy manually: ' + url, 'error', 8000);
                }
                document.body.removeChild(textArea);
            }
        });
    }

    // Sidebar mobile toggle
    if (elements.sidebarToggle) {
        elements.sidebarToggle.addEventListener('click', () => {
            if (elements.sidebarPanel) {
                elements.sidebarPanel.classList.add('open');
            }
            if (elements.sidebarOverlay) {
                elements.sidebarOverlay.classList.add('visible');
            }
        });
    }

    if (elements.sidebarClose) {
        elements.sidebarClose.addEventListener('click', closeSidebar);
    }

    if (elements.sidebarOverlay) {
        elements.sidebarOverlay.addEventListener('click', closeSidebar);
    }

    // Scroll indicator logic
    if (elements.sidebarPanel) {
        const scrollIndicator = document.querySelector('.sidebar-scroll-indicator');
        if (scrollIndicator) {
            const checkScroll = () => {
                const scrollTop = elements.sidebarPanel.scrollTop;
                const scrollHeight = elements.sidebarPanel.scrollHeight;
                const clientHeight = elements.sidebarPanel.clientHeight;
                const nearBottom = scrollHeight - scrollTop - clientHeight < 50;
                scrollIndicator.classList.toggle('hidden', nearBottom);
            };
            elements.sidebarPanel.addEventListener('scroll', checkScroll);
            // Initial check
            setTimeout(checkScroll, 100);
        }
    }

    // Refresh Rource button (fetch latest commits from GitHub)
    if (elements.btnRefreshRource) {
        elements.btnRefreshRource.addEventListener('click', async () => {
            if (elements.btnRefreshRource.classList.contains('loading')) return;

            elements.btnRefreshRource.classList.add('loading');
            if (elements.refreshStatus) {
                elements.refreshStatus.className = 'refresh-status loading';
                elements.refreshStatus.textContent = 'Fetching latest commits...';
                elements.refreshStatus.classList.remove('hidden');
            }

            try {
                // Fetch commits since the cached timestamp
                const sinceDate = new Date(ROURCE_STATS.lastTimestamp * 1000).toISOString();
                const response = await fetch(
                    `https://api.github.com/repos/tomtom215/rource/commits?since=${sinceDate}&per_page=100`,
                    { headers: { 'Accept': 'application/vnd.github.v3+json' } }
                );

                if (!response.ok) {
                    // Check for rate limiting
                    const rateLimitRemaining = response.headers.get('X-RateLimit-Remaining');
                    const rateLimitReset = response.headers.get('X-RateLimit-Reset');

                    if (response.status === 403 && rateLimitRemaining === '0') {
                        const resetTime = rateLimitReset ? new Date(parseInt(rateLimitReset) * 1000) : null;
                        const waitMsg = resetTime
                            ? ` Try again after ${resetTime.toLocaleTimeString()}.`
                            : ' Please wait a few minutes.';
                        throw new Error(`GitHub API rate limit exceeded.${waitMsg}`);
                    }
                    throw new Error(`GitHub API error: ${response.status}`);
                }

                const commits = await response.json();

                if (commits.length <= 1) {
                    // Only the last cached commit or none - no new commits
                    if (elements.refreshStatus) {
                        elements.refreshStatus.className = 'refresh-status success';
                        elements.refreshStatus.textContent = 'Already up to date!';
                        setTimeout(() => elements.refreshStatus.classList.add('hidden'), CONFIG.STATUS_HIDE_DELAY_MS);
                    }
                } else {
                    // Fetch files for each new commit (skip the first which is our cached one)
                    let newEntries = [];
                    for (const commit of commits.slice(1)) {
                        const timestamp = Math.floor(new Date(commit.commit.author.date).getTime() / 1000);
                        const author = commit.commit.author.name || 'Unknown';

                        // Fetch commit details for files
                        const detailResponse = await fetch(commit.url, {
                            headers: { 'Accept': 'application/vnd.github.v3+json' }
                        });

                        if (detailResponse.ok) {
                            const detail = await detailResponse.json();
                            for (const file of (detail.files || [])) {
                                const action = file.status === 'added' ? 'A'
                                    : file.status === 'removed' ? 'D' : 'M';
                                newEntries.push(`${timestamp}|${author}|${action}|${file.filename}`);
                            }
                        }
                    }

                    if (newEntries.length > 0) {
                        setAdditionalCommits(newEntries.join('\n'));
                        const newCommitCount = commits.length - 1;

                        // Count unique files and authors from new entries
                        const newFiles = new Set();
                        const newAuthors = new Set();
                        for (const entry of newEntries) {
                            const parts = entry.split('|');
                            if (parts.length >= 4) {
                                newAuthors.add(parts[1]);
                                newFiles.add(parts[3]);
                            }
                        }

                        if (elements.refreshStatus) {
                            elements.refreshStatus.className = 'refresh-status success';
                            elements.refreshStatus.textContent = `Found ${newCommitCount} new commit${newCommitCount === 1 ? '' : 's'} (${newFiles.size} files). Click "Visualize" to reload.`;
                        }

                        // Update showcase stats with "+" to indicate more data pending
                        if (elements.showcaseCommits) {
                            const totalCommits = ROURCE_STATS.commits + newCommitCount;
                            elements.showcaseCommits.textContent = totalCommits.toLocaleString() + '+';
                        }
                        if (elements.showcaseFiles) {
                            const totalFiles = ROURCE_STATS.files + newFiles.size;
                            elements.showcaseFiles.textContent = totalFiles.toLocaleString() + '+';
                        }
                        if (elements.showcaseAuthors) {
                            // Authors may overlap, so just show a "+" indicator
                            elements.showcaseAuthors.textContent = ROURCE_STATS.authors.toLocaleString() + '+';
                        }
                    } else {
                        if (elements.refreshStatus) {
                            elements.refreshStatus.className = 'refresh-status success';
                            elements.refreshStatus.textContent = 'Already up to date!';
                            setTimeout(() => elements.refreshStatus.classList.add('hidden'), CONFIG.STATUS_HIDE_DELAY_MS);
                        }
                    }
                }
            } catch (error) {
                console.error('Refresh error:', error);
                if (elements.refreshStatus) {
                    elements.refreshStatus.className = 'refresh-status error';
                    elements.refreshStatus.textContent = error.message || 'Failed to fetch updates';
                }
                showToast('Failed to fetch updates: ' + error.message, 'error');
            } finally {
                elements.btnRefreshRource.classList.remove('loading');
            }
        });
    }
}

// Track uploaded file content
let uploadedFileContent = null;

/**
 * Handles file upload.
 */
function handleFileUpload(file) {
    const elements = getAllElements();
    const MAX_FILE_SIZE = 10 * 1024 * 1024; // 10MB

    if (file.size > MAX_FILE_SIZE) {
        showToast('File too large. Maximum size is 10MB.', 'error');
        return;
    }

    // Show loading state
    if (elements.fileNameEl) {
        elements.fileNameEl.textContent = `Loading ${file.name}...`;
        elements.fileNameEl.classList.remove('hidden');
    }
    if (elements.btnLoadFile) {
        elements.btnLoadFile.disabled = true;
    }

    const reader = new FileReader();

    reader.onload = (e) => {
        uploadedFileContent = e.target.result;
        if (elements.fileNameEl) {
            elements.fileNameEl.textContent = `${file.name} (${(file.size / 1024).toFixed(1)} KB)`;
        }
        if (elements.btnLoadFile) {
            elements.btnLoadFile.disabled = false;
        }
    };

    reader.onerror = () => {
        if (elements.fileNameEl) {
            elements.fileNameEl.textContent = 'Failed to read file';
        }
        showToast('Failed to read file. Please try again.', 'error');
    };

    reader.readAsText(file);
}

/**
 * Closes the sidebar (mobile).
 */
function closeSidebar() {
    const elements = getAllElements();
    if (elements.sidebarPanel) {
        elements.sidebarPanel.classList.remove('open');
    }
    if (elements.sidebarOverlay) {
        elements.sidebarOverlay.classList.remove('visible');
    }
}

/**
 * Generates a shareable URL with current state.
 */
function generateShareableUrl() {
    const rource = getRource();
    const elements = getAllElements();
    const params = new URLSearchParams();

    // Add speed if not default
    const currentSpeed = elements.speedSelect?.value;
    if (currentSpeed && currentSpeed !== '10') {
        params.set('speed', currentSpeed);
    }

    // Add current commit position
    if (rource && hasData()) {
        const current = safeWasmCall('currentCommit', () => rource.currentCommit(), 0);
        const total = safeWasmCall('commitCount', () => rource.commitCount(), 0);
        if (current > 0 && current < total - 1) {
            params.set('commit', current.toString());
        }
    }

    // Build URL
    const baseUrl = window.location.origin + window.location.pathname;
    const queryString = params.toString();
    return queryString ? `${baseUrl}?${queryString}` : baseUrl;
}

/**
 * Sets up canvas mouse/touch events.
 *
 * Uses WASM mouse event handlers for entity dragging and camera panning.
 * The WASM code internally handles hit-testing entities (files, users) and
 * decides whether to drag an entity or pan the camera.
 */
function setupCanvasEvents(canvas, rource) {
    if (!canvas) return;

    // Convert client coordinates to canvas-relative coordinates
    function getCanvasCoords(clientX, clientY) {
        const rect = canvas.getBoundingClientRect();
        return {
            x: clientX - rect.left,
            y: clientY - rect.top
        };
    }

    // Mouse events - delegate to WASM for entity drag / camera pan handling
    canvas.addEventListener('mousedown', (e) => {
        const { x, y } = getCanvasCoords(e.clientX, e.clientY);
        safeWasmVoid('onMouseDown', () => rource.onMouseDown(x, y));
        canvas.style.cursor = 'grabbing';
    });

    canvas.addEventListener('mousemove', (e) => {
        const { x, y } = getCanvasCoords(e.clientX, e.clientY);
        // Always call onMouseMove - WASM tracks mouse_down state internally
        safeWasmVoid('onMouseMove', () => rource.onMouseMove(x, y));
    });

    canvas.addEventListener('mouseup', () => {
        safeWasmVoid('onMouseUp', () => rource.onMouseUp());
        canvas.style.cursor = 'grab';
    });

    canvas.addEventListener('mouseleave', () => {
        safeWasmVoid('onMouseUp', () => rource.onMouseUp());
        canvas.style.cursor = 'grab';
    });

    // Wheel events - use WASM onWheel for zoom-toward-cursor
    canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const { x, y } = getCanvasCoords(e.clientX, e.clientY);
        safeWasmVoid('onWheel', () => rource.onWheel(e.deltaY, x, y));
    }, { passive: false });

    // Touch events for mobile
    let touchStartDist = 0;
    let lastTouchX = 0;
    let lastTouchY = 0;

    canvas.addEventListener('touchstart', (e) => {
        if (e.touches.length === 1) {
            const { x, y } = getCanvasCoords(e.touches[0].clientX, e.touches[0].clientY);
            lastTouchX = x;
            lastTouchY = y;
            safeWasmVoid('onMouseDown', () => rource.onMouseDown(x, y));
        } else if (e.touches.length === 2) {
            touchStartDist = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
        }
    });

    canvas.addEventListener('touchmove', (e) => {
        e.preventDefault();
        if (e.touches.length === 1) {
            const { x, y } = getCanvasCoords(e.touches[0].clientX, e.touches[0].clientY);
            safeWasmVoid('onMouseMove', () => rource.onMouseMove(x, y));
            lastTouchX = x;
            lastTouchY = y;
        } else if (e.touches.length === 2) {
            const dist = Math.hypot(
                e.touches[0].clientX - e.touches[1].clientX,
                e.touches[0].clientY - e.touches[1].clientY
            );
            if (touchStartDist > 0) {
                const factor = dist / touchStartDist;
                safeWasmCall('zoom', () => rource.zoom(factor), undefined);
                touchStartDist = dist;
            }
        }
    }, { passive: false });

    canvas.addEventListener('touchend', () => {
        safeWasmVoid('onMouseUp', () => rource.onMouseUp());
        touchStartDist = 0;
    });

    canvas.style.cursor = 'grab';
}

/**
 * Handles file selection.
 */
function handleFileSelect(e) {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (event) => {
        const content = event.target.result;
        loadLogData(content, 'custom');

        const fileNameEl = getElement('fileNameEl');
        if (fileNameEl) {
            fileNameEl.textContent = file.name;
        }
    };
    reader.onerror = () => {
        showToast('Failed to read file', 'error');
    };
    reader.readAsText(file);
}

/**
 * Updates the file types legend with file counts.
 */
function updateLegend(content) {
    const legendItems = getElement('legendItems');
    if (!legendItems) return;

    // Count files per extension
    const extensionCounts = new Map();
    const lines = content.split('\n');
    const processedFiles = new Set(); // Track unique files

    for (const line of lines) {
        const parts = line.split('|');
        if (parts.length >= 4) {
            const file = parts[3].trim();
            // Only count unique files
            if (!processedFiles.has(file)) {
                processedFiles.add(file);
                const ext = file.includes('.') ? file.split('.').pop()?.toLowerCase() : '';
                if (ext) {
                    extensionCounts.set(ext, (extensionCounts.get(ext) || 0) + 1);
                }
            }
        }
    }

    // Sort by count descending
    const sortedExts = Array.from(extensionCounts.entries())
        .sort((a, b) => b[1] - a[1])
        .slice(0, 20); // Limit to 20

    // Build legend HTML
    let html = '';
    for (const [ext, count] of sortedExts) {
        const color = getExtensionColor(ext);
        html += `<div class="legend-item">
            <span class="legend-color" style="background-color: ${escapeHtml(color)}"></span>
            <span class="legend-label">.${escapeHtml(ext)}</span>
            <span class="legend-count">${count}</span>
        </div>`;
    }

    legendItems.innerHTML = html;
}

/**
 * Updates the authors legend with commit counts.
 */
function updateAuthorsLegend(content) {
    const authorsItems = getElement('authorsItems');
    const rource = getRource();
    if (!authorsItems || !rource) return;

    try {
        // Count commits per author from content
        const authorCommitCounts = new Map();
        if (content) {
            const lines = content.split('\n');
            const seenCommits = new Set(); // Track unique timestamp+author combos

            for (const line of lines) {
                const parts = line.split('|');
                if (parts.length >= 4) {
                    const timestamp = parts[0].trim();
                    const author = parts[1].trim();
                    const commitKey = `${timestamp}|${author}`;
                    if (!seenCommits.has(commitKey)) {
                        seenCommits.add(commitKey);
                        authorCommitCounts.set(author, (authorCommitCounts.get(author) || 0) + 1);
                    }
                }
            }
        }

        // Sort by commit count descending
        const sortedAuthors = Array.from(authorCommitCounts.entries())
            .sort((a, b) => b[1] - a[1])
            .slice(0, 30); // Limit to 30

        let html = '';

        for (const [author, commitCount] of sortedAuthors) {
            const color = safeWasmCall('getAuthorColor', () => rource.getAuthorColor(author), '#888');
            html += `<div class="author-item" data-author="${escapeHtml(author)}">
                <span class="author-color" style="background-color: ${escapeHtml(color)}"></span>
                <span class="author-name">${escapeHtml(author)}</span>
                <span class="author-commits">${commitCount}</span>
            </div>`;
        }

        authorsItems.innerHTML = html;
    } catch {
        // Authors may not be available yet
    }
}

/**
 * Updates timeline markers for significant commits.
 */
function updateTimelineMarkers(content) {
    const timelineMarkers = getElement('timelineMarkers');
    if (!timelineMarkers) return;

    // Clear existing markers
    timelineMarkers.innerHTML = '';

    // This is a simplified version - the full implementation would
    // identify significant commits (large changes, milestones, etc.)
}

// Start the application
main().catch(console.error);

/**
 * Rource - Data Input Handling
 *
 * Handles file upload, paste, GitHub fetch, and repository selection.
 * Single responsibility: loading visualization data from various sources.
 */

import { getRource, hasData, addManagedEventListener } from '../state.js';
import { safeWasmCall } from '../wasm-api.js';
import { getElement, getAllElements } from '../dom.js';
import { showToast } from '../toast.js';
import { CONFIG } from '../config.js';
import { loadLogData, loadRourceData } from '../data-loader.js';
import { fetchGitHubWithProgress, parseGitHubUrl } from '../github-fetch.js';
import { ROURCE_STATS, setAdditionalCommits } from '../cached-data.js';

/**
 * Uploaded file content storage.
 */
let uploadedFileContent = null;

/**
 * Handles file upload from input or drop.
 * @param {File} file - File to upload
 */
function handleFileUpload(file) {
    const elements = getAllElements();

    if (file.size > CONFIG.MAX_FILE_SIZE_BYTES) {
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
 * Handles file input change event.
 * @param {Event} e - Change event
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
 * Initializes visualize Rource button.
 */
function initVisualizeRource() {
    const btnVisualizeRource = getElement('btnVisualizeRource');
    if (!btnVisualizeRource) return;

    addManagedEventListener(btnVisualizeRource, 'click', () => {
        loadRourceData();
    });
}

/**
 * Initializes load from textarea button.
 */
function initLoadFromTextarea() {
    const btnLoad = getElement('btnLoad');
    if (!btnLoad) return;

    addManagedEventListener(btnLoad, 'click', () => {
        const logInput = getElement('logInput');
        if (logInput && logInput.value.trim()) {
            loadLogData(logInput.value, 'custom');
        } else {
            showToast('Please enter log data first', 'error');
        }
    });
}

/**
 * Initializes file input handler.
 */
function initFileInput() {
    const fileInput = getElement('fileInput');
    if (!fileInput) return;

    addManagedEventListener(fileInput, 'change', handleFileSelect);
}

/**
 * Initializes file drop zone.
 */
function initFileDropZone() {
    const fileDropZone = getElement('fileDropZone');
    const fileInput = getElement('fileInput');
    if (!fileDropZone) return;

    addManagedEventListener(fileDropZone, 'click', () => {
        if (fileInput) fileInput.click();
    });

    addManagedEventListener(fileDropZone, 'dragover', (e) => {
        e.preventDefault();
        fileDropZone.classList.add('dragover');
    });

    addManagedEventListener(fileDropZone, 'dragleave', () => {
        fileDropZone.classList.remove('dragover');
    });

    addManagedEventListener(fileDropZone, 'drop', (e) => {
        e.preventDefault();
        fileDropZone.classList.remove('dragover');
        if (e.dataTransfer.files[0]) {
            handleFileUpload(e.dataTransfer.files[0]);
        }
    });
}

/**
 * Initializes load file button (after file upload).
 */
function initLoadFileButton() {
    const btnLoadFile = getElement('btnLoadFile');
    if (!btnLoadFile) return;

    addManagedEventListener(btnLoadFile, 'click', () => {
        if (uploadedFileContent) {
            loadLogData(uploadedFileContent, 'custom');
        } else {
            showToast('Please select a file first', 'error');
        }
    });
}

/**
 * Initializes GitHub fetch functionality.
 */
function initGitHubFetch() {
    const btnFetchGithub = getElement('btnFetchGithub');
    const githubUrlInput = getElement('githubUrlInput');
    const elements = getAllElements();

    if (!btnFetchGithub) return;

    addManagedEventListener(btnFetchGithub, 'click', async () => {
        const url = githubUrlInput?.value.trim();
        if (!url) {
            showToast('Please enter a GitHub repository URL.', 'error');
            return;
        }

        // Disable button during fetch
        btnFetchGithub.disabled = true;
        const originalText = btnFetchGithub.textContent;
        btnFetchGithub.textContent = 'Fetching...';

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
            btnFetchGithub.disabled = false;
            btnFetchGithub.textContent = originalText;
            if (elements.fetchStatus) {
                elements.fetchStatus.classList.remove('visible', 'loading');
            }
        }
    });

    // Enter key to fetch
    if (githubUrlInput) {
        addManagedEventListener(githubUrlInput, 'keypress', (e) => {
            if (e.key === 'Enter' && btnFetchGithub) {
                btnFetchGithub.click();
            }
        });
    }
}

/**
 * Initializes popular repo chip clicks.
 */
function initRepoChips() {
    const chips = document.querySelectorAll('.repo-chip');
    const githubUrlInput = getElement('githubUrlInput');
    const btnFetchGithub = getElement('btnFetchGithub');

    chips.forEach(chip => {
        addManagedEventListener(chip, 'click', () => {
            const repo = chip.dataset.repo;
            if (githubUrlInput) {
                githubUrlInput.value = `https://github.com/${repo}`;
            }
            if (btnFetchGithub) {
                btnFetchGithub.click();
            }
        });
    });
}

/**
 * Initializes copy command button.
 */
function initCopyCommand() {
    const btnCopyCommand = getElement('btnCopyCommand');
    if (!btnCopyCommand) return;

    addManagedEventListener(btnCopyCommand, 'click', async () => {
        const commandEl = document.getElementById('git-command');
        const command = commandEl?.textContent || '';
        try {
            await navigator.clipboard.writeText(command);
            btnCopyCommand.innerHTML = '<svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z"/></svg> Copied!';
            setTimeout(() => {
                btnCopyCommand.innerHTML = '<svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/></svg> Copy Command';
            }, CONFIG.COPY_FEEDBACK_DELAY_MS);
        } catch (e) {
            showToast('Failed to copy. Please select and copy manually.', 'error');
        }
    });
}

/**
 * Generates a shareable URL with current state.
 * @returns {string} Shareable URL
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
 * Initializes share URL button.
 */
function initShareUrl() {
    const btnShare = getElement('btnShare');
    if (!btnShare) return;

    addManagedEventListener(btnShare, 'click', async () => {
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

/**
 * Initializes refresh Rource button (fetch latest commits).
 */
function initRefreshRource() {
    const btnRefreshRource = getElement('btnRefreshRource');
    const elements = getAllElements();
    if (!btnRefreshRource) return;

    addManagedEventListener(btnRefreshRource, 'click', async () => {
        if (btnRefreshRource.classList.contains('loading')) return;

        btnRefreshRource.classList.add('loading');
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
            btnRefreshRource.classList.remove('loading');
        }
    });
}

/**
 * Initializes all data input event listeners.
 */
export function initDataInput() {
    initVisualizeRource();
    initLoadFromTextarea();
    initFileInput();
    initFileDropZone();
    initLoadFileButton();
    initGitHubFetch();
    initRepoChips();
    initCopyCommand();
    initShareUrl();
    initRefreshRource();
}

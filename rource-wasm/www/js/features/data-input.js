// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

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
import { loadLogData, loadRourceData, detectLogFormat } from '../data-loader.js';
import { fetchGitHubWithProgress, parseGitHubUrl, getRateLimitStatus, updateRateLimitFromResponse } from '../github-fetch.js';
import { ROURCE_STATS, setAdditionalCommits } from '../cached-data.js';
import { formatBytes } from '../utils.js';

/**
 * Uploaded file content storage (for "Load Uploaded File" button fallback).
 */
let uploadedFileContent = null;

/**
 * Handles file upload from drag-and-drop.
 * Auto-loads the file content like file browse does.
 * @param {File} file - File to upload
 */
function handleFileUpload(file) {
    const fileNameEl = getElement('fileNameEl');

    // Show loading state
    if (fileNameEl) {
        fileNameEl.textContent = `Loading ${file.name}...`;
        fileNameEl.classList.remove('hidden');
    }

    const reader = new FileReader();

    reader.onload = (e) => {
        const content = e.target.result;
        // Store for "Load Uploaded File" button fallback
        uploadedFileContent = content;

        // Show filename with size
        if (fileNameEl) {
            fileNameEl.textContent = `${file.name} (${formatBytes(file.size)})`;
        }

        // Auto-detect format and load (consistent with file browse behavior)
        const format = detectLogFormat(content);
        if (format === 'unknown') {
            showToast('Unknown log format. Trying custom format...', 'warning', 3000);
        }
        loadLogData(content, format === 'unknown' ? 'custom' : format);
    };

    reader.onerror = () => {
        if (fileNameEl) {
            fileNameEl.textContent = 'Failed to read file';
        }
        showToast('Failed to read file. Please try again.', 'error');
    };

    reader.readAsText(file);
}

/**
 * Handles file input change event (file browse).
 * @param {Event} e - Change event
 */
function handleFileSelect(e) {
    const file = e.target.files[0];
    if (!file) return;

    const fileNameEl = getElement('fileNameEl');

    // Show loading state
    if (fileNameEl) {
        fileNameEl.textContent = `Loading ${file.name}...`;
        fileNameEl.classList.remove('hidden');
    }

    const reader = new FileReader();
    reader.onload = (event) => {
        const content = event.target.result;
        // Store for "Load Uploaded File" button fallback
        uploadedFileContent = content;

        // Show filename with size
        if (fileNameEl) {
            fileNameEl.textContent = `${file.name} (${formatBytes(file.size)})`;
        }

        // Auto-detect format and load
        const format = detectLogFormat(content);
        if (format === 'unknown') {
            showToast('Unknown log format. Trying custom format...', 'warning', 3000);
        }
        loadLogData(content, format === 'unknown' ? 'custom' : format);
    };
    reader.onerror = () => {
        if (fileNameEl) {
            fileNameEl.textContent = 'Failed to read file';
        }
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
            const content = logInput.value;
            // Auto-detect format
            const format = detectLogFormat(content);
            loadLogData(content, format === 'unknown' ? 'custom' : format);
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
            // Auto-detect format
            const format = detectLogFormat(uploadedFileContent);
            loadLogData(uploadedFileContent, format === 'unknown' ? 'custom' : format);
        } else {
            showToast('Please select a file first', 'error');
        }
    });
}

/**
 * Creates an SVG icon element safely (no innerHTML).
 * @param {string} pathD - SVG path d attribute
 * @returns {SVGElement} SVG element
 */
function createRateLimitIcon(pathD) {
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('class', 'rate-limit-icon');
    svg.setAttribute('viewBox', '0 0 24 24');
    svg.setAttribute('fill', 'currentColor');

    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', pathD);
    svg.appendChild(path);

    return svg;
}

/**
 * Updates the rate limit status display in the UI.
 * Uses textContent instead of innerHTML to prevent XSS.
 */
function updateRateLimitStatusUI() {
    const elements = getAllElements();
    const statusEl = elements.rateLimitStatus;
    if (!statusEl) return;

    const status = getRateLimitStatus();

    // Clear existing content safely
    statusEl.textContent = '';
    statusEl.className = 'rate-limit-status';

    // Icon paths
    const checkIconPath = 'M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm-2 15l-5-5 1.41-1.41L10 14.17l7.59-7.59L19 8l-9 9z';
    const warningIconPath = 'M1 21h22L12 2 1 21zm12-3h-2v-2h2v2zm0-4h-2v-4h2v4z';

    if (status.isExhausted) {
        statusEl.classList.add('exhausted');
        statusEl.appendChild(createRateLimitIcon(checkIconPath));
        const span = document.createElement('span');
        span.textContent = `Rate limit exhausted. Resets at ${status.resetTime?.toLocaleTimeString() || 'soon'}.`;
        statusEl.appendChild(span);
    } else if (status.isLow) {
        statusEl.classList.add('low');
        statusEl.appendChild(createRateLimitIcon(warningIconPath));
        const span = document.createElement('span');
        span.textContent = `Low API quota: ${status.remaining}/${status.limit} requests remaining.`;
        statusEl.appendChild(span);
    } else if (status.remaining < status.limit) {
        // Show status if we've made some requests
        statusEl.classList.add('ok');
        statusEl.appendChild(createRateLimitIcon(checkIconPath));
        const span = document.createElement('span');
        span.textContent = `API quota: ${status.remaining}/${status.limit} requests remaining.`;
        statusEl.appendChild(span);
    } else {
        // Full quota - hide the status
        statusEl.classList.add('hidden');
    }
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
            // Update rate limit status after fetch attempt
            updateRateLimitStatusUI();
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
            // Check rate limit before allowing click
            const status = getRateLimitStatus();
            if (status.isExhausted) {
                showToast(`Rate limit exhausted. Try again after ${status.resetTime?.toLocaleTimeString() || 'some time'}.`, 'error', 5000);
                updateRateLimitStatusUI();
                return;
            }

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
 * Creates an SVG element with the given path.
 * @param {string} pathD - SVG path d attribute
 * @returns {SVGElement} SVG element
 */
function createCopyIcon(pathD) {
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('width', '12');
    svg.setAttribute('height', '12');
    svg.setAttribute('viewBox', '0 0 24 24');
    svg.setAttribute('fill', 'currentColor');

    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', pathD);
    svg.appendChild(path);

    return svg;
}

/**
 * Updates the copy button state using safe DOM APIs (no innerHTML).
 * @param {HTMLElement} btn - Button element
 * @param {boolean} copied - True if copied state, false for default state
 */
function updateCopyButtonState(btn, copied) {
    // Clear existing content
    while (btn.firstChild) {
        btn.removeChild(btn.firstChild);
    }

    if (copied) {
        // Checkmark icon
        const checkPath = 'M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z';
        btn.appendChild(createCopyIcon(checkPath));
        btn.appendChild(document.createTextNode(' Copied!'));
    } else {
        // Copy icon
        const copyPath = 'M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z';
        btn.appendChild(createCopyIcon(copyPath));
        btn.appendChild(document.createTextNode(' Copy Command'));
    }
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
            // Update button using safe DOM APIs (no innerHTML)
            updateCopyButtonState(btnCopyCommand, true);
            setTimeout(() => {
                updateCopyButtonState(btnCopyCommand, false);
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
            // Check rate limit before starting
            const rateLimitStatus = getRateLimitStatus();
            if (rateLimitStatus.isExhausted) {
                throw new Error(`GitHub API rate limit exhausted. Try again after ${rateLimitStatus.resetTime?.toLocaleTimeString() || 'some time'}.`);
            }

            // Fetch commits since the cached timestamp
            const sinceDate = new Date(ROURCE_STATS.lastTimestamp * 1000).toISOString();
            const response = await fetch(
                `https://api.github.com/repos/tomtom215/rource/commits?since=${sinceDate}&per_page=100`,
                { headers: { 'Accept': 'application/vnd.github.v3+json' } }
            );

            // Update shared rate limit state
            updateRateLimitFromResponse(response);

            if (!response.ok) {
                if (response.status === 403 && getRateLimitStatus().remaining === 0) {
                    const status = getRateLimitStatus();
                    throw new Error(`GitHub API rate limit exceeded. Try again after ${status.resetTime?.toLocaleTimeString() || 'some time'}.`);
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
                    // Check rate limit before each request
                    if (getRateLimitStatus().remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER) {
                        console.warn('Stopping refresh early: rate limit low');
                        break;
                    }

                    const timestamp = Math.floor(new Date(commit.commit.author.date).getTime() / 1000);
                    const author = (commit.commit.author.name || 'Unknown').replace(/\|/g, '_');

                    // Fetch commit details for files
                    const detailResponse = await fetch(commit.url, {
                        headers: { 'Accept': 'application/vnd.github.v3+json' }
                    });

                    // Update shared rate limit state
                    updateRateLimitFromResponse(detailResponse);

                    if (detailResponse.ok) {
                        const detail = await detailResponse.json();
                        for (const file of (detail.files || [])) {
                            const action = file.status === 'added' ? 'A'
                                : file.status === 'removed' ? 'D' : 'M';
                            const filename = file.filename.replace(/\|/g, '_');
                            newEntries.push(`${timestamp}|${author}|${action}|${filename}`);
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
            // Update rate limit status after refresh attempt
            updateRateLimitStatusUI();
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

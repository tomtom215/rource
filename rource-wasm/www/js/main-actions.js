// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - UI Action Handlers
 *
 * Bottom sheet and analytics dashboard action wiring.
 * Connects UI buttons to existing functionality in feature modules.
 */

import { getRource, get, addManagedEventListener, subscribe } from './state.js';
import { safeWasmCall } from './wasm-api.js';
import { updatePlaybackUI } from './animation.js';
import { loadLogData, loadRourceData } from './data-loader.js';
import { fetchGitHubWithProgress } from './github-fetch.js';
import { showToast } from './toast.js';
import { openBottomSheet, closeBottomSheet } from './features/bottom-sheet.js';
import { showControls } from './features/mobile-controls.js';
import { switchToVisualization } from './features/view-manager.js';

/**
 * Initializes bottom sheet button actions.
 * Connects bottom sheet UI to existing functionality.
 */
export function initBottomSheetActions() {
    const bsVisualizeBtn = document.getElementById('bs-visualize-rource');
    const bsFetchRepoBtn = document.getElementById('bs-fetch-repo');
    const bsGithubUrl = document.getElementById('bs-github-url');
    const bsFetchBtn = document.getElementById('bs-fetch-btn');
    const bsFab = document.getElementById('bottom-sheet-fab');

    if (bsVisualizeBtn) {
        bsVisualizeBtn.disabled = false;
        addManagedEventListener(bsVisualizeBtn, 'click', () => {
            loadRourceData();
            closeBottomSheet();
        });
    }

    if (bsFetchRepoBtn) {
        addManagedEventListener(bsFetchRepoBtn, 'click', () => {
            if (bsGithubUrl) {
                bsGithubUrl.focus();
                bsGithubUrl.scrollIntoView({ behavior: 'smooth', block: 'center' });
            }
        });
    }

    if (bsGithubUrl && bsFetchBtn) {
        bsFetchBtn.disabled = false;
        addManagedEventListener(bsGithubUrl, 'input', () => {
            bsFetchBtn.disabled = !bsGithubUrl.value.trim();
        });

        addManagedEventListener(bsFetchBtn, 'click', async () => {
            const input = bsGithubUrl.value.trim();
            if (!input) return;

            let repo = input;
            const urlMatch = input.match(/github\.com\/([^\/]+\/[^\/]+)/);
            if (urlMatch) {
                repo = urlMatch[1];
            }

            bsFetchBtn.disabled = true;
            bsGithubUrl.disabled = true;

            try {
                const logData = await fetchGitHubWithProgress(repo, {
                    statusEl: null,
                });

                if (logData) {
                    loadLogData(logData, 'custom');
                    closeBottomSheet();
                    showToast(`Loaded ${repo}`, 'success');
                } else {
                    showToast('Failed to fetch repository', 'error');
                }
            } catch (error) {
                showToast('Error fetching repository: ' + error.message, 'error');
            } finally {
                bsFetchBtn.disabled = false;
                bsGithubUrl.disabled = false;
            }
        });

        addManagedEventListener(bsGithubUrl, 'keydown', (e) => {
            if (e.key === 'Enter' && !bsFetchBtn.disabled) {
                bsFetchBtn.click();
            }
        });
    }

    if (bsFab) {
        addManagedEventListener(bsFab, 'click', () => {
            const controlsHidden = document.body.classList.contains('controls-hidden');
            if (controlsHidden) {
                showControls();
            } else {
                openBottomSheet('HALF');
            }
        });
    }

    updateBottomSheetTechSpecs();
}

/**
 * Initializes analytics dashboard actions.
 * Wires the "Visualize" button, GitHub URL input, and fetch button.
 */
export function initAnalyticsDashboardActions() {
    const vizBtn = document.getElementById('btn-switch-to-viz');
    const analyticsGithubUrl = document.getElementById('analytics-github-url');
    const analyticsFetchBtn = document.getElementById('analytics-fetch-btn');

    if (vizBtn) {
        addManagedEventListener(vizBtn, 'click', () => {
            switchToVisualization();
            const rource = getRource();
            if (rource && get('hasLoadedData')) {
                safeWasmCall('play', () => rource.play(), undefined);
                updatePlaybackUI();
            }
        });
    }

    if (analyticsGithubUrl && analyticsFetchBtn) {
        analyticsFetchBtn.disabled = true;

        addManagedEventListener(analyticsGithubUrl, 'input', () => {
            const hasValue = !!analyticsGithubUrl.value.trim();
            analyticsFetchBtn.disabled = !hasValue;
            analyticsFetchBtn.setAttribute('aria-label',
                hasValue ? 'Fetch repository data' : 'Fetch repository data (enter a GitHub URL first)');
        });

        addManagedEventListener(analyticsFetchBtn, 'click', async () => {
            const input = analyticsGithubUrl.value.trim();
            if (!input) return;

            let repo = input;
            const urlMatch = input.match(/github\.com\/([^\/]+\/[^\/]+)/);
            if (urlMatch) {
                repo = urlMatch[1];
            }

            analyticsFetchBtn.disabled = true;
            analyticsGithubUrl.disabled = true;

            try {
                const logData = await fetchGitHubWithProgress(repo, {
                    statusEl: document.getElementById('analytics-fetch-status-text'),
                    progressEl: document.getElementById('analytics-fetch-progress-bar'),
                });

                if (logData) {
                    loadLogData(logData, 'custom');
                    showToast(`Loaded ${repo}`, 'success');
                } else {
                    showToast('Failed to fetch repository', 'error');
                }
            } catch (error) {
                showToast('Error fetching repository: ' + error.message, 'error');
            } finally {
                analyticsFetchBtn.disabled = false;
                analyticsGithubUrl.disabled = false;
            }
        });

        addManagedEventListener(analyticsGithubUrl, 'keydown', (e) => {
            if (e.key === 'Enter' && !analyticsFetchBtn.disabled) {
                analyticsFetchBtn.click();
            }
        });
    }

    subscribe('hasLoadedData', (loaded) => {
        if (loaded) {
            const repoName = document.getElementById('analytics-repo-name');
            if (repoName && get('commitStats')) {
                const stats = get('commitStats');
                repoName.textContent = `${stats.commits || 0} commits across ${stats.files || 0} files`;
            }
        }
    });
}

/**
 * Updates bottom sheet technical specifications.
 */
function updateBottomSheetTechSpecs() {
    const rource = getRource();
    if (!rource) return;

    const bsRenderer = document.getElementById('bs-tech-renderer');
    if (bsRenderer) {
        const rendererType = rource.getRendererType();
        const displayNames = {
            'wgpu': 'WebGPU',
            'webgl2': 'WebGL2',
            'software': 'CPU'
        };
        bsRenderer.textContent = displayNames[rendererType] || rendererType;
    }
}

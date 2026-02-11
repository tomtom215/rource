// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Sidebar panel HTML templates.
 * Extracted from index.html for maintainability.
 * Each function returns HTML for one sidebar section.
 */

export function getShowcasePanelTemplate() {
    return `
            <span class="showcase-badge">Featured</span>
            <svg class="showcase-icon" viewBox="0 0 100 100" aria-hidden="true">
                <circle cx="50" cy="50" r="45" fill="#e94560"/>
                <circle cx="50" cy="30" r="8" fill="white"/>
                <circle cx="30" cy="60" r="6" fill="white"/>
                <circle cx="70" cy="55" r="6" fill="white"/>
                <circle cx="50" cy="75" r="5" fill="white"/>
                <line x1="50" y1="38" x2="50" y2="70" stroke="white" stroke-width="2"/>
                <line x1="50" y1="50" x2="32" y2="58" stroke="white" stroke-width="2"/>
                <line x1="50" y1="50" x2="68" y2="53" stroke="white" stroke-width="2"/>
            </svg>
            <h2>Visualize This Project</h2>
            <p>Watch the complete development history of Rource itself. Cached locally - no API limits.</p>
            <div class="showcase-buttons">
                <button type="button" id="btn-visualize-rource" class="showcase-btn" disabled>
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor">
                        <path d="M8 5v14l11-7z"/>
                    </svg>
                    Visualize Rource
                </button>
                <button type="button" id="btn-refresh-rource" class="showcase-btn-secondary" title="Fetch latest commits from GitHub">
                    <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                        <path d="M23 4v6h-6M1 20v-6h6"/>
                        <path d="M3.51 9a9 9 0 0114.85-3.36L23 10M1 14l4.64 4.36A9 9 0 0020.49 15"/>
                    </svg>
                    Fetch Latest
                </button>
            </div>
            <div id="refresh-status" class="refresh-status hidden"></div>
            <div class="showcase-stats">
                <div class="showcase-stat" title="Visualization steps (file changes grouped by time)">
                    <div class="showcase-stat-value" id="showcase-commits">--</div>
                    <div class="showcase-stat-label">Commits</div>
                </div>
                <div class="showcase-stat">
                    <div class="showcase-stat-value" id="showcase-files">--</div>
                    <div class="showcase-stat-label">Files</div>
                </div>
                <div class="showcase-stat">
                    <div class="showcase-stat-value" id="showcase-authors">--</div>
                    <div class="showcase-stat-label">Authors</div>
                </div>
            </div>`;
}

export function getGithubPanelTemplate() {
    return `
            <div class="panel-header">
                <h2>
                    <svg width="16" height="16" viewBox="0 0 16 16" fill="currentColor" aria-hidden="true">
                        <path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"/>
                    </svg>
                    Other Repositories
                </h2>
            </div>
            <div class="panel-body">
                <div class="github-input-group">
                    <input type="text" id="github-url" placeholder="https://github.com/owner/repo" aria-label="GitHub repository URL">
                    <button type="button" id="btn-fetch-github" class="btn btn-success btn-sm" disabled>
                        <svg width="14" height="14" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                            <path d="M19 9h-4V3H9v6H5l7 7 7-7zM5 18v2h14v-2H5z"/>
                        </svg>
                        Fetch
                    </button>
                </div>
                <div class="popular-repos">
                    <span class="popular-repos-label">Pre-cached repos (instant, no API calls):</span>
                    <div class="repo-chips">
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="facebook/react" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#61dafb"><circle cx="8" cy="8" r="3"/></svg>
                            React
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="vuejs/vue" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#42b883"><circle cx="8" cy="8" r="3"/></svg>
                            Vue
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="sveltejs/svelte" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#ff3e00"><circle cx="8" cy="8" r="3"/></svg>
                            Svelte
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="denoland/deno" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="currentColor"><circle cx="8" cy="8" r="3"/></svg>
                            Deno
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="rust-lang/rust" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#dea584"><circle cx="8" cy="8" r="3"/></svg>
                            Rust
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="microsoft/vscode" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#007acc"><circle cx="8" cy="8" r="3"/></svg>
                            VS Code
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="golang/go" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#00add8"><circle cx="8" cy="8" r="3"/></svg>
                            Go
                        </button>
                        <button type="button" class="repo-chip repo-chip-cached" data-repo="torvalds/linux" title="Pre-cached - instant loading">
                            <svg viewBox="0 0 16 16" fill="#f1c40f"><circle cx="8" cy="8" r="3"/></svg>
                            Linux
                        </button>
                    </div>
                </div>
                <div id="fetch-status" class="fetch-status">
                    <span id="fetch-status-text"></span>
                    <div class="fetch-progress">
                        <div id="fetch-progress-bar" class="fetch-progress-bar"></div>
                    </div>
                </div>
                <p class="help-text" style="margin-top: 0.75rem;">
                    Fetches up to 50 recent commits from public GitHub repositories.
                    <span class="rate-limit-note">GitHub API limit: 60 requests/hour without auth.</span>
                </p>
                <div id="rate-limit-status" class="rate-limit-status hidden"></div>
            </div>`;
}

export function getManualLoadPanelTemplate() {
    return `
            <div class="tab-nav" role="tablist">
                <button type="button" class="tab-btn active" data-tab="command" role="tab" aria-selected="true">Git Command</button>
                <button type="button" class="tab-btn" data-tab="upload" role="tab" aria-selected="false">Upload File</button>
                <button type="button" class="tab-btn" data-tab="paste" role="tab" aria-selected="false">Paste Log</button>
            </div>

            <div id="tab-command" class="tab-content active" role="tabpanel">
                <p class="help-text" style="margin-bottom: 0.75rem;">Generate a log file from your local repository:</p>
                <div class="command-box">
                    <code id="git-command">git log --reverse --pretty=format:"commit %H%nAuthor: %an%nDate: %at%n" --name-status &gt; rource.log</code>
                </div>
                <button type="button" id="btn-copy-command" class="btn btn-sm btn-secondary">
                    <svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/></svg>
                    Copy Command
                </button>
                <div class="help-text" style="margin-top: 0.75rem;">
                    <strong>How to use:</strong>
                    <ol style="margin: 0.5rem 0 0 1.2rem; padding: 0;">
                        <li>Open a terminal in your Git repository</li>
                        <li>Run the command above (creates <code>rource.log</code>)</li>
                        <li>Upload the generated file using the "Upload File" tab</li>
                    </ol>
                    <p style="margin-top: 0.5rem; color: var(--text-muted); font-size: 0.85em;">
                        <strong>Note:</strong> Works on Linux/macOS/Windows (Git Bash). Handles renames and all file statuses.
                    </p>
                </div>
            </div>

            <div id="tab-upload" class="tab-content" role="tabpanel" hidden>
                <div class="file-upload-area" id="file-drop-zone">
                    <input type="file" id="file-input" accept="text/*,.txt,.log,.csv,.rource">
                    <div class="file-upload-icon">
                        <svg width="48" height="48" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">
                            <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>
                            <polyline points="14 2 14 8 20 8"/>
                            <line x1="12" y1="18" x2="12" y2="12"/>
                            <line x1="9" y1="15" x2="12" y2="12"/>
                            <line x1="15" y1="15" x2="12" y2="12"/>
                        </svg>
                    </div>
                    <div class="file-upload-text">
                        <strong>Select a file</strong> or drag and drop
                    </div>
                    <div class="file-upload-privacy">
                        100% client-side - your data never leaves your browser
                    </div>
                </div>
                <div id="file-name" class="file-name hidden"></div>
                <button type="button" id="btn-load-file" class="btn btn-sm" disabled>Load Uploaded File</button>
                <div class="help-text" style="margin-top: 0.75rem;">
                    <strong>Supported formats (auto-detected):</strong><br>
                    <span style="color: var(--text-secondary);">&#8226; Native git log format</span> (from "Git Command" tab)<br>
                    <span style="color: var(--text-secondary);">&#8226; Custom pipe-delimited:</span> <code>timestamp|author|action|path</code><br>
                    <span style="color: var(--text-muted); font-size: 0.85em;">Invalid lines are automatically skipped.</span>
                </div>
            </div>

            <div id="tab-paste" class="tab-content" role="tabpanel" hidden>
                <textarea id="log-input" aria-label="Log data input - paste git log or custom format data" placeholder="Paste your log data here...&#10;Formats auto-detected: git log or timestamp|author|action|path"></textarea>
                <button type="button" id="btn-load" class="btn btn-sm" disabled>Load Log Data</button>
                <p class="help-text">
                    Supported formats (auto-detected):<br>
                    <code>git log --name-status</code> output, or <code>timestamp|author|action|path</code>
                </p>
                <p class="file-upload-privacy" style="margin-top: 0.5rem;">
                    100% client-side - your data never leaves your browser
                </p>
            </div>`;
}

export function getKeyboardShortcutsPanelTemplate() {
    return `
            <div class="shortcut-grid">
                <div class="shortcut-item"><span>Play/Pause</span><kbd>Space</kbd></div>
                <div class="shortcut-item"><span>Zoom In</span><kbd>+</kbd></div>
                <div class="shortcut-item"><span>Zoom Out</span><kbd>-</kbd></div>
                <div class="shortcut-item"><span>Reset View</span><kbd>R</kbd></div>
                <div class="shortcut-item"><span>Pan</span><kbd>Arrows</kbd></div>
                <div class="shortcut-item"><span>Labels</span><kbd>L</kbd></div>
                <div class="shortcut-item"><span>Step Fwd</span><kbd>&gt;</kbd></div>
                <div class="shortcut-item"><span>Step Back</span><kbd>&lt;</kbd></div>
                <div class="shortcut-item"><span>Speed Down</span><kbd>[</kbd></div>
                <div class="shortcut-item"><span>Speed Up</span><kbd>]</kbd></div>
                <div class="shortcut-item"><span>Perf Stats</span><kbd>P</kbd></div>
                <div class="shortcut-item"><span>Authors</span><kbd>A</kbd></div>
                <div class="shortcut-item"><span>Full Map</span><kbd>M</kbd></div>
                <div class="shortcut-item"><span>Record</span><kbd>V</kbd></div>
                <div class="shortcut-item"><span>Text Size +</span><kbd>Shift+&#8593;</kbd></div>
                <div class="shortcut-item"><span>Text Size -</span><kbd>Shift+&#8595;</kbd></div>
            </div>
            <p class="help-text" style="margin-top: 0.75rem;">
                <strong>Mouse:</strong> Drag to pan, scroll to zoom
            </p>`;
}

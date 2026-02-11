// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Bottom sheet content HTML template.
 * Extracted from index.html for maintainability.
 * Injected into #bottom-sheet-content by initComponents().
 */

export function getBottomSheetContentTemplate() {
    return `
            <!-- Quick Actions -->
            <div class="bottom-sheet-section">
                <div class="bottom-sheet-quick-actions">
                    <button type="button" id="bs-visualize-rource" class="bottom-sheet-action-btn primary" disabled>
                        <svg width="20" height="20" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                            <path d="M8 5v14l11-7z"/>
                        </svg>
                        <span>Visualize Rource</span>
                    </button>
                    <button type="button" id="bs-fetch-repo" class="bottom-sheet-action-btn">
                        <svg width="20" height="20" viewBox="0 0 16 16" fill="currentColor" aria-hidden="true">
                            <path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"/>
                        </svg>
                        <span>Load Repository</span>
                    </button>
                </div>
            </div>

            <!-- Legends Section (File Types & Authors) - populated via JS -->
            <div id="bs-legends-section" class="bottom-sheet-legends hidden">
                <div class="bottom-sheet-legend-section" id="bs-file-types">
                    <div class="bottom-sheet-legend-header">
                        <span class="bottom-sheet-legend-title">File Types</span>
                    </div>
                    <div class="bottom-sheet-legend-items" id="bs-file-types-items">
                        <!-- Populated dynamically -->
                    </div>
                </div>
                <div class="bottom-sheet-legend-section" id="bs-authors">
                    <div class="bottom-sheet-legend-header">
                        <span class="bottom-sheet-legend-title">Authors</span>
                    </div>
                    <div class="bottom-sheet-legend-items" id="bs-authors-items">
                        <!-- Populated dynamically -->
                    </div>
                </div>
            </div>

            <!-- Repository Insights Summary (populated via JS when data is loaded) -->
            <div id="bs-insights-section" class="bottom-sheet-section hidden">
                <div class="bottom-sheet-legend-header">
                    <span class="bottom-sheet-legend-title">Repository Insights</span>
                </div>
                <div id="bs-insights-summary" class="insights-summary">
                    <!-- Populated dynamically by insights.js -->
                </div>
                <button type="button" id="bs-insights-expand" class="bottom-sheet-action-btn" aria-label="View full insights">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                        <path d="M19 3H5c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h14c1.1 0 2-.9 2-2V5c0-1.1-.9-2-2-2zm-7 14H8v-2h4v2zm4-4H8v-2h8v2zm0-4H8V7h8v2z"/>
                    </svg>
                    <span>View Full Insights</span>
                </button>
            </div>

            <!-- GitHub URL Input -->
            <div class="bottom-sheet-section">
                <label class="bottom-sheet-label">GitHub Repository</label>
                <div class="bottom-sheet-input-group">
                    <input type="text" id="bs-github-url" class="bottom-sheet-input" placeholder="owner/repo or full URL">
                    <button type="button" id="bs-fetch-btn" class="bottom-sheet-fetch-btn" disabled aria-label="Fetch repository">
                        <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                            <path d="M19 9h-4V3H9v6H5l7 7 7-7zM5 18v2h14v-2H5z"/>
                        </svg>
                    </button>
                </div>
                <p class="bottom-sheet-hint">Popular: react, vue, svelte, deno</p>
            </div>

            <!-- Collapsible: Quick Guide -->
            <details class="bottom-sheet-details">
                <summary class="bottom-sheet-summary">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                        <path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm1 17h-2v-6h2v6zm0-8h-2V7h2v4z"/>
                    </svg>
                    Quick Guide
                </summary>
                <div class="bottom-sheet-details-content">
                    <p><strong>Rource</strong> visualizes git history as an animated tree.</p>
                    <ul>
                        <li>Files = colored dots</li>
                        <li>Developers = larger circles</li>
                        <li>Beams = commits connecting developers to files</li>
                    </ul>
                </div>
            </details>

            <!-- Collapsible: Controls -->
            <details class="bottom-sheet-details">
                <summary class="bottom-sheet-summary">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                        <path d="M9.5 6.5v3h-3v-3h3M11 5H5v6h6V5zm-1.5 9.5v3h-3v-3h3M11 13H5v6h6v-6zm6.5-6.5v3h-3v-3h3M19 5h-6v6h6V5zm-6 8h1.5v1.5H13V13zm1.5 1.5H16V16h-1.5v-1.5zM16 13h1.5v1.5H16V13zm-3 3h1.5v1.5H13V16zm1.5 1.5H16V19h-1.5v-1.5zM16 16h1.5v1.5H16V16zm1.5-1.5H19V16h-1.5v-1.5zm0 3H19V19h-1.5v-1.5zM19 13h-1.5v1.5H19V13z"/>
                    </svg>
                    Touch Controls
                </summary>
                <div class="bottom-sheet-details-content">
                    <ul>
                        <li><strong>Drag</strong> canvas to pan</li>
                        <li><strong>Pinch</strong> to zoom</li>
                        <li><strong>Tap</strong> play button to start/stop</li>
                        <li><strong>Swipe</strong> this sheet to dismiss</li>
                    </ul>
                </div>
            </details>

            <!-- Collapsible: Tech Specs -->
            <details class="bottom-sheet-details">
                <summary class="bottom-sheet-summary">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                        <path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm-1 17.93c-3.95-.49-7-3.85-7-7.93 0-.62.08-1.21.21-1.79L9 15v1c0 1.1.9 2 2 2v1.93zm6.9-2.54c-.26-.81-1-1.39-1.9-1.39h-1v-3c0-.55-.45-1-1-1H8v-2h2c.55 0 1-.45 1-1V7h2c1.1 0 2-.9 2-2v-.41c2.93 1.19 5 4.06 5 7.41 0 2.08-.8 3.97-2.1 5.39z"/>
                    </svg>
                    Technical Specs
                </summary>
                <div class="bottom-sheet-details-content">
                    <div class="bottom-sheet-tech-grid">
                        <div class="bottom-sheet-tech-item">
                            <span class="bottom-sheet-tech-value" id="bs-tech-wasm">~990KB</span>
                            <span class="bottom-sheet-tech-label">WASM</span>
                        </div>
                        <div class="bottom-sheet-tech-item">
                            <span class="bottom-sheet-tech-value" id="bs-tech-renderer">--</span>
                            <span class="bottom-sheet-tech-label">Renderer</span>
                        </div>
                        <div class="bottom-sheet-tech-item">
                            <span class="bottom-sheet-tech-value" id="bs-tech-tests">1836</span>
                            <span class="bottom-sheet-tech-label">Tests</span>
                        </div>
                    </div>
                    <div class="bottom-sheet-badges">
                        <span class="bottom-sheet-badge">Rust</span>
                        <span class="bottom-sheet-badge">WebAssembly</span>
                        <span class="bottom-sheet-badge">GPU</span>
                    </div>
                </div>
            </details>

            <!-- Footer Links -->
            <div class="bottom-sheet-footer">
                <a href="https://github.com/tomtom215/rource" target="_blank" rel="noopener" class="bottom-sheet-link">
                    <svg width="16" height="16" viewBox="0 0 16 16" fill="currentColor" aria-hidden="true">
                        <path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"/>
                    </svg>
                    View on GitHub
                </a>
                <a href="https://github.com/tomtom215/rource/issues" target="_blank" rel="noopener" class="bottom-sheet-link">
                    Report Issue
                </a>
            </div>`;
}

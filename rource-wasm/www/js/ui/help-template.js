// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Help overlay HTML template.
 * Extracted from index.html for maintainability.
 * Injected into #help-overlay by initComponents().
 */

export function getHelpTemplate() {
    return `
        <div class="help-content">
            <button type="button" id="help-close" class="help-close" aria-label="Close help">
                <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                    <path d="M19 6.41L17.59 5 12 10.59 6.41 5 5 6.41 10.59 12 5 17.59 6.41 19 12 13.41 17.59 19 19 17.59 13.41 12z"/>
                </svg>
            </button>
            <h2 id="help-title">What am I looking at?</h2>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><circle cx="12" cy="12" r="10"/></svg>
                    Visual Elements
                </h3>
                <div class="help-visual">
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32" aria-hidden="true">
                            <circle cx="16" cy="16" r="8" fill="#58a6ff"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Files</strong>
                            <span>Colored dots represent files. Color = file type.</span>
                        </div>
                    </div>
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32" aria-hidden="true">
                            <circle cx="16" cy="16" r="10" fill="#e94560" stroke="white" stroke-width="2"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Users</strong>
                            <span>Larger circles = developers. Each has a unique color.</span>
                        </div>
                    </div>
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32" aria-hidden="true">
                            <!-- Beam with glow effect -->
                            <defs>
                                <linearGradient id="beam-gradient" x1="0%" y1="0%" x2="100%" y2="0%">
                                    <stop offset="0%" style="stop-color:#3fb950;stop-opacity:0.3"/>
                                    <stop offset="50%" style="stop-color:#3fb950;stop-opacity:1"/>
                                    <stop offset="100%" style="stop-color:#3fb950;stop-opacity:0.3"/>
                                </linearGradient>
                                <filter id="beam-glow">
                                    <feGaussianBlur stdDeviation="2" result="blur"/>
                                    <feMerge>
                                        <feMergeNode in="blur"/>
                                        <feMergeNode in="SourceGraphic"/>
                                    </feMerge>
                                </filter>
                            </defs>
                            <!-- Glow layer -->
                            <line x1="4" y1="16" x2="28" y2="16" stroke="#3fb950" stroke-width="4" opacity="0.3" stroke-linecap="round"/>
                            <!-- Main beam line -->
                            <line x1="4" y1="16" x2="28" y2="16" stroke="url(#beam-gradient)" stroke-width="2" stroke-linecap="round" filter="url(#beam-glow)"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Beams</strong>
                            <span>Lines connecting users to files they modify.</span>
                        </div>
                    </div>
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32" aria-hidden="true">
                            <!-- Gray hollow circle with center dot = directory node -->
                            <circle cx="16" cy="16" r="10" fill="none" stroke="#8b949e" stroke-width="2" opacity="0.7"/>
                            <circle cx="16" cy="16" r="3" fill="#8b949e" opacity="0.5"/>
                            <!-- Soft glow effect -->
                            <circle cx="16" cy="16" r="12" fill="#8b949e" opacity="0.1"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Directories</strong>
                            <span>Gray circles with center dots = folders. Lines connect parent-child folders.</span>
                        </div>
                    </div>
                </div>
            </div>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm-2 15l-5-5 1.41-1.41L10 14.17l7.59-7.59L19 8l-9 9z"/></svg>
                    How It Works
                </h3>
                <p style="color: var(--text-secondary); font-size: 0.9rem; line-height: 1.6;">
                    Rource visualizes your Git history as an animated tree. Each commit creates "beams" connecting
                    developers to the files they modify. Files branch out from the root based on their directory
                    structure. The visualization uses a force-directed layout to naturally organize files and prevent overlap.
                </p>
                <p style="color: var(--text-muted); font-size: 0.8rem; line-height: 1.5; margin-top: 0.5rem;">
                    <strong>Note:</strong> The commit count groups file changes by timestamp and author. This may differ slightly from your git commit count if multiple commits share the same second.
                </p>
            </div>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M15.5 14h-.79l-.28-.27C15.41 12.59 16 11.11 16 9.5 16 5.91 13.09 3 9.5 3S3 5.91 3 9.5 5.91 16 9.5 16c1.61 0 3.09-.59 4.23-1.57l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z"/></svg>
                    Quick Tips
                </h3>
                <ul style="color: var(--text-secondary); font-size: 0.9rem; line-height: 1.8; padding-left: 1.25rem;">
                    <li><strong>Hover</strong> over files or users to see details</li>
                    <li><strong>Drag</strong> to pan around the visualization</li>
                    <li><strong>Scroll</strong> to zoom in/out</li>
                    <li><strong>Click canvas</strong> to focus, then use keyboard shortcuts</li>
                </ul>
            </div>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M20 5H4c-1.1 0-1.99.9-1.99 2L2 17c0 1.1.9 2 2 2h16c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm-9 3h2v2h-2V8zm0 3h2v2h-2v-2zM8 8h2v2H8V8zm0 3h2v2H8v-2zm-1 2H5v-2h2v2zm0-3H5V8h2v2zm9 7H8v-2h8v2zm0-4h-2v-2h2v2zm0-3h-2V8h2v2zm3 3h-2v-2h2v2zm0-3h-2V8h2v2z"/></svg>
                    Keyboard Shortcuts
                </h3>
                <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 0.5rem 1.5rem; color: var(--text-secondary); font-size: 0.85rem;">
                    <!-- Playback -->
                    <div style="font-weight: 600; color: var(--text-primary); grid-column: 1 / -1; margin-top: 0.5rem; border-bottom: 1px solid var(--border); padding-bottom: 0.25rem;">Playback</div>
                    <div><kbd class="kbd">Space</kbd> Play / Pause</div>
                    <div><kbd class="kbd">Home</kbd> Restart</div>
                    <div><kbd class="kbd">\u2190</kbd> <kbd class="kbd">,</kbd> Previous commit</div>
                    <div><kbd class="kbd">\u2192</kbd> <kbd class="kbd">.</kbd> Next commit</div>
                    <div><kbd class="kbd">[</kbd> Slower speed</div>
                    <div><kbd class="kbd">]</kbd> Faster speed</div>
                    <!-- Camera -->
                    <div style="font-weight: 600; color: var(--text-primary); grid-column: 1 / -1; margin-top: 0.5rem; border-bottom: 1px solid var(--border); padding-bottom: 0.25rem;">Camera</div>
                    <div><kbd class="kbd">W</kbd><kbd class="kbd">A</kbd><kbd class="kbd">S</kbd><kbd class="kbd">D</kbd> Pan<span style="color: var(--text-muted); font-size: 0.75rem;"> (canvas focused)</span></div>
                    <div><kbd class="kbd">R</kbd> Reset camera</div>
                    <div><kbd class="kbd">+</kbd> <kbd class="kbd">=</kbd> Zoom in</div>
                    <div><kbd class="kbd">-</kbd> Zoom out</div>
                    <!-- Display -->
                    <div style="font-weight: 600; color: var(--text-primary); grid-column: 1 / -1; margin-top: 0.5rem; border-bottom: 1px solid var(--border); padding-bottom: 0.25rem;">Display</div>
                    <div><kbd class="kbd">L</kbd> Toggle labels</div>
                    <div><kbd class="kbd">F</kbd> Fullscreen</div>
                    <div><kbd class="kbd">T</kbd> Toggle theme</div>
                    <div><kbd class="kbd">A</kbd> Toggle authors panel</div>
                    <div><kbd class="kbd">P</kbd> Performance overlay</div>
                    <div><kbd class="kbd">Shift</kbd>+<kbd class="kbd">\u2191\u2193</kbd> Font size</div>
                    <!-- Export -->
                    <div style="font-weight: 600; color: var(--text-primary); grid-column: 1 / -1; margin-top: 0.5rem; border-bottom: 1px solid var(--border); padding-bottom: 0.25rem;">Export</div>
                    <div><kbd class="kbd">S</kbd> Screenshot</div>
                    <div><kbd class="kbd">M</kbd> Export full map</div>
                    <div><kbd class="kbd">V</kbd> Video recording</div>
                    <div></div>
                    <!-- Help -->
                    <div style="font-weight: 600; color: var(--text-primary); grid-column: 1 / -1; margin-top: 0.5rem; border-bottom: 1px solid var(--border); padding-bottom: 0.25rem;">Help</div>
                    <div><kbd class="kbd">?</kbd> Show this help</div>
                    <div><kbd class="kbd">Esc</kbd> Close dialogs</div>
                </div>
            </div>

            <button type="button" id="help-got-it" class="btn" style="width: 100%; margin-top: 1rem;">Got it!</button>
        </div>`;
}

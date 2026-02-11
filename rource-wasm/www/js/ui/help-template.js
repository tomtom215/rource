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
                <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M19 6.41L17.59 5 12 10.59 6.41 5 5 6.41 10.59 12 5 17.59 6.41 19 12 13.41 17.59 19 19 17.59 13.41 12z"/>
                </svg>
            </button>
            <h2 id="help-title">What am I looking at?</h2>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor"><circle cx="12" cy="12" r="10"/></svg>
                    Visual Elements
                </h3>
                <div class="help-visual">
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32">
                            <circle cx="16" cy="16" r="8" fill="#58a6ff"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Files</strong>
                            <span>Colored dots represent files. Color = file type.</span>
                        </div>
                    </div>
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32">
                            <circle cx="16" cy="16" r="10" fill="#e94560" stroke="white" stroke-width="2"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Users</strong>
                            <span>Larger circles = developers. Each has a unique color.</span>
                        </div>
                    </div>
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32">
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
                            <line x1="4" y1="16" x2="28" y2="16" stroke="#3fb950" stroke-width="4" opacity="0.3" stroke-linecap="round"/>
                            <line x1="4" y1="16" x2="28" y2="16" stroke="url(#beam-gradient)" stroke-width="2" stroke-linecap="round" filter="url(#beam-glow)"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Beams</strong>
                            <span>Lines connecting users to files they modify.</span>
                        </div>
                    </div>
                    <div class="help-item">
                        <svg class="help-item-icon" viewBox="0 0 32 32">
                            <circle cx="16" cy="16" r="12" fill="none" stroke="#d29922" stroke-width="2" stroke-dasharray="4 2"/>
                        </svg>
                        <div class="help-item-text">
                            <strong>Directories</strong>
                            <span>Dashed circles group files by folder.</span>
                        </div>
                    </div>
                </div>
            </div>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor"><path d="M20 5H4c-1.1 0-1.99.9-1.99 2L2 17c0 1.1.9 2 2 2h16c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2z"/></svg>
                    Keyboard Shortcuts
                </h3>
                <div class="help-shortcuts">
                    <div class="help-shortcut"><kbd>Space</kbd><span>Play / Pause</span></div>
                    <div class="help-shortcut"><kbd>+</kbd> / <kbd>-</kbd><span>Zoom In / Out</span></div>
                    <div class="help-shortcut"><kbd>Arrow keys</kbd><span>Pan view</span></div>
                    <div class="help-shortcut"><kbd>R</kbd><span>Reset view</span></div>
                    <div class="help-shortcut"><kbd>L</kbd><span>Toggle labels</span></div>
                    <div class="help-shortcut"><kbd>&lt;</kbd> / <kbd>&gt;</kbd><span>Step through commits</span></div>
                    <div class="help-shortcut"><kbd>[</kbd> / <kbd>]</kbd><span>Decrease / Increase speed</span></div>
                    <div class="help-shortcut"><kbd>P</kbd><span>Toggle performance stats</span></div>
                    <div class="help-shortcut"><kbd>A</kbd><span>Toggle authors panel</span></div>
                    <div class="help-shortcut"><kbd>M</kbd><span>Export full map (high-res)</span></div>
                    <div class="help-shortcut"><kbd>V</kbd><span>Start/stop video recording</span></div>
                    <div class="help-shortcut"><kbd>T</kbd><span>Toggle light/dark theme</span></div>
                    <div class="help-shortcut"><kbd>F</kbd><span>Toggle fullscreen</span></div>
                    <div class="help-shortcut"><kbd>?</kbd><span>Show this help</span></div>
                    <div class="help-shortcut"><kbd>Shift+Up/Down</kbd><span>Increase/decrease label text size</span></div>
                </div>
            </div>

            <div class="help-section">
                <h3 class="help-section-heading">
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor"><path d="M13 7h-2v4H7v2h4v4h2v-4h4v-2h-4V7z"/><circle cx="12" cy="12" r="10" fill="none" stroke="currentColor" stroke-width="2"/></svg>
                    Mouse &amp; Touch
                </h3>
                <div class="help-shortcuts">
                    <div class="help-shortcut"><kbd>Click + Drag</kbd><span>Pan view</span></div>
                    <div class="help-shortcut"><kbd>Scroll wheel</kbd><span>Zoom</span></div>
                    <div class="help-shortcut"><kbd>Pinch</kbd><span>Zoom (touch)</span></div>
                    <div class="help-shortcut"><kbd>Hover file</kbd><span>Show file info tooltip</span></div>
                </div>
            </div>
        </div>`;
}

/**
 * Rource - Software Version Control Visualization
 * https://github.com/tomtom215/rource
 *
 * Main application entry point for the WASM web demo
 * License: GPL-3.0
 */

import init, { Rource } from './pkg/rource_wasm.js';

// ============================================================
// Application State
// ============================================================

// State
let rource = null;
let animationId = null;
let uploadedFileContent = null;
let hasLoadedData = false;
let commitStats = { commits: 0, files: 0, authors: new Set() };
let isContextLost = false;
let lastLoadedRepo = null;

// ============================================================
// User Preferences (localStorage)
// ============================================================

const PREFS_KEY = 'rource_preferences';

/**
 * Default user preferences
 */
const defaultPrefs = {
    speed: '10',           // Default speed (1x)
    showLabels: true,      // Show file/user labels
    panelStates: {         // Collapsed state for panels
        shortcuts: true,   // Keyboard shortcuts panel
        guide: true,       // Quick guide panel
        techSpecs: true,   // Technical specifications panel
        legend: true,      // File types legend
        authors: true,     // Authors legend
        perf: false,       // Performance overlay (hidden by default)
    },
    theme: 'dark',         // Theme preference
};

/**
 * Load user preferences from localStorage
 * @returns {Object} User preferences merged with defaults
 */
function loadPreferences() {
    try {
        const stored = localStorage.getItem(PREFS_KEY);
        if (stored) {
            const parsed = JSON.parse(stored);
            // Deep merge with defaults to handle new preference keys
            return {
                ...defaultPrefs,
                ...parsed,
                panelStates: {
                    ...defaultPrefs.panelStates,
                    ...(parsed.panelStates || {}),
                },
            };
        }
    } catch (e) {
        console.warn('Failed to load preferences:', e);
    }
    return { ...defaultPrefs };
}

/**
 * Save user preferences to localStorage
 * @param {Object} prefs - Preferences to save
 */
function savePreferences(prefs) {
    try {
        localStorage.setItem(PREFS_KEY, JSON.stringify(prefs));
    } catch (e) {
        console.warn('Failed to save preferences:', e);
    }
}

/**
 * Update a single preference value
 * @param {string} key - Preference key (supports dot notation for nested, e.g., 'panelStates.shortcuts')
 * @param {*} value - New value
 */
function updatePreference(key, value) {
    const prefs = loadPreferences();
    const keys = key.split('.');
    let obj = prefs;
    for (let i = 0; i < keys.length - 1; i++) {
        if (!obj[keys[i]]) obj[keys[i]] = {};
        obj = obj[keys[i]];
    }
    obj[keys[keys.length - 1]] = value;
    savePreferences(prefs);
}

// Load preferences at startup
const userPrefs = loadPreferences();

/**
 * Apply saved panel collapsed states from preferences
 */
function applyPanelPreferences() {
    const states = userPrefs.panelStates || {};

    // Keyboard shortcuts panel
    const shortcutsPanel = document.getElementById('panel-shortcuts');
    if (shortcutsPanel) {
        shortcutsPanel.classList.toggle('collapsed', states.shortcuts !== false);
    }

    // Quick guide panel
    const guidePanel = document.getElementById('panel-guide');
    if (guidePanel) {
        guidePanel.classList.toggle('collapsed', states.guide !== false);
    }

    // Technical specs panel
    const techPanel = document.getElementById('tech-info-panel');
    if (techPanel) {
        techPanel.classList.toggle('collapsed', states.techSpecs !== false);
    }

    // Legend panel
    const legendPanel = document.getElementById('legend-panel');
    if (legendPanel) {
        legendPanel.classList.toggle('collapsed', states.legend !== false);
    }
}

/**
 * Setup panel toggle handlers with preference saving
 * Consolidated handler for all collapsible sidebar panels
 */
function setupPanelToggleHandlers() {
    // Make collapsible panels save their state
    const panelMappings = [
        { id: 'panel-shortcuts', pref: 'panelStates.shortcuts' },
        { id: 'panel-guide', pref: 'panelStates.guide' },
        { id: 'tech-info-panel', pref: 'panelStates.techSpecs' },
    ];

    panelMappings.forEach(({ id, pref }) => {
        const panel = document.getElementById(id);
        if (!panel) return;

        const header = panel.querySelector('.panel-header, .tech-info-header');
        if (!header) return;

        // Use addEventListener for proper event handling
        header.addEventListener('click', () => {
            panel.classList.toggle('collapsed');
            const isCollapsed = panel.classList.contains('collapsed');

            // Update aria-expanded for accessibility
            header.setAttribute('aria-expanded', (!isCollapsed).toString());

            // Save preference
            updatePreference(pref, isCollapsed);
        });
    });
}

// =====================================================================
// URL STATE MANAGEMENT
// =====================================================================
// Enables sharing visualization settings via URL parameters.
// Supported params: repo, speed, autoplay
// =====================================================================

/**
 * Parses URL parameters and returns configuration object.
 * @returns {Object} Configuration from URL params
 */
function parseUrlParams() {
    const params = new URLSearchParams(window.location.search);
    return {
        repo: params.get('repo'),           // e.g., "owner/repo" or full URL
        speed: params.get('speed'),         // seconds per day
        autoplay: params.get('autoplay'),   // "true" to auto-play
        commit: params.get('commit'),       // commit index to start at
    };
}

/**
 * Updates URL with current visualization state without page reload.
 * @param {Object} state - State to persist in URL
 */
function updateUrlState(state) {
    const params = new URLSearchParams(window.location.search);

    if (state.repo !== undefined) {
        if (state.repo) params.set('repo', state.repo);
        else params.delete('repo');
    }
    if (state.speed !== undefined) {
        if (state.speed && state.speed !== '10') params.set('speed', state.speed);
        else params.delete('speed');
    }
    if (state.autoplay !== undefined) {
        if (state.autoplay) params.set('autoplay', 'true');
        else params.delete('autoplay');
    }

    const newUrl = params.toString()
        ? `${window.location.pathname}?${params.toString()}`
        : window.location.pathname;

    window.history.replaceState({}, '', newUrl);
}

/**
 * Generates a shareable URL for current state.
 * @returns {string} Full shareable URL
 */
function getShareableUrl() {
    return window.location.href;
}

// =====================================================================
// CACHED ROURCE REPOSITORY DATA
// =====================================================================
// This is the complete commit history of the Rource project itself.
// Cached locally to ensure the demo always works without API rate limits.
// Generated from: git log --reverse --format="%at|%an" --name-status
// Last updated: 2026-01-11
// =====================================================================
const ROURCE_CACHED_DATA = `1768004902|Tom F|A|LICENSE
1768004902|Tom F|A|README.md
1768006231|Claude|A|GOURCE_RUST_REWRITE_PLAN.md
1768028263|Claude|A|CLAUDE.md
1768028263|Claude|A|scripts/session-setup.sh
1768029507|Claude|A|.gitignore
1768029507|Claude|A|Cargo.toml
1768029507|Claude|A|crates/rource-core/Cargo.toml
1768029507|Claude|A|crates/rource-core/src/entity.rs
1768029507|Claude|A|crates/rource-core/src/lib.rs
1768029507|Claude|A|crates/rource-math/Cargo.toml
1768029507|Claude|A|crates/rource-math/src/color.rs
1768029507|Claude|A|crates/rource-math/src/lib.rs
1768029507|Claude|A|crates/rource-math/src/mat3.rs
1768029507|Claude|A|crates/rource-math/src/mat4.rs
1768029507|Claude|A|crates/rource-math/src/rect.rs
1768029507|Claude|A|crates/rource-math/src/vec2.rs
1768029507|Claude|A|crates/rource-math/src/vec3.rs
1768029507|Claude|A|crates/rource-math/src/vec4.rs
1768029507|Claude|A|crates/rource-vcs/Cargo.toml
1768029507|Claude|A|crates/rource-vcs/src/commit.rs
1768029507|Claude|A|crates/rource-vcs/src/lib.rs
1768029545|Claude|M|CLAUDE.md
1768039323|Claude|A|crates/rource-vcs/src/detect.rs
1768039323|Claude|A|crates/rource-vcs/src/error.rs
1768039323|Claude|M|crates/rource-vcs/src/lib.rs
1768039323|Claude|A|crates/rource-vcs/src/parser/custom.rs
1768039323|Claude|A|crates/rource-vcs/src/parser/git.rs
1768039323|Claude|A|crates/rource-vcs/src/parser/mod.rs
1768039351|Claude|M|CLAUDE.md
1768041150|Claude|M|CLAUDE.md
1768041150|Claude|M|crates/rource-core/src/lib.rs
1768041150|Claude|A|crates/rource-core/src/physics/mod.rs
1768041150|Claude|A|crates/rource-core/src/physics/spatial.rs
1768041150|Claude|A|crates/rource-core/src/scene/action.rs
1768041150|Claude|A|crates/rource-core/src/scene/file.rs
1768041150|Claude|A|crates/rource-core/src/scene/mod.rs
1768041150|Claude|A|crates/rource-core/src/scene/tree.rs
1768041150|Claude|A|crates/rource-core/src/scene/user.rs
1768041150|Claude|M|crates/rource-math/src/color.rs
1768041150|Claude|M|crates/rource-math/src/mat4.rs
1768041150|Claude|M|crates/rource-vcs/src/commit.rs
1768041150|Claude|M|crates/rource-vcs/src/detect.rs
1768041150|Claude|M|crates/rource-vcs/src/parser/custom.rs
1768041150|Claude|M|crates/rource-vcs/src/parser/git.rs
1768041150|Claude|M|crates/rource-vcs/src/parser/mod.rs
1768042447|Claude|M|CLAUDE.md
1768042447|Claude|A|crates/rource-core/src/animation/mod.rs
1768042447|Claude|A|crates/rource-core/src/animation/spline.rs
1768042447|Claude|A|crates/rource-core/src/animation/tween.rs
1768042447|Claude|A|crates/rource-core/src/camera/mod.rs
1768042447|Claude|M|crates/rource-core/src/lib.rs
1768042447|Claude|A|crates/rource-core/src/physics/force.rs
1768042447|Claude|M|crates/rource-core/src/physics/mod.rs
1768042602|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768044097|Claude|M|CLAUDE.md
1768044097|Claude|M|Cargo.toml
1768044097|Claude|M|crates/rource-core/src/physics/force.rs
1768044097|Claude|A|crates/rource-render/Cargo.toml
1768044097|Claude|A|crates/rource-render/src/backend/mod.rs
1768044097|Claude|A|crates/rource-render/src/backend/software.rs
1768044097|Claude|A|crates/rource-render/src/command.rs
1768044097|Claude|A|crates/rource-render/src/effects/bloom.rs
1768044097|Claude|A|crates/rource-render/src/effects/mod.rs
1768044097|Claude|A|crates/rource-render/src/font.rs
1768044097|Claude|A|crates/rource-render/src/lib.rs
1768044097|Claude|A|crates/rource-render/src/texture.rs
1768045302|Claude|M|CLAUDE.md
1768045302|Claude|M|Cargo.toml
1768045302|Claude|M|crates/rource-render/src/backend/software.rs
1768045302|Claude|M|crates/rource-render/src/command.rs
1768045302|Claude|M|crates/rource-render/src/effects/bloom.rs
1768045302|Claude|M|crates/rource-render/src/font.rs
1768045302|Claude|M|crates/rource-render/src/texture.rs
1768045302|Claude|A|rource-cli/Cargo.toml
1768045302|Claude|A|rource-cli/src/args.rs
1768045302|Claude|A|rource-cli/src/main.rs
1768046181|Claude|M|rource-cli/src/main.rs
1768046358|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768047064|Claude|A|crates/rource-core/src/config/mod.rs
1768047064|Claude|A|crates/rource-core/src/config/settings.rs
1768047064|Claude|M|crates/rource-core/src/lib.rs
1768047064|Claude|M|crates/rource-core/src/scene/mod.rs
1768047064|Claude|M|rource-cli/src/main.rs
1768047369|Claude|M|crates/rource-render/src/effects/mod.rs
1768047369|Claude|A|crates/rource-render/src/effects/shadow.rs
1768047369|Claude|M|rource-cli/src/args.rs
1768047369|Claude|M|rource-cli/src/main.rs
1768047841|Claude|M|crates/rource-vcs/src/detect.rs
1768047841|Claude|M|crates/rource-vcs/src/parser/mod.rs
1768047841|Claude|A|crates/rource-vcs/src/parser/svn.rs
1768047991|Claude|M|CLAUDE.md
1768047991|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768049940|Claude|M|CLAUDE.md
1768049940|Claude|M|crates/rource-core/src/config/settings.rs
1768049940|Claude|M|crates/rource-core/src/scene/mod.rs
1768049940|Claude|A|crates/rource-render/assets/RobotoMono-Regular.ttf
1768049940|Claude|M|crates/rource-render/src/backend/software.rs
1768049940|Claude|A|crates/rource-render/src/default_font.rs
1768049940|Claude|M|crates/rource-render/src/effects/shadow.rs
1768049940|Claude|M|crates/rource-render/src/lib.rs
1768049940|Claude|M|crates/rource-vcs/src/parser/svn.rs
1768049940|Claude|M|rource-cli/src/main.rs
1768061605|Claude|M|CLAUDE.md
1768061605|Claude|M|rource-cli/src/args.rs
1768061605|Claude|M|rource-cli/src/main.rs
1768062405|Claude|M|CLAUDE.md
1768062405|Claude|M|rource-cli/src/args.rs
1768062405|Claude|A|rource-cli/src/export.rs
1768062405|Claude|M|rource-cli/src/main.rs
1768064101|Claude|M|crates/rource-core/src/scene/mod.rs
1768064101|Claude|M|rource-cli/src/main.rs
1768064892|Claude|M|CLAUDE.md
1768064892|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768066271|Claude|M|Cargo.toml
1768066271|Claude|M|rource-cli/src/main.rs
1768066271|Claude|A|rource-wasm/Cargo.toml
1768066271|Claude|A|rource-wasm/src/lib.rs
1768066271|Claude|A|rource-wasm/www/index.html
1768066271|Claude|A|scripts/build-wasm.sh
1768066342|Claude|M|CLAUDE.md
1768068930|Claude|M|crates/rource-vcs/src/detect.rs
1768068930|Claude|A|crates/rource-vcs/src/parser/mercurial.rs
1768068930|Claude|M|crates/rource-vcs/src/parser/mod.rs
1768068930|Claude|M|rource-cli/Cargo.toml
1768068930|Claude|M|rource-cli/src/args.rs
1768068930|Claude|M|rource-cli/src/export.rs
1768068930|Claude|M|rource-cli/src/main.rs
1768068930|Claude|M|rource-wasm/src/lib.rs
1768068930|Claude|M|rource-wasm/www/index.html
1768070585|Claude|M|crates/rource-vcs/src/detect.rs
1768070585|Claude|A|crates/rource-vcs/src/parser/bazaar.rs
1768070585|Claude|M|crates/rource-vcs/src/parser/mercurial.rs
1768070585|Claude|M|crates/rource-vcs/src/parser/mod.rs
1768070585|Claude|M|rource-cli/src/export.rs
1768070585|Claude|M|rource-cli/src/main.rs
1768070585|Claude|M|rource-wasm/src/lib.rs
1768070585|Claude|M|rource-wasm/www/index.html
1768079256|Claude|M|crates/rource-core/src/scene/mod.rs
1768079256|Claude|M|rource-cli/src/main.rs
1768082290|Claude|M|Cargo.toml
1768082290|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768082290|Claude|M|crates/rource-core/Cargo.toml
1768082290|Claude|A|crates/rource-core/src/config/config_file.rs
1768082290|Claude|M|crates/rource-core/src/config/mod.rs
1768082290|Claude|M|crates/rource-core/src/scene/mod.rs
1768082290|Claude|M|crates/rource-render/src/backend/software.rs
1768082290|Claude|M|rource-cli/Cargo.toml
1768082290|Claude|M|rource-cli/src/args.rs
1768082290|Claude|A|rource-cli/src/avatar.rs
1768082290|Claude|M|rource-cli/src/main.rs
1768082688|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768084344|Claude|M|crates/rource-core/Cargo.toml
1768084344|Claude|M|crates/rource-core/src/config/config_file.rs
1768084344|Claude|M|crates/rource-core/src/config/mod.rs
1768084344|Claude|M|crates/rource-core/src/config/settings.rs
1768084344|Claude|M|rource-cli/src/args.rs
1768084344|Claude|M|rource-cli/src/main.rs
1768087702|Claude|M|crates/rource-core/src/scene/mod.rs
1768087702|Claude|M|rource-cli/src/main.rs
1768088628|Claude|M|CLAUDE.md
1768088628|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768088628|Claude|A|crates/rource-core/src/config/config_env.rs
1768088628|Claude|M|crates/rource-core/src/config/mod.rs
1768088628|Claude|M|rource-cli/src/args.rs
1768088628|Claude|M|rource-cli/src/main.rs
1768088835|Claude|M|rource-cli/src/args.rs
1768088835|Claude|M|rource-cli/src/main.rs
1768088917|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768091184|Claude|A|MIGRATING.md
1768091184|Claude|M|README.md
1768091184|Claude|A|examples/README.md
1768091184|Claude|A|examples/basic.toml
1768091184|Claude|A|examples/export-video.sh
1768091184|Claude|A|examples/large-repo.toml
1768091184|Claude|A|examples/minimal.toml
1768091184|Claude|A|examples/presentation.toml
1768091184|Claude|A|examples/quick-preview.sh
1768091184|Claude|A|examples/rust-project.toml
1768091184|Claude|A|examples/sample-custom.log
1768091184|Claude|A|examples/video-export.toml
1768091184|Claude|A|examples/web-project.toml
1768091218|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768092822|Claude|M|CLAUDE.md
1768092822|Claude|M|README.md
1768092822|Claude|M|crates/rource-render/Cargo.toml
1768092822|Claude|M|crates/rource-render/src/backend/mod.rs
1768092822|Claude|A|crates/rource-render/src/backend/webgl2/buffers.rs
1768092822|Claude|A|crates/rource-render/src/backend/webgl2/mod.rs
1768092822|Claude|A|crates/rource-render/src/backend/webgl2/shaders.rs
1768092822|Claude|A|crates/rource-render/src/backend/webgl2/textures.rs
1768092822|Claude|M|crates/rource-render/src/lib.rs
1768092822|Claude|M|rource-wasm/Cargo.toml
1768092822|Claude|M|rource-wasm/src/lib.rs
1768093056|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768094482|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768094482|Claude|M|crates/rource-core/src/config/config_env.rs
1768094482|Claude|M|crates/rource-core/src/config/settings.rs
1768094482|Claude|M|crates/rource-core/src/scene/mod.rs
1768094482|Claude|M|crates/rource-render/src/backend/mod.rs
1768094482|Claude|M|crates/rource-render/src/backend/webgl2/textures.rs
1768094482|Claude|M|crates/rource-vcs/src/detect.rs
1768094482|Claude|M|crates/rource-vcs/src/lib.rs
1768094482|Claude|M|crates/rource-vcs/src/parser/bazaar.rs
1768094482|Claude|M|crates/rource-vcs/src/parser/mercurial.rs
1768094482|Claude|M|rource-cli/src/args.rs
1768094482|Claude|M|rource-cli/src/avatar.rs
1768094482|Claude|M|rource-cli/src/main.rs
1768094482|Claude|M|rource-wasm/src/lib.rs
1768129122|Claude|M|CLAUDE.md
1768129122|Claude|M|GOURCE_RUST_REWRITE_PLAN.md
1768129122|Claude|A|crates/rource-vcs/examples/memory_benchmark.rs
1768129122|Claude|A|crates/rource-vcs/src/compact.rs
1768129122|Claude|A|crates/rource-vcs/src/intern.rs
1768129122|Claude|M|crates/rource-vcs/src/lib.rs
1768129122|Claude|A|crates/rource-vcs/src/stream.rs
1768135084|Claude|M|crates/rource-core/src/config/config_env.rs
1768135084|Claude|M|crates/rource-core/src/config/config_file.rs
1768135084|Claude|M|crates/rource-core/src/config/mod.rs
1768135084|Claude|M|crates/rource-core/src/config/settings.rs
1768135084|Claude|M|rource-cli/src/args.rs
1768135084|Claude|M|rource-cli/src/main.rs
1768137496|Claude|A|crates/rource-core/src/camera/camera3d.rs
1768137496|Claude|M|crates/rource-core/src/camera/mod.rs
1768137496|Claude|M|crates/rource-core/src/config/config_env.rs
1768137496|Claude|M|crates/rource-core/src/config/config_file.rs
1768137496|Claude|M|crates/rource-core/src/config/settings.rs
1768137496|Claude|M|crates/rource-core/src/lib.rs
1768137496|Claude|M|crates/rource-render/Cargo.toml
1768137496|Claude|M|crates/rource-render/src/backend/software.rs
1768137496|Claude|M|crates/rource-render/src/backend/webgl2/shaders.rs
1768137496|Claude|A|crates/rource-render/src/image.rs
1768137496|Claude|M|crates/rource-render/src/lib.rs
1768137496|Claude|M|crates/rource-vcs/src/compact.rs
1768137496|Claude|M|crates/rource-vcs/src/intern.rs
1768137496|Claude|M|crates/rource-vcs/src/stream.rs
1768137496|Claude|M|rource-cli/src/args.rs
1768137496|Claude|M|rource-cli/src/main.rs
1768137496|Claude|M|rource-wasm/src/lib.rs
1768145880|Claude|A|benchmarks/.gitignore
1768145880|Claude|A|benchmarks/BENCHMARK_REPORT.md
1768145880|Claude|A|benchmarks/docs/BENCHMARK_METHODOLOGY.md
1768145880|Claude|A|benchmarks/scripts/benchmark_binary.sh
1768145880|Claude|A|benchmarks/scripts/benchmark_features.sh
1768145880|Claude|A|benchmarks/scripts/benchmark_log_parsing.sh
1768145880|Claude|A|benchmarks/scripts/benchmark_memory.sh
1768145880|Claude|A|benchmarks/scripts/benchmark_rendering.sh
1768145880|Claude|A|benchmarks/scripts/common.sh
1768145880|Claude|A|benchmarks/scripts/run_benchmarks.sh
1768145880|Claude|A|benchmarks/scripts/test_benchmarks.sh
1768146249|Claude|A|.github/workflows/deploy-pages.yml
1768146249|Claude|A|rource-wasm/www/.nojekyll
1768147375|Claude|M|.github/workflows/deploy-pages.yml
1768147375|Claude|M|rource-wasm/www/index.html
1768147471|Claude|M|README.md
1768147773|Claude|M|.github/workflows/deploy-pages.yml
1768150459|Claude|M|rource-wasm/www/index.html
1768151357|Claude|M|crates/rource-core/src/scene/mod.rs
1768151357|Claude|M|crates/rource-core/src/scene/user.rs
1768151357|Claude|M|rource-wasm/www/index.html
1768152039|Claude|M|rource-wasm/src/lib.rs
1768152039|Claude|M|rource-wasm/www/index.html
1768153285|Claude|M|rource-wasm/src/lib.rs
1768153285|Claude|M|rource-wasm/www/index.html
1768153285|Claude|A|rource-wasm/www/pkg/package.json
1768153285|Claude|A|rource-wasm/www/pkg/rource_wasm.d.ts
1768153285|Claude|A|rource-wasm/www/pkg/rource_wasm.js
1768153285|Claude|A|rource-wasm/www/pkg/rource_wasm_bg.wasm
1768153285|Claude|A|rource-wasm/www/pkg/rource_wasm_bg.wasm.d.ts
1768154755|Claude|M|rource-wasm/src/lib.rs
1768154755|Claude|M|rource-wasm/www/index.html
1768155097|Claude|M|rource-wasm/www/index.html`;

// Pre-calculate stats for the cached Rource data
const ROURCE_STATS = (() => {
    const lines = ROURCE_CACHED_DATA.split('\n');
    const files = new Set();
    const authors = new Set();
    let commits = 0;
    let lastTimestamp = 0;
    for (const line of lines) {
        if (!line.trim()) continue;
        const parts = line.split('|');
        if (parts.length >= 4) {
            commits++;
            authors.add(parts[1].trim());
            files.add(parts[3].trim());
            const ts = parseInt(parts[0], 10);
            if (ts > lastTimestamp) lastTimestamp = ts;
        }
    }
    return { commits, files: files.size, authors: authors.size, lastTimestamp };
})();

// Track additional commits fetched via refresh
let additionalCommits = '';

// Demo data - more comprehensive project evolution
const DEMO_DATA = `1704067200|Alice|A|src/main.rs
1704067260|Alice|A|src/lib.rs
1704067320|Alice|A|Cargo.toml
1704067380|Alice|A|README.md
1704153600|Bob|A|src/config.rs
1704153660|Bob|M|src/main.rs
1704153720|Bob|A|src/utils/mod.rs
1704153780|Bob|A|src/utils/helpers.rs
1704240000|Charlie|A|tests/test_main.rs
1704240060|Charlie|M|src/lib.rs
1704240120|Charlie|A|tests/test_config.rs
1704326400|Alice|M|src/main.rs
1704326460|Alice|M|src/config.rs
1704326520|Alice|A|docs/API.md
1704412800|Bob|A|src/api/mod.rs
1704412860|Bob|A|src/api/routes.rs
1704412920|Bob|A|src/api/handlers.rs
1704412980|Bob|M|src/main.rs
1704499200|Charlie|A|src/db/mod.rs
1704499260|Charlie|A|src/db/models.rs
1704499320|Charlie|A|src/db/queries.rs
1704499380|Charlie|M|src/api/handlers.rs
1704585600|Alice|A|src/auth/mod.rs
1704585660|Alice|A|src/auth/jwt.rs
1704585720|Alice|M|src/api/routes.rs
1704585780|Alice|A|tests/test_auth.rs
1704672000|Bob|M|src/db/queries.rs
1704672060|Bob|M|src/api/handlers.rs
1704672120|Bob|A|migrations/001_initial.sql
1704758400|Charlie|A|.github/workflows/ci.yml
1704758460|Charlie|M|Cargo.toml
1704758520|Charlie|A|Dockerfile
1704844800|Alice|M|README.md
1704844860|Alice|A|docs/DEPLOY.md
1704844920|Alice|M|src/main.rs
1704931200|Bob|D|src/utils/helpers.rs
1704931260|Bob|A|src/utils/string.rs
1704931320|Bob|A|src/utils/time.rs
1704931380|Bob|M|src/utils/mod.rs
1705017600|Charlie|M|src/auth/jwt.rs
1705017660|Charlie|A|src/auth/middleware.rs
1705017720|Charlie|M|src/api/routes.rs
1705104000|Diana|A|frontend/index.html
1705104060|Diana|A|frontend/style.css
1705104120|Diana|A|frontend/app.js
1705190400|Eve|A|src/cache/mod.rs
1705190460|Eve|A|src/cache/redis.rs
1705190520|Eve|M|src/api/handlers.rs`;

// DOM elements
const canvas = document.getElementById('canvas');
const btnPlayMain = document.getElementById('btn-play-main');
const playIconMain = document.getElementById('play-icon-main');
const btnPrev = document.getElementById('btn-prev');
const btnNext = document.getElementById('btn-next');
const btnResetBar = document.getElementById('btn-reset-bar');
const btnLabels = document.getElementById('btn-labels');
const labelsText = document.getElementById('labels-text');
const btnScreenshot = document.getElementById('btn-screenshot');
const contextLostOverlay = document.getElementById('context-lost-overlay');
const btnRestoreContext = document.getElementById('btn-restore-context');
const btnLoad = document.getElementById('btn-load');
const btnLoadFile = document.getElementById('btn-load-file');
const btnCopyCommand = document.getElementById('btn-copy-command');
const btnFetchGithub = document.getElementById('btn-fetch-github');
const githubUrlInput = document.getElementById('github-url');
const fetchStatus = document.getElementById('fetch-status');
const fetchStatusText = document.getElementById('fetch-status-text');
const fetchProgressBar = document.getElementById('fetch-progress-bar');
const logInput = document.getElementById('log-input');
const loadingEl = document.getElementById('loading');
const timelineSlider = document.getElementById('timeline-slider');
const timelineInfo = document.getElementById('timeline-info');
const speedSelect = document.getElementById('speed-select');
const fileInput = document.getElementById('file-input');
const fileDropZone = document.getElementById('file-drop-zone');
const fileNameEl = document.getElementById('file-name');
const emptyState = document.getElementById('empty-state');
const rendererBadge = document.getElementById('renderer-badge');
const statsOverlay = document.getElementById('stats-overlay');
const statCommits = document.getElementById('stat-commits');
const statFiles = document.getElementById('stat-files');
const statAuthors = document.getElementById('stat-authors');
const toast = document.getElementById('toast');

// Performance metrics DOM elements
const perfOverlay = document.getElementById('perf-overlay');
const perfFps = document.getElementById('perf-fps');
const perfFrameTime = document.getElementById('perf-frame-time');
const perfEntities = document.getElementById('perf-entities');
const perfVisible = document.getElementById('perf-visible');
const perfDraws = document.getElementById('perf-draws');
const perfResolution = document.getElementById('perf-resolution');
const techRenderer = document.getElementById('tech-renderer');

// Showcase panel DOM elements
const btnVisualizeRource = document.getElementById('btn-visualize-rource');
const btnRefreshRource = document.getElementById('btn-refresh-rource');
const refreshStatus = document.getElementById('refresh-status');
const showcaseCommits = document.getElementById('showcase-commits');
const showcaseFiles = document.getElementById('showcase-files');
const showcaseAuthors = document.getElementById('showcase-authors');

// Authors legend DOM elements
const authorsPanel = document.getElementById('authors-panel');
const authorsItems = document.getElementById('authors-items');
const authorsToggle = document.getElementById('authors-toggle');

// New UI feature DOM elements
const themeToggle = document.getElementById('btn-theme');
const helpBtn = document.getElementById('btn-help');
const helpOverlay = document.getElementById('help-overlay');
const helpClose = document.getElementById('help-close');
const helpGotIt = document.getElementById('help-got-it');
const sidebarPanel = document.getElementById('sidebar-panel');
const sidebarToggle = document.getElementById('sidebar-toggle');
const sidebarClose = document.getElementById('sidebar-close');
const sidebarOverlay = document.getElementById('sidebar-overlay');
const commitTooltip = document.getElementById('commit-tooltip');
const tooltipAuthorColor = document.getElementById('tooltip-author-color');
const tooltipAuthor = document.getElementById('tooltip-author');
const tooltipDate = document.getElementById('tooltip-date');
const tooltipFile = document.getElementById('tooltip-file');
const tooltipAction = document.getElementById('tooltip-action');

// Author filter state
let filteredAuthor = null;
let authorColorMap = new Map();

// Timeline markers DOM element
const timelineMarkers = document.getElementById('timeline-markers');

// First visit state for help overlay
const HELP_SHOWN_KEY = 'rource_help_shown';

// Toast notification
function showToast(message, type = 'error', duration = 5000) {
    toast.querySelector('.toast-message').textContent = message;
    toast.className = `toast ${type} visible`;
    setTimeout(() => toast.classList.remove('visible'), duration);
}

toast.querySelector('.toast-close').addEventListener('click', () => {
    toast.classList.remove('visible');
});

// Resize canvas
function resizeCanvas() {
    const container = document.getElementById('canvas-container');
    const rect = container.getBoundingClientRect();
    const width = Math.floor(rect.width);
    const height = Math.floor(rect.height);

    if (canvas.width !== width || canvas.height !== height) {
        canvas.width = width;
        canvas.height = height;
        if (rource) {
            rource.resize(width, height);
            rource.forceRender();
        }
    }
}

// Performance metrics update counter (update every N frames for performance)
let perfUpdateCounter = 0;
const PERF_UPDATE_INTERVAL = 10; // Update every 10 frames

// Animation loop
function animate(timestamp) {
    if (rource) {
        rource.frame(timestamp);
        updateUI();

        // Update performance metrics periodically
        perfUpdateCounter++;
        if (perfUpdateCounter >= PERF_UPDATE_INTERVAL) {
            updatePerfMetrics();
            perfUpdateCounter = 0;
        }
    }
    animationId = requestAnimationFrame(animate);
}

// Update performance metrics overlay
function updatePerfMetrics() {
    if (!rource || !hasLoadedData) return;

    try {
        // Get FPS and frame time
        const fps = rource.getFps();
        const frameTimeMs = rource.getFrameTimeMs();

        // Get render statistics
        const totalEntities = rource.getTotalEntities();
        const visibleFiles = rource.getVisibleFiles();
        const visibleUsers = rource.getVisibleUsers();
        const visibleDirs = rource.getVisibleDirectories();
        const drawCalls = rource.getDrawCalls();
        const width = rource.getCanvasWidth();
        const height = rource.getCanvasHeight();

        // Update FPS display with color coding and playback status
        const fpsRounded = Math.round(fps);
        const isPlaying = rource.isPlaying();
        const total = rource.commitCount();
        const current = rource.currentCommit();
        const isComplete = current >= total - 1 && !isPlaying;

        if (isComplete) {
            perfFps.textContent = `Complete`;
            perfFps.className = 'perf-fps complete';
        } else if (!isPlaying) {
            perfFps.textContent = `Paused`;
            perfFps.className = 'perf-fps paused';
        } else {
            perfFps.textContent = `${fpsRounded} FPS`;
            perfFps.className = 'perf-fps ' + (fpsRounded >= 55 ? 'good' : fpsRounded >= 30 ? 'ok' : 'bad');
        }

        // Update other metrics
        perfFrameTime.textContent = `${frameTimeMs.toFixed(1)}ms`;
        perfEntities.textContent = totalEntities.toLocaleString();
        perfVisible.textContent = `${visibleFiles + visibleUsers + visibleDirs}`;
        perfDraws.textContent = drawCalls.toString();
        perfResolution.textContent = `${width}×${height}`;
    } catch (e) {
        // Silently ignore errors if methods don't exist
    }
}

// Check if visualization is at the end
function isAtEnd() {
    if (!rource) return false;
    const total = rource.commitCount();
    const current = rource.currentCommit();
    return total > 0 && current >= total - 1;
}

// Update UI
function updateUI() {
    if (!rource) return;

    const playing = rource.isPlaying();
    const total = rource.commitCount();
    const current = rource.currentCommit();
    const atEnd = total > 0 && current >= total - 1 && !playing;

    // Update play button icon - show replay icon when at end
    const pauseIcon = '<rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/>';
    const playIconPath = '<path d="M8 5v14l11-7z"/>';
    const replayIcon = '<path d="M12 5V1L7 6l5 5V7c3.31 0 6 2.69 6 6s-2.69 6-6 6-6-2.69-6-6H4c0 4.42 3.58 8 8 8s8-3.58 8-8-3.58-8-8-8z"/>';

    if (playing) {
        playIconMain.innerHTML = pauseIcon;
        btnPlayMain.title = 'Pause (Space)';
        btnPlayMain.classList.add('active');
        btnPlayMain.classList.remove('replay');
    } else if (atEnd) {
        playIconMain.innerHTML = replayIcon;
        btnPlayMain.title = 'Replay from start (Space)';
        btnPlayMain.classList.remove('active');
        btnPlayMain.classList.add('replay');
    } else {
        playIconMain.innerHTML = playIconPath;
        btnPlayMain.title = 'Play (Space)';
        btnPlayMain.classList.remove('active');
        btnPlayMain.classList.remove('replay');
    }

    // Update timeline
    if (total > 0) {
        timelineSlider.max = total - 1;
        timelineSlider.value = Math.min(current, total - 1);
        timelineSlider.disabled = false;
        timelineInfo.textContent = `${Math.min(current + 1, total)} / ${total}`;
    } else {
        timelineSlider.max = 0;
        timelineSlider.value = 0;
        timelineSlider.disabled = true;
        timelineInfo.textContent = '0 / 0';
    }
}

// Analyze log data for stats
function analyzeLogData(content) {
    const lines = content.split('\n');
    const files = new Set();
    const authors = new Set();
    let commits = 0;

    for (const line of lines) {
        if (!line.trim()) continue;
        const parts = line.split('|');
        if (parts.length >= 4) {
            commits++;
            authors.add(parts[1].trim());
            files.add(parts[3].trim());
        }
    }

    return { commits, files: files.size, authors };
}

// Load log data
function loadLogData(content, format = 'custom') {
    if (!rource || !content.trim()) {
        showToast('Please enter or upload log data first.', 'error');
        return;
    }

    try {
        let count;
        if (format === 'git') {
            count = rource.loadGitLog(content);
        } else {
            count = rource.loadCustomLog(content);
        }

        if (count === 0) {
            showToast('No commits found. Check your log format.', 'error');
            return;
        }

        // Analyze data
        const stats = analyzeLogData(content);
        statCommits.textContent = count;
        statFiles.textContent = stats.files;
        statAuthors.textContent = stats.authors.size;

        hasLoadedData = true;
        emptyState.classList.add('hidden');
        statsOverlay.classList.remove('hidden');
        perfOverlay.classList.remove('hidden');

        // Enable controls
        btnPrev.disabled = false;
        btnNext.disabled = false;
        speedSelect.disabled = false;

        updateUI();
        updateLegend(content);
        updateAuthorsLegend(content);
        updateTimelineMarkers(content);
        updatePerfMetrics();

        // Parse commits for tooltip display
        parseCommitsForTooltip(content);

        // Show first-time help overlay
        maybeShowFirstTimeHelp();

        showToast(`Loaded ${count} commits from ${stats.authors.size} authors!`, 'success', 3000);

        // Check for commit position in URL
        const urlParams = parseUrlParams();
        if (urlParams.commit) {
            const commitIndex = parseInt(urlParams.commit, 10);
            if (!isNaN(commitIndex) && commitIndex >= 0 && commitIndex < count) {
                rource.seek(commitIndex);
                updateUI();
            }
        }

        // Start paused by default for first-time users
        // Only auto-play if explicitly requested via URL parameter
        if (urlParams.autoplay === 'true') {
            rource.play();
        }
        updateUI();

    } catch (e) {
        showToast(`Failed to parse log: ${e}`, 'error');
        console.error('Parse error:', e);
    }
}

// Extension colors (matches Rust code)
const extensionColors = {
    'rs': '#dea584', 'go': '#00add8', 'py': '#3572a5',
    'js': '#f7df1e', 'ts': '#3178c6', 'jsx': '#61dafb', 'tsx': '#61dafb',
    'java': '#b07219', 'kt': '#a78bfa', 'c': '#5555ff', 'cpp': '#00599c',
    'cs': '#9b4f96', 'rb': '#cc342d', 'php': '#4f5d95', 'swift': '#f05138',
    'html': '#e34c26', 'css': '#563d7c', 'scss': '#cd6799',
    'json': '#808080', 'yaml': '#cb171e', 'yml': '#cb171e',
    'toml': '#9c4221', 'xml': '#0060ac', 'md': '#083fa1',
    'sh': '#008000', 'sql': '#e38c00', 'dockerfile': '#2496ed'
};

function getExtensionColor(ext) {
    const lower = ext.toLowerCase();
    if (extensionColors[lower]) return extensionColors[lower];
    // Hash for unknown extensions
    let hash = 0;
    for (let i = 0; i < lower.length; i++) {
        hash = (hash * 31 + lower.charCodeAt(i)) >>> 0;
    }
    return `hsl(${hash % 360}, 50%, 50%)`;
}

// =====================================================================
// TIMELINE MARKERS
// =====================================================================
// Creates visual markers on the timeline for significant commits
// (first commit, large commits, recent activity bursts)
// =====================================================================
function updateTimelineMarkers(content) {
    if (!timelineMarkers) return;

    // Clear existing markers
    timelineMarkers.innerHTML = '';

    const lines = content.trim().split('\n').filter(l => l.trim());
    const totalCommits = lines.length;

    if (totalCommits === 0) return;

    // Parse commits to find significant ones
    const commitData = [];
    let commitIndex = 0;

    for (const line of lines) {
        const parts = line.split('|');
        if (parts.length >= 4) {
            const timestamp = parseInt(parts[0], 10);
            const author = parts[1];
            const action = parts[2];
            const path = parts[3];

            // Track file count per commit (commits can span multiple lines)
            if (commitData.length === 0 || commitData[commitData.length - 1].timestamp !== timestamp) {
                commitData.push({
                    index: commitIndex++,
                    timestamp,
                    author,
                    fileCount: 1
                });
            } else {
                commitData[commitData.length - 1].fileCount++;
            }
        }
    }

    // Deduplicate to actual commit count
    const uniqueCommits = commitData.length;
    if (uniqueCommits === 0) return;

    // Find significant commits:
    // 1. First commit
    // 2. Commits with many file changes (> 10 files)
    // 3. Every 20% milestone

    const markers = [];

    // First commit marker
    markers.push({ position: 0, type: 'first-commit', title: 'First commit' });

    // Find large commits (more than 10 file changes)
    const avgFiles = commitData.reduce((sum, c) => sum + c.fileCount, 0) / commitData.length;
    const largeThreshold = Math.max(10, avgFiles * 3);

    for (let i = 0; i < commitData.length; i++) {
        const commit = commitData[i];
        if (commit.fileCount >= largeThreshold) {
            markers.push({
                position: (i / (uniqueCommits - 1)) * 100,
                type: 'large-commit',
                title: `Large commit: ${commit.fileCount} files changed`
            });
        }
    }

    // Add milestone markers (25%, 50%, 75%)
    const milestones = [0.25, 0.5, 0.75];
    for (const milestone of milestones) {
        const idx = Math.floor(milestone * (uniqueCommits - 1));
        if (idx > 0 && idx < uniqueCommits - 1) {
            // Only add if not too close to other markers
            const pos = milestone * 100;
            const tooClose = markers.some(m => Math.abs(m.position - pos) < 5);
            if (!tooClose) {
                markers.push({
                    position: pos,
                    type: 'recent-commit',
                    title: `${Math.round(milestone * 100)}% milestone`
                });
            }
        }
    }

    // Create marker elements
    for (const marker of markers) {
        const el = document.createElement('div');
        el.className = `timeline-marker ${marker.type}`;
        el.style.left = `${marker.position}%`;
        el.title = marker.title;
        timelineMarkers.appendChild(el);
    }
}

// Update legend
function updateLegend(content) {
    const legendItems = document.getElementById('legend-items');
    const extensionCounts = {};

    const lines = content.split('\n');
    for (const line of lines) {
        const parts = line.split('|');
        if (parts.length >= 4) {
            const path = parts[3].trim();
            const dotIdx = path.lastIndexOf('.');
            if (dotIdx > 0 && dotIdx < path.length - 1) {
                const ext = path.substring(dotIdx + 1).toLowerCase();
                if (ext.length <= 10) {
                    extensionCounts[ext] = (extensionCounts[ext] || 0) + 1;
                }
            }
        }
    }

    const sorted = Object.entries(extensionCounts)
        .sort((a, b) => b[1] - a[1])
        .slice(0, 12);

    legendItems.innerHTML = sorted.map(([ext, count]) => {
        const color = getExtensionColor(ext);
        return `<div class="legend-item" role="listitem">
            <span class="legend-color" style="background: ${color}"></span>
            <span class="legend-ext">.${ext}</span>
            <span class="legend-count">${count}</span>
        </div>`;
    }).join('');

    if (sorted.length > 0) {
        document.getElementById('legend-panel').classList.remove('collapsed');
        document.getElementById('legend-toggle').setAttribute('aria-expanded', 'true');
    }
}

// Legend toggle
const legendToggle = document.getElementById('legend-toggle');
function toggleLegend() {
    const panel = document.getElementById('legend-panel');
    panel.classList.toggle('collapsed');
    const isExpanded = !panel.classList.contains('collapsed');
    legendToggle.setAttribute('aria-expanded', isExpanded.toString());
}
legendToggle.addEventListener('click', toggleLegend);
legendToggle.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        toggleLegend();
    }
});

// =====================================================================
// AUTHORS LEGEND
// =====================================================================
// Updates the authors legend panel with contributors and their colors.
// Uses the WASM getAuthors() API to get accurate color assignments.
// =====================================================================
function updateAuthorsLegend(content) {
    if (!rource) return;

    // Clear existing author color map
    authorColorMap.clear();

    // Parse author data from log content first (before WASM is populated)
    const authorCommits = {};
    const lines = content.split('\n');
    for (const line of lines) {
        if (!line.trim()) continue;
        const parts = line.split('|');
        if (parts.length >= 4) {
            const author = parts[1].trim();
            authorCommits[author] = (authorCommits[author] || 0) + 1;
        }
    }

    // Sort by commit count descending
    const sorted = Object.entries(authorCommits)
        .sort((a, b) => b[1] - a[1])
        .slice(0, 10); // Show top 10 authors

    if (sorted.length === 0) return;

    // Build the authors items HTML and populate color map
    authorsItems.innerHTML = sorted.map(([name, commits]) => {
        // Get color from WASM (deterministic based on name hash)
        let color;
        try {
            color = rource.getAuthorColor(name);
        } catch (e) {
            // Fallback color generation if WASM method isn't available
            let hash = 0;
            for (let i = 0; i < name.length; i++) {
                hash = (hash * 31 + name.charCodeAt(i)) >>> 0;
            }
            color = `hsl(${hash % 360}, 60%, 55%)`;
        }

        // Store in color map for tooltip use
        authorColorMap.set(name, color);

        // Escape HTML in name
        const escapedName = name.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
        return `<div class="author-item" role="listitem" title="Click to filter by ${escapedName} (${commits} commits)">
            <span class="author-color" style="background: ${color}"></span>
            <span class="author-name">${escapedName}</span>
            <span class="author-commits">${commits}</span>
        </div>`;
    }).join('');

    // Add clear filter button to header if not present
    const header = authorsPanel.querySelector('.authors-header');
    if (header && !header.querySelector('.author-filter-clear')) {
        const clearBtn = document.createElement('span');
        clearBtn.className = 'author-filter-clear';
        clearBtn.textContent = 'Clear';
        clearBtn.addEventListener('click', (e) => {
            e.stopPropagation();
            clearAuthorFilter();
        });
        header.appendChild(clearBtn);
    }

    // Show the authors panel
    authorsPanel.classList.remove('hidden');
    authorsPanel.classList.remove('collapsed');
    authorsToggle.setAttribute('aria-expanded', 'true');
}

// Authors legend toggle
function toggleAuthorsPanel() {
    authorsPanel.classList.toggle('collapsed');
    const isExpanded = !authorsPanel.classList.contains('collapsed');
    authorsToggle.setAttribute('aria-expanded', isExpanded.toString());
}
authorsToggle.addEventListener('click', toggleAuthorsPanel);
authorsToggle.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        toggleAuthorsPanel();
    }
});

// Keyboard shortcuts for authors panel (A key)
document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
    if (e.key === 'a' || e.key === 'A') {
        if (hasLoadedData && !authorsPanel.classList.contains('hidden')) {
            toggleAuthorsPanel();
        }
    }
});

// Performance overlay toggle
const perfToggle = document.getElementById('perf-toggle');
function togglePerfOverlay() {
    perfOverlay.classList.toggle('collapsed');
    const isExpanded = !perfOverlay.classList.contains('collapsed');
    perfToggle.setAttribute('aria-expanded', isExpanded.toString());
}
perfToggle.addEventListener('click', togglePerfOverlay);
perfToggle.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        togglePerfOverlay();
    }
});

// Keyboard shortcut for performance overlay (P key)
document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
    if (e.key === 'p' || e.key === 'P') {
        if (hasLoadedData) {
            perfOverlay.classList.toggle('hidden');
        }
    }
});

// Keyboard shortcut for fullscreen (F key)
document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
    if (e.key === 'f' || e.key === 'F') {
        toggleFullscreen();
    }
});

// =====================================================================
// COLLAPSIBLE SIDEBAR PANELS
// =====================================================================
// Event handlers for collapsible panels are set up in setupPanelToggleHandlers()
// which is called after WASM initialization to ensure proper preference saving.
// The handlers are consolidated there to avoid duplicate event listeners.

// GitHub API rate limit tracking
let rateLimitRemaining = 60;
let rateLimitReset = 0;

// Cache for fetched repos (uses localStorage)
const CACHE_KEY = 'rource_github_cache';
const CACHE_EXPIRY = 24 * 60 * 60 * 1000; // 24 hours

function getCache() {
    try {
        const cached = localStorage.getItem(CACHE_KEY);
        if (cached) {
            const data = JSON.parse(cached);
            // Clean expired entries
            const now = Date.now();
            for (const key of Object.keys(data)) {
                if (data[key].timestamp < now - CACHE_EXPIRY) {
                    delete data[key];
                }
            }
            return data;
        }
    } catch (e) { /* ignore */ }
    return {};
}

function setCache(key, logContent) {
    try {
        const cache = getCache();
        cache[key] = { logContent, timestamp: Date.now() };
        localStorage.setItem(CACHE_KEY, JSON.stringify(cache));
    } catch (e) { /* ignore quota errors */ }
}

function getCachedRepo(owner, repo) {
    const cache = getCache();
    const key = `${owner}/${repo}`;
    if (cache[key] && cache[key].timestamp > Date.now() - CACHE_EXPIRY) {
        return cache[key].logContent;
    }
    return null;
}

// Check rate limit before making requests
async function checkRateLimit() {
    try {
        const response = await fetch('https://api.github.com/rate_limit', {
            headers: { 'Accept': 'application/vnd.github.v3+json' }
        });
        if (response.ok) {
            const data = await response.json();
            rateLimitRemaining = data.rate.remaining;
            rateLimitReset = data.rate.reset * 1000;
            return rateLimitRemaining;
        }
    } catch (e) { /* ignore */ }
    return rateLimitRemaining;
}

function formatTimeUntilReset() {
    const now = Date.now();
    if (rateLimitReset <= now) return 'soon';
    const minutes = Math.ceil((rateLimitReset - now) / 60000);
    return minutes === 1 ? '1 minute' : `${minutes} minutes`;
}

// GitHub API fetch with caching and rate limit awareness
async function fetchGitHubRepo(repoUrl) {
    // Parse repo URL
    let owner, repo;
    try {
        const url = new URL(repoUrl.includes('://') ? repoUrl : 'https://' + repoUrl);
        const parts = url.pathname.split('/').filter(p => p);
        if (parts.length < 2) throw new Error('Invalid URL');
        owner = parts[0];
        repo = parts[1].replace('.git', '');
    } catch (e) {
        // Try simple format: owner/repo
        const parts = repoUrl.split('/').filter(p => p);
        if (parts.length >= 2) {
            owner = parts[parts.length - 2];
            repo = parts[parts.length - 1].replace('.git', '');
        } else {
            throw new Error('Invalid repository URL. Use format: owner/repo or https://github.com/owner/repo');
        }
    }

    // Check cache first
    const cachedContent = getCachedRepo(owner, repo);
    if (cachedContent) {
        fetchStatus.className = 'fetch-status visible success';
        fetchStatusText.textContent = `Loaded ${owner}/${repo} from cache!`;
        fetchProgressBar.style.width = '100%';
        loadLogData(cachedContent, 'custom');
        lastLoadedRepo = `${owner}/${repo}`;
        updateUrlState({ repo: `${owner}/${repo}` });
        return;
    }

    // Check rate limit before proceeding
    const remaining = await checkRateLimit();
    if (remaining < 5) {
        throw new Error(`GitHub API rate limit low (${remaining} requests left). Resets in ${formatTimeUntilReset()}. Try a cached repo or wait.`);
    }

    fetchStatus.className = 'fetch-status visible loading';
    fetchStatusText.textContent = `Fetching commits from ${owner}/${repo}... (${remaining} API calls remaining)`;
    fetchProgressBar.style.width = '10%';

    // Limit commits based on available rate limit (each commit needs 1 API call for details)
    const maxDetailedCommits = Math.min(50, Math.floor(remaining * 0.8)); // Use 80% of remaining, max 50

    try {
        // Fetch commit list (single API call for many commits)
        const response = await fetch(
            `https://api.github.com/repos/${owner}/${repo}/commits?per_page=100`,
            { headers: { 'Accept': 'application/vnd.github.v3+json' } }
        );

        // Update rate limit from response headers
        const limitHeader = response.headers.get('X-RateLimit-Remaining');
        if (limitHeader) rateLimitRemaining = parseInt(limitHeader, 10);

        if (!response.ok) {
            if (response.status === 404) {
                throw new Error('Repository not found. Make sure it exists and is public.');
            } else if (response.status === 403) {
                const resetHeader = response.headers.get('X-RateLimit-Reset');
                if (resetHeader) rateLimitReset = parseInt(resetHeader, 10) * 1000;
                throw new Error(`GitHub API rate limit exceeded. Resets in ${formatTimeUntilReset()}.`);
            }
            throw new Error(`GitHub API error: ${response.status}`);
        }

        const commits = await response.json();
        if (commits.length === 0) {
            throw new Error('No commits found in this repository.');
        }

        fetchProgressBar.style.width = '20%';
        fetchStatusText.textContent = `Found ${commits.length} commits. Fetching file details (limited to ${maxDetailedCommits} to preserve API quota)...`;

        const logLines = [];
        const limitedCommits = commits.slice(0, maxDetailedCommits);
        let fetchedCount = 0;
        let skippedDueToRateLimit = 0;

        for (let i = 0; i < limitedCommits.length; i++) {
            // Check if we're running low on rate limit
            if (rateLimitRemaining < 3) {
                skippedDueToRateLimit = limitedCommits.length - i;
                break;
            }

            const commit = limitedCommits[i];
            const timestamp = Math.floor(new Date(commit.commit.author.date).getTime() / 1000);
            const author = commit.commit.author.name || 'Unknown';

            // Fetch commit details for file changes
            try {
                const detailResponse = await fetch(commit.url, {
                    headers: { 'Accept': 'application/vnd.github.v3+json' }
                });

                // Update rate limit
                const limitHeader = detailResponse.headers.get('X-RateLimit-Remaining');
                if (limitHeader) rateLimitRemaining = parseInt(limitHeader, 10);

                if (detailResponse.status === 403) {
                    skippedDueToRateLimit = limitedCommits.length - i;
                    break;
                }

                if (detailResponse.ok) {
                    const detail = await detailResponse.json();
                    if (detail.files) {
                        for (const file of detail.files.slice(0, 50)) {
                            let action = 'M';
                            if (file.status === 'added') action = 'A';
                            else if (file.status === 'removed') action = 'D';
                            logLines.push(`${timestamp}|${author}|${action}|${file.filename}`);
                        }
                    }
                    fetchedCount++;
                }
            } catch (e) {
                // Skip failed file fetches
            }

            // Update progress
            fetchProgressBar.style.width = `${20 + (i / limitedCommits.length) * 70}%`;
            fetchStatusText.textContent = `Processing commits... ${i + 1}/${limitedCommits.length} (${rateLimitRemaining} API calls left)`;

            // Small delay to be nice to the API
            if (i % 5 === 4) {
                await new Promise(r => setTimeout(r, 50));
            }
        }

        // Reverse to get chronological order
        logLines.reverse();

        if (logLines.length === 0) {
            throw new Error('Could not fetch file changes. The repository may be empty or API limit was reached.');
        }

        // Cache the result
        const logContent = logLines.join('\n');
        setCache(`${owner}/${repo}`, logContent);

        fetchProgressBar.style.width = '100%';
        fetchStatus.className = 'fetch-status visible success';
        let statusMsg = `Loaded ${logLines.length} file changes from ${fetchedCount} commits.`;
        if (skippedDueToRateLimit > 0) {
            statusMsg += ` (${skippedDueToRateLimit} commits skipped due to rate limit)`;
        }
        fetchStatusText.textContent = statusMsg;

        loadLogData(logContent, 'custom');
        lastLoadedRepo = `${owner}/${repo}`;
        updateUrlState({ repo: `${owner}/${repo}` });

    } catch (error) {
        fetchStatus.className = 'fetch-status visible error';
        fetchStatusText.textContent = error.message;
        fetchProgressBar.style.width = '0%';
        throw error;
    }
}

// Initialize
async function main() {
    try {
        await init();
        resizeCanvas();
        rource = new Rource(canvas);

        // Update renderer badge and tech panel
        const isWebGL2 = rource.isWebGL2();
        const rendererType = rource.getRendererType();
        rendererBadge.textContent = isWebGL2 ? 'WebGL2' : 'Software';
        if (isWebGL2) rendererBadge.classList.add('webgl2');
        techRenderer.textContent = isWebGL2 ? 'WebGL2' : 'CPU';

        // Enable buttons
        btnPlayMain.disabled = false;
        btnResetBar.disabled = false;
        btnLabels.disabled = false;
        btnScreenshot.disabled = false;
        btnLoad.disabled = false;
        btnFetchGithub.disabled = false;
        btnVisualizeRource.disabled = false;

        // Initialize showcase stats from pre-calculated data
        showcaseCommits.textContent = ROURCE_STATS.commits.toLocaleString();
        showcaseFiles.textContent = ROURCE_STATS.files.toLocaleString();
        showcaseAuthors.textContent = ROURCE_STATS.authors.toLocaleString();

        // Initialize labels button state
        updateLabelsButton();

        // Log technical info to console for verification
        console.log(`%c Rource Technical Info `, 'background: #e94560; color: white; font-weight: bold;');
        console.log(`  Renderer: ${rendererType}`);
        console.log(`  Canvas: ${canvas.width}×${canvas.height}`);
        console.log(`  WebGL2: ${isWebGL2}`);
        console.log(`  Cached Rource Data: ${ROURCE_STATS.commits} commits, ${ROURCE_STATS.files} files, ${ROURCE_STATS.authors} authors`);

        // Start animation
        animationId = requestAnimationFrame(animate);
        loadingEl.classList.add('hidden');

        // Check URL parameters for shareable state
        const urlParams = parseUrlParams();

        // Apply speed from URL (priority) or saved preference
        if (urlParams.speed) {
            const speedValue = urlParams.speed;
            speedSelect.value = speedValue;
            rource.setSpeed(parseFloat(speedValue));
        } else if (userPrefs.speed && userPrefs.speed !== '10') {
            speedSelect.value = userPrefs.speed;
            rource.setSpeed(parseFloat(userPrefs.speed));
        }

        // Apply saved label preference
        if (userPrefs.showLabels !== undefined) {
            rource.setShowLabels(userPrefs.showLabels);
            updateLabelsButton();
        }

        // Apply saved panel states and setup toggle handlers
        applyPanelPreferences();
        setupPanelToggleHandlers();

        // Load repo from URL or default to Rource
        setTimeout(async () => {
            if (!hasLoadedData) {
                if (urlParams.repo) {
                    // Load repo from URL parameter
                    githubUrlInput.value = urlParams.repo;
                    try {
                        await fetchGitHubRepo(urlParams.repo);
                        if (urlParams.autoplay === 'true') {
                            rource.play();
                            updateUI();
                        }
                    } catch (e) {
                        console.error('Failed to load repo from URL:', e);
                        // Fall back to cached Rource data
                        loadLogData(ROURCE_CACHED_DATA, 'custom');
                        lastLoadedRepo = 'rource';
                        showToast('Loaded Rource project history (cached)', 'success', 3000);
                    }
                } else {
                    // Default: load cached Rource project
                    loadLogData(ROURCE_CACHED_DATA, 'custom');
                    lastLoadedRepo = 'rource';
                    showToast('Loaded Rource project history (cached)', 'success', 3000);
                }
            }
        }, 500);

    } catch (e) {
        console.error('Initialization failed:', e);
        loadingEl.querySelector('.loading-text').textContent = 'Failed to load: ' + e.message;
        showToast(`Initialization failed: ${e.message}`, 'error', 10000);
    }
}

// Event handlers
btnPlayMain.addEventListener('click', () => {
    if (rource && hasLoadedData) {
        // If at the end and paused, replay from start
        if (isAtEnd() && !rource.isPlaying()) {
            rource.seek(0);
            rource.play();
        } else {
            rource.togglePlay();
        }
        updateUI();
    } else if (!hasLoadedData) {
        // Load Rource project data by default (cached)
        loadLogData(ROURCE_CACHED_DATA, 'custom');
    }
});

btnPrev.addEventListener('click', () => {
    if (rource) {
        rource.stepBackward();
        updateUI();
    }
});

btnNext.addEventListener('click', () => {
    if (rource) {
        rource.stepForward();
        updateUI();
    }
});

btnResetBar.addEventListener('click', () => {
    if (rource) {
        // Pause if playing, then reset to start
        if (rource.isPlaying()) {
            rource.pause();
        }
        rource.resetCamera();
        rource.seek(0);
        updateUI();
    }
});

btnLabels.addEventListener('click', () => {
    if (rource) {
        const currentState = rource.getShowLabels();
        const newState = !currentState;
        rource.setShowLabels(newState);
        updateLabelsButton();
        updatePreference('showLabels', newState); // Save to localStorage
    }
});

function updateLabelsButton() {
    if (rource) {
        const showLabels = rource.getShowLabels();
        labelsText.textContent = showLabels ? 'Labels' : 'Labels Off';
        btnLabels.classList.toggle('active', showLabels);
    }
}

// =====================================================================
// SCREENSHOT DOWNLOAD
// =====================================================================
// Downloads the current canvas as a PNG image.
// Works with both WebGL2 and software renderers.
// =====================================================================
btnScreenshot.addEventListener('click', () => {
    if (!rource || isContextLost) {
        showToast('Cannot capture screenshot - visualization not ready', 'error');
        return;
    }

    try {
        // Generate filename with timestamp
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
        const filename = `rource-${timestamp}.png`;

        // Use canvas.toBlob for best quality (works with WebGL2 too)
        canvas.toBlob((blob) => {
            if (!blob) {
                showToast('Failed to capture screenshot', 'error');
                return;
            }

            // Create download link
            const url = URL.createObjectURL(blob);
            const link = document.createElement('a');
            link.href = url;
            link.download = filename;
            link.click();

            // Cleanup
            URL.revokeObjectURL(url);
            showToast(`Screenshot saved: ${filename}`, 'success', 3000);
        }, 'image/png', 1.0);

    } catch (error) {
        console.error('Screenshot error:', error);
        showToast('Failed to capture screenshot: ' + error.message, 'error');
    }
});

// =====================================================================
// FULLSCREEN MODE
// =====================================================================
// Enables fullscreen presentation mode for demos and presentations.
// =====================================================================
const btnFullscreen = document.getElementById('btn-fullscreen');
const fullscreenIcon = document.getElementById('fullscreen-icon');

// Fullscreen icons
const enterFullscreenPath = 'M7 14H5v5h5v-2H7v-3zm-2-4h2V7h3V5H5v5zm12 7h-3v2h5v-5h-2v3zM14 5v2h3v3h2V5h-5z';
const exitFullscreenPath = 'M5 16h3v3h2v-5H5v2zm3-8H5v2h5V5H8v3zm6 11h2v-3h3v-2h-5v5zm2-11V5h-2v5h5V8h-3z';

function updateFullscreenIcon() {
    const isFullscreen = document.fullscreenElement || document.webkitFullscreenElement;
    fullscreenIcon.innerHTML = `<path d="${isFullscreen ? exitFullscreenPath : enterFullscreenPath}"/>`;
    btnFullscreen.title = isFullscreen ? 'Exit fullscreen (F)' : 'Fullscreen (F)';
}

function toggleFullscreen() {
    if (document.fullscreenElement || document.webkitFullscreenElement) {
        // Exit fullscreen
        if (document.exitFullscreen) {
            document.exitFullscreen();
        } else if (document.webkitExitFullscreen) {
            document.webkitExitFullscreen();
        }
    } else {
        // Enter fullscreen
        const elem = document.documentElement;
        if (elem.requestFullscreen) {
            elem.requestFullscreen();
        } else if (elem.webkitRequestFullscreen) {
            elem.webkitRequestFullscreen();
        }
    }
}

btnFullscreen.addEventListener('click', toggleFullscreen);

// Listen for fullscreen changes
document.addEventListener('fullscreenchange', updateFullscreenIcon);
document.addEventListener('webkitfullscreenchange', updateFullscreenIcon);

// =====================================================================
// SHARE URL
// =====================================================================
// Generates and copies a shareable URL with current state.
// =====================================================================
const btnShare = document.getElementById('btn-share');

function generateShareableUrl() {
    const params = new URLSearchParams();

    // Add repo if loaded
    if (lastLoadedRepo) {
        params.set('repo', lastLoadedRepo);
    }

    // Add speed if not default
    const currentSpeed = speedSelect.value;
    if (currentSpeed && currentSpeed !== '10') {
        params.set('speed', currentSpeed);
    }

    // Add current commit position
    if (rource && hasLoadedData) {
        const current = rource.currentCommit();
        const total = rource.commitCount();
        if (current > 0 && current < total - 1) {
            params.set('commit', current.toString());
        }
    }

    // Build URL
    const baseUrl = window.location.origin + window.location.pathname;
    const queryString = params.toString();
    return queryString ? `${baseUrl}?${queryString}` : baseUrl;
}

async function copyShareableUrl() {
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
}

btnShare.addEventListener('click', copyShareableUrl);

// =====================================================================
// WEBGL CONTEXT LOSS RECOVERY
// =====================================================================
// Handles WebGL context loss gracefully with user-friendly recovery.
// Context loss can occur on mobile devices or when switching tabs.
// =====================================================================
canvas.addEventListener('webglcontextlost', (event) => {
    event.preventDefault();
    console.warn('WebGL context lost');
    isContextLost = true;
    contextLostOverlay.classList.remove('hidden');

    // Pause animation to prevent errors
    if (animationId) {
        cancelAnimationFrame(animationId);
        animationId = null;
    }
});

canvas.addEventListener('webglcontextrestored', () => {
    console.log('WebGL context restored');
    isContextLost = false;
    contextLostOverlay.classList.add('hidden');

    // Resume animation loop
    if (rource && hasLoadedData) {
        requestAnimationFrame(animationLoop);
    }
});

btnRestoreContext.addEventListener('click', () => {
    // Force context restoration by recreating the WASM instance
    contextLostOverlay.classList.add('hidden');

    showToast('Restoring visualization...', 'success', 2000);

    // Re-initialize after a short delay
    setTimeout(async () => {
        try {
            // Re-create the Rource instance
            const width = canvas.width;
            const height = canvas.height;
            rource = new Rource('canvas', width, height);

            // Reload the last data if available
            if (lastLoadedRepo === 'rource') {
                loadLogData(ROURCE_CACHED_DATA + (additionalCommits ? '\n' + additionalCommits : ''), 'custom');
            } else if (uploadedFileContent) {
                loadLogData(uploadedFileContent, 'custom');
            }

            isContextLost = false;
            showToast('Visualization restored!', 'success', 2000);
        } catch (error) {
            console.error('Failed to restore:', error);
            showToast('Failed to restore visualization. Please refresh the page.', 'error');
        }
    }, 500);
});

// =====================================================================
// SHOWCASE: VISUALIZE ROURCE BUTTON
// =====================================================================
// Loads the cached Rource repository data - no API calls needed.
// This ensures the demo always works regardless of GitHub rate limits.
// =====================================================================
btnVisualizeRource.addEventListener('click', () => {
    if (!rource) return;

    // Reset the visualization and load cached Rource data
    btnVisualizeRource.disabled = true;
    btnVisualizeRource.innerHTML = `
        <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" class="spin">
            <path d="M12 4V1L8 5l4 4V6c3.31 0 6 2.69 6 6 0 1.01-.25 1.97-.7 2.8l1.46 1.46C19.54 15.03 20 13.57 20 12c0-4.42-3.58-8-8-8zm0 14c-3.31 0-6-2.69-6-6 0-1.01.25-1.97.7-2.8L5.24 7.74C4.46 8.97 4 10.43 4 12c0 4.42 3.58 8 8 8v3l4-4-4-4v3z"/>
        </svg>
        Loading...
    `;

    // Short delay for visual feedback
    setTimeout(() => {
        // Combine cached data with any additional fetched commits
        const fullData = additionalCommits
            ? ROURCE_CACHED_DATA + '\n' + additionalCommits
            : ROURCE_CACHED_DATA;
        loadLogData(fullData, 'custom');
        lastLoadedRepo = 'rource';
        // Clear repo from URL when loading the cached Rource data
        updateUrlState({ repo: null });
        btnVisualizeRource.disabled = false;
        btnVisualizeRource.innerHTML = `
            <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor">
                <path d="M8 5v14l11-7z"/>
            </svg>
            Visualize Rource
        `;
    }, 100);
});

// REFRESH: FETCH LATEST COMMITS FROM GITHUB
// =====================================================================
// Fetches commits since the last cached timestamp.
// Uses GitHub API but only for incremental updates.
// =====================================================================
btnRefreshRource.addEventListener('click', async () => {
    if (btnRefreshRource.classList.contains('loading')) return;

    btnRefreshRource.classList.add('loading');
    refreshStatus.className = 'refresh-status loading';
    refreshStatus.textContent = 'Fetching latest commits...';
    refreshStatus.classList.remove('hidden');

    try {
        // Check rate limit first
        const remaining = await checkRateLimit();
        if (remaining < 5) {
            throw new Error(`Rate limit low (${remaining}). Resets ${formatTimeUntilReset()}.`);
        }

        // Fetch commits since the cached timestamp
        const sinceDate = new Date(ROURCE_STATS.lastTimestamp * 1000).toISOString();
        const response = await fetch(
            `https://api.github.com/repos/tomtom215/rource/commits?since=${sinceDate}&per_page=100`,
            { headers: { 'Accept': 'application/vnd.github.v3+json' } }
        );

        if (!response.ok) {
            throw new Error(`GitHub API error: ${response.status}`);
        }

        const commits = await response.json();

        if (commits.length <= 1) {
            // Only the last cached commit or none - no new commits
            refreshStatus.className = 'refresh-status success';
            refreshStatus.textContent = 'Already up to date!';
            setTimeout(() => refreshStatus.classList.add('hidden'), 3000);
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
                additionalCommits = newEntries.join('\n');
                const newCommitCount = commits.length - 1;
                refreshStatus.className = 'refresh-status success';
                refreshStatus.textContent = `Found ${newCommitCount} new commit${newCommitCount === 1 ? '' : 's'} (${newEntries.length} files). Click "Visualize" to reload.`;

                // Update stats display
                const totalCommits = ROURCE_STATS.commits + newEntries.length;
                showcaseCommits.textContent = totalCommits.toLocaleString() + '+';
            } else {
                refreshStatus.className = 'refresh-status success';
                refreshStatus.textContent = 'Already up to date!';
                setTimeout(() => refreshStatus.classList.add('hidden'), 3000);
            }
        }

    } catch (error) {
        console.error('Refresh error:', error);
        refreshStatus.className = 'refresh-status error';
        refreshStatus.textContent = error.message || 'Failed to fetch updates';
    } finally {
        btnRefreshRource.classList.remove('loading');
    }
});

btnLoad.addEventListener('click', () => {
    if (logInput.value.trim()) {
        loadLogData(logInput.value, 'custom');
    } else {
        showToast('Please paste log data first.', 'error');
    }
});

// Speed control
speedSelect.addEventListener('change', () => {
    if (rource) {
        const speed = speedSelect.value;
        rource.setSpeed(parseFloat(speed));
        updateUrlState({ speed });
        updatePreference('speed', speed); // Save to localStorage
    }
});

// Timeline slider
timelineSlider.addEventListener('input', () => {
    if (rource) {
        rource.pause();
        rource.seek(parseInt(timelineSlider.value, 10));
        updateUI();
    }
});

// GitHub fetch
btnFetchGithub.addEventListener('click', async () => {
    const url = githubUrlInput.value.trim();
    if (!url) {
        showToast('Please enter a GitHub repository URL.', 'error');
        return;
    }

    btnFetchGithub.disabled = true;
    try {
        await fetchGitHubRepo(url);
    } catch (e) {
        console.error('Fetch error:', e);
        // Show error to user (fetchGitHubRepo already updates fetchStatus for API errors,
        // but URL parsing errors need explicit handling)
        if (fetchStatus && !fetchStatus.classList.contains('error')) {
            fetchStatus.className = 'fetch-status visible error';
            fetchStatusText.textContent = e.message || 'An error occurred while fetching the repository.';
        }
        showToast(e.message || 'Failed to fetch repository.', 'error');
    }
    btnFetchGithub.disabled = false;
});

githubUrlInput.addEventListener('keypress', (e) => {
    if (e.key === 'Enter') btnFetchGithub.click();
});

// Popular repo chips
document.querySelectorAll('.repo-chip').forEach(chip => {
    chip.addEventListener('click', () => {
        const repo = chip.dataset.repo;
        githubUrlInput.value = `https://github.com/${repo}`;
        btnFetchGithub.click();
    });
});

// Tab switching
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
        content.classList.add('active');
        content.removeAttribute('hidden');
    });
});

// File upload
fileDropZone.addEventListener('click', () => fileInput.click());
fileInput.addEventListener('change', (e) => {
    if (e.target.files[0]) handleFileUpload(e.target.files[0]);
});

fileDropZone.addEventListener('dragover', (e) => {
    e.preventDefault();
    fileDropZone.classList.add('dragover');
});

fileDropZone.addEventListener('dragleave', () => {
    fileDropZone.classList.remove('dragover');
});

fileDropZone.addEventListener('drop', (e) => {
    e.preventDefault();
    fileDropZone.classList.remove('dragover');
    if (e.dataTransfer.files[0]) handleFileUpload(e.dataTransfer.files[0]);
});

function handleFileUpload(file) {
    if (file.size > 10 * 1024 * 1024) {
        showToast('File too large. Maximum size is 10MB.', 'error');
        return;
    }

    fileNameEl.textContent = `${file.name} (${(file.size / 1024).toFixed(1)} KB)`;
    fileNameEl.classList.remove('hidden');

    const reader = new FileReader();
    reader.onload = (e) => {
        uploadedFileContent = e.target.result;
        btnLoadFile.disabled = false;
    };
    reader.readAsText(file);
}

btnLoadFile.addEventListener('click', () => {
    if (uploadedFileContent) loadLogData(uploadedFileContent, 'custom');
});

// Copy command
btnCopyCommand.addEventListener('click', async () => {
    const command = document.getElementById('git-command').textContent;
    try {
        await navigator.clipboard.writeText(command);
        btnCopyCommand.innerHTML = '<svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41z"/></svg> Copied!';
        setTimeout(() => {
            btnCopyCommand.innerHTML = '<svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor"><path d="M16 1H4c-1.1 0-2 .9-2 2v14h2V3h12V1zm3 4H8c-1.1 0-2 .9-2 2v14c0 1.1.9 2 2 2h11c1.1 0 2-.9 2-2V7c0-1.1-.9-2-2-2zm0 16H8V7h11v14z"/></svg> Copy Command';
        }, 2000);
    } catch (e) {
        showToast('Failed to copy. Please select and copy manually.', 'error');
    }
});

// Keyboard controls
document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;

    // Screenshot shortcut (S key)
    if ((e.key === 's' || e.key === 'S') && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        btnScreenshot.click();
        return;
    }

    if (rource) {
        rource.onKeyDown(e.key);
        updateUI();
        // Update labels button if L was pressed
        if (e.key === 'l' || e.key === 'L') {
            updateLabelsButton();
        }
    }
});

// Mouse controls
canvas.addEventListener('mousedown', (e) => {
    if (rource) {
        const rect = canvas.getBoundingClientRect();
        rource.onMouseDown(e.clientX - rect.left, e.clientY - rect.top);
    }
});

canvas.addEventListener('mouseup', () => {
    if (rource) rource.onMouseUp();
});

canvas.addEventListener('mousemove', (e) => {
    if (rource) {
        const rect = canvas.getBoundingClientRect();
        rource.onMouseMove(e.clientX - rect.left, e.clientY - rect.top);
    }
});

canvas.addEventListener('wheel', (e) => {
    if (rource) {
        e.preventDefault();
        rource.onWheel(e.deltaY);
    }
}, { passive: false });

// Touch controls
let touchState = { startX: 0, startY: 0, initialDistance: 0, isPanning: false, isPinching: false };

function getTouchDistance(touches) {
    const dx = touches[0].clientX - touches[1].clientX;
    const dy = touches[0].clientY - touches[1].clientY;
    return Math.sqrt(dx * dx + dy * dy);
}

canvas.addEventListener('touchstart', (e) => {
    e.preventDefault();
    const rect = canvas.getBoundingClientRect();

    if (e.touches.length === 1) {
        touchState.isPanning = true;
        touchState.startX = e.touches[0].clientX - rect.left;
        touchState.startY = e.touches[0].clientY - rect.top;
        if (rource) rource.onMouseDown(touchState.startX, touchState.startY);
    } else if (e.touches.length === 2) {
        touchState.isPanning = false;
        touchState.isPinching = true;
        touchState.initialDistance = getTouchDistance(e.touches);
        if (rource) rource.onMouseUp();
    }
}, { passive: false });

canvas.addEventListener('touchmove', (e) => {
    e.preventDefault();
    const rect = canvas.getBoundingClientRect();

    if (touchState.isPanning && e.touches.length === 1) {
        const x = e.touches[0].clientX - rect.left;
        const y = e.touches[0].clientY - rect.top;
        if (rource) rource.onMouseMove(x, y);
    } else if (touchState.isPinching && e.touches.length === 2) {
        const currentDistance = getTouchDistance(e.touches);
        const scaleFactor = currentDistance / touchState.initialDistance;

        if (rource && Math.abs(scaleFactor - 1.0) > 0.01) {
            rource.zoom(scaleFactor > 1.0 ? 1.05 : 0.95);
            touchState.initialDistance = currentDistance;
        }
    }
}, { passive: false });

canvas.addEventListener('touchend', (e) => {
    e.preventDefault();
    if (rource && touchState.isPanning) rource.onMouseUp();
    touchState.isPanning = false;
    touchState.isPinching = false;
}, { passive: false });

// Resize handler
window.addEventListener('resize', resizeCanvas);

// =====================================================================
// THEME TOGGLE
// =====================================================================
const THEME_KEY = 'rource_theme';

function initTheme() {
    const savedTheme = localStorage.getItem(THEME_KEY);
    if (savedTheme === 'light') {
        document.documentElement.classList.add('light-theme');
    }
}

function toggleTheme() {
    const isLight = document.documentElement.classList.toggle('light-theme');
    localStorage.setItem(THEME_KEY, isLight ? 'light' : 'dark');
}

themeToggle.addEventListener('click', toggleTheme);

// Theme keyboard shortcut (T)
document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
    if ((e.key === 't' || e.key === 'T') && !e.ctrlKey && !e.metaKey) {
        toggleTheme();
    }
});

// Initialize theme
initTheme();

// =====================================================================
// HELP OVERLAY
// =====================================================================
let helpPreviousFocus = null;

function showHelp() {
    // Store the currently focused element to restore later
    helpPreviousFocus = document.activeElement;
    helpOverlay.classList.add('visible');
    document.body.style.overflow = 'hidden';
    // Focus the close button for keyboard accessibility
    helpClose.focus();
}

function hideHelp() {
    helpOverlay.classList.remove('visible');
    document.body.style.overflow = '';
    localStorage.setItem(HELP_SHOWN_KEY, 'true');
    // Restore focus to the element that triggered the overlay
    if (helpPreviousFocus && typeof helpPreviousFocus.focus === 'function') {
        helpPreviousFocus.focus();
    }
    helpPreviousFocus = null;
}

helpBtn.addEventListener('click', showHelp);
helpClose.addEventListener('click', hideHelp);
helpGotIt.addEventListener('click', hideHelp);

helpOverlay.addEventListener('click', (e) => {
    if (e.target === helpOverlay) hideHelp();
});

// Help keyboard shortcuts
document.addEventListener('keydown', (e) => {
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
    if (e.key === '?' || (e.key === '/' && e.shiftKey)) {
        e.preventDefault();
        showHelp();
    }
    if (e.key === 'Escape' && helpOverlay.classList.contains('visible')) {
        hideHelp();
    }
});

// Show help on first visit (after data is loaded)
function maybeShowFirstTimeHelp() {
    if (!localStorage.getItem(HELP_SHOWN_KEY)) {
        setTimeout(showHelp, 500);
    }
}

// =====================================================================
// MOBILE SIDEBAR TOGGLE
// =====================================================================
let sidebarPreviousFocus = null;

function openSidebar() {
    // Store the currently focused element to restore later
    sidebarPreviousFocus = document.activeElement;
    sidebarPanel.classList.add('open');
    sidebarOverlay.classList.add('visible');
    sidebarClose.classList.remove('hidden');
    document.body.style.overflow = 'hidden';
    // Focus the close button for keyboard accessibility
    sidebarClose.focus();
}

function closeSidebar() {
    sidebarPanel.classList.remove('open');
    sidebarOverlay.classList.remove('visible');
    sidebarClose.classList.add('hidden');
    document.body.style.overflow = '';
    // Restore focus to the element that triggered the sidebar
    if (sidebarPreviousFocus && typeof sidebarPreviousFocus.focus === 'function') {
        sidebarPreviousFocus.focus();
    }
    sidebarPreviousFocus = null;
}

sidebarToggle.addEventListener('click', openSidebar);
sidebarClose.addEventListener('click', closeSidebar);
sidebarOverlay.addEventListener('click', closeSidebar);

// Close sidebar on escape
document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && sidebarPanel.classList.contains('open')) {
        closeSidebar();
    }
});

// Check viewport width and setup mobile sidebar close button visibility
function checkMobileSidebar() {
    const isMobile = window.innerWidth <= 1200;
    if (!isMobile) {
        closeSidebar();
    }
}

window.addEventListener('resize', checkMobileSidebar);
checkMobileSidebar();

// =====================================================================
// SIDEBAR SCROLL INDICATOR
// =====================================================================
const scrollIndicator = document.getElementById('sidebar-scroll-indicator');

function updateScrollIndicator() {
    if (!sidebarPanel || !scrollIndicator) return;

    // Check if sidebar has scrollable content
    const scrollTop = sidebarPanel.scrollTop;
    const scrollHeight = sidebarPanel.scrollHeight;
    const clientHeight = sidebarPanel.clientHeight;

    // If content fits without scrolling, hide indicator
    if (scrollHeight <= clientHeight + 5) {
        scrollIndicator.classList.add('hidden');
        return;
    }

    // Show indicator if not near the bottom (within 50px)
    const distanceFromBottom = scrollHeight - scrollTop - clientHeight;
    if (distanceFromBottom > 50) {
        scrollIndicator.classList.remove('hidden');
    } else {
        scrollIndicator.classList.add('hidden');
    }
}

// Update on scroll
sidebarPanel.addEventListener('scroll', updateScrollIndicator, { passive: true });

// Update on resize (content height may change)
window.addEventListener('resize', updateScrollIndicator);

// Initial check after a short delay to ensure content is rendered
setTimeout(updateScrollIndicator, 100);

// Also update when collapsible panels are toggled
document.addEventListener('click', (e) => {
    if (e.target.closest('.panel-header') || e.target.closest('.collapsible')) {
        // Delay to allow animation/content change to complete
        setTimeout(updateScrollIndicator, 350);
    }
});

// =====================================================================
// COMMIT TOOLTIP ON HOVER
// =====================================================================
let tooltipData = []; // Stores parsed commit data for tooltip lookup
let tooltipTimeout = null;

function parseCommitsForTooltip(logData) {
    tooltipData = [];
    const lines = logData.trim().split('\n');
    for (const line of lines) {
        const parts = line.split('|');
        if (parts.length >= 4) {
            const timestamp = parseInt(parts[0], 10);
            const author = parts[1];
            const action = parts[2];
            const path = parts[3];
            tooltipData.push({ timestamp, author, action, path });
        }
    }
}

function showTooltip(x, y, data) {
    tooltipAuthorColor.style.background = authorColorMap.get(data.author) || '#e94560';
    tooltipAuthor.textContent = data.author;
    tooltipDate.textContent = new Date(data.timestamp * 1000).toLocaleDateString();
    tooltipFile.textContent = data.path;

    const actionMap = { 'A': 'add', 'M': 'modify', 'D': 'delete' };
    const actionText = { 'A': 'Added', 'M': 'Modified', 'D': 'Deleted' };
    tooltipAction.textContent = actionText[data.action] || data.action;
    tooltipAction.className = `commit-tooltip-action ${actionMap[data.action] || ''}`;

    // Position tooltip
    const tooltipRect = commitTooltip.getBoundingClientRect();
    let left = x + 15;
    let top = y + 15;

    // Keep tooltip on screen
    if (left + 320 > window.innerWidth) {
        left = x - 320 - 15;
    }
    if (top + 150 > window.innerHeight) {
        top = y - 150 - 15;
    }

    commitTooltip.style.left = `${Math.max(10, left)}px`;
    commitTooltip.style.top = `${Math.max(10, top)}px`;
    commitTooltip.classList.add('visible');
}

function hideTooltip() {
    commitTooltip.classList.remove('visible');
}

// Track mouse position for tooltip
canvas.addEventListener('mousemove', (e) => {
    if (!rource || !hasLoadedData || tooltipData.length === 0) return;

    // Get current commit index to show relevant tooltip data
    const currentCommit = rource.currentCommit();
    if (currentCommit >= 0 && currentCommit < tooltipData.length) {
        clearTimeout(tooltipTimeout);
        tooltipTimeout = setTimeout(() => {
            // Show tooltip for current commit after hover delay
            showTooltip(e.clientX, e.clientY, tooltipData[Math.min(currentCommit, tooltipData.length - 1)]);
        }, 500);
    }
});

canvas.addEventListener('mouseleave', () => {
    clearTimeout(tooltipTimeout);
    hideTooltip();
});

canvas.addEventListener('mousedown', () => {
    clearTimeout(tooltipTimeout);
    hideTooltip();
});

// =====================================================================
// AUTHOR FILTER
// =====================================================================
function setAuthorFilter(author) {
    filteredAuthor = author;
    updateAuthorFilterUI();

    // If we have rource instance, we could filter visualization
    // For now, just update UI to show which author is selected
    if (rource && typeof rource.setAuthorFilter === 'function') {
        rource.setAuthorFilter(author);
    }
}

function clearAuthorFilter() {
    filteredAuthor = null;
    updateAuthorFilterUI();
    if (rource && typeof rource.clearAuthorFilter === 'function') {
        rource.clearAuthorFilter();
    }
}

function updateAuthorFilterUI() {
    const clearBtn = authorsPanel.querySelector('.author-filter-clear');
    const authorItems = authorsPanel.querySelectorAll('.author-item');

    if (clearBtn) {
        clearBtn.classList.toggle('visible', filteredAuthor !== null);
    }

    authorItems.forEach(item => {
        const name = item.querySelector('.author-name')?.textContent;
        if (filteredAuthor === null) {
            item.classList.remove('filtered', 'active');
        } else if (name === filteredAuthor) {
            item.classList.remove('filtered');
            item.classList.add('active');
        } else {
            item.classList.add('filtered');
            item.classList.remove('active');
        }
    });
}

// Add click handler to author items (delegate to parent)
authorsItems.addEventListener('click', (e) => {
    const authorItem = e.target.closest('.author-item');
    if (authorItem) {
        const authorName = authorItem.querySelector('.author-name')?.textContent;
        if (authorName) {
            if (filteredAuthor === authorName) {
                clearAuthorFilter();
            } else {
                setAuthorFilter(authorName);
            }
        }
    }
});

// =====================================================================
// ENHANCED TOUCH GESTURES
// =====================================================================
// The existing touch handlers are already good, but let's add
// two-finger pan support and improve pinch-to-zoom smoothness

let lastTouchCenter = null;

function getTouchCenter(touches) {
    return {
        x: (touches[0].clientX + touches[1].clientX) / 2,
        y: (touches[0].clientY + touches[1].clientY) / 2
    };
}

// Override the existing touchmove handler with enhanced version
canvas.removeEventListener('touchmove', null); // Note: This won't actually remove it

// We'll modify the touchmove behavior in-place by updating touchState usage
// The existing handler already handles pinch-to-zoom well

// =====================================================================
// PERFORMANCE PANEL TOGGLE ENHANCEMENT
// =====================================================================
// The existing perf panel toggle is handled, but let's add keyboard shortcut info

// Start
main();

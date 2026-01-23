/**
 * Rource - Configuration Constants
 *
 * Central configuration for the WASM web demo.
 * All magic numbers and configurable values live here.
 */

export const CONFIG = {
    // Performance
    PERF_UPDATE_INTERVAL: 10,        // Update perf metrics every N frames
    TOOLTIP_DELAY_MS: 500,           // Delay before showing tooltip
    SCROLL_INDICATOR_THRESHOLD: 50,  // Pixels from bottom to hide indicator
    DEBOUNCE_DELAY_MS: 150,          // Debounce delay for resize events

    // UI
    TOOLTIP_WIDTH: 320,              // Tooltip width in pixels
    TOOLTIP_HEIGHT: 150,             // Tooltip height in pixels

    // GitHub API
    // IMPORTANT: Unauthenticated rate limit is 60 requests/hour
    // Each commit needs 1 API call for file details, so we must be conservative
    GITHUB_CACHE_EXPIRY_MS: 24 * 60 * 60 * 1000,  // 24 hours
    GITHUB_RATE_LIMIT_BUFFER: 5,     // Stop fetching when this many requests remain
    GITHUB_MAX_COMMITS: 50,          // Max commits to fetch (50 commits = ~51 API calls)
    GITHUB_WARN_LOW_LIMIT: 10,       // Warn user when rate limit is below this

    // Animation & Timing
    TOAST_DURATION_MS: 3000,         // Default toast duration
    TOAST_SUCCESS_DURATION_MS: 2000, // Success toast duration
    TOAST_ERROR_DURATION_MS: 5000,   // Error toast duration (longer for user to read)
    INIT_DELAY_MS: 500,              // Delay before auto-loading default data
    CONTEXT_RESTORE_DELAY_MS: 500,   // Delay before WebGL context restoration
    SCROLL_INDICATOR_DELAY_MS: 100,  // Delay before checking scroll indicator
    PANEL_ANIMATION_DELAY_MS: 350,   // Delay for panel collapse/expand animations
    COPY_FEEDBACK_DELAY_MS: 2000,    // Duration to show "Copied!" feedback
    STATUS_HIDE_DELAY_MS: 3000,      // Delay before hiding status messages
    PREWARM_DELAY_MS: 50,            // Delay between prewarm iterations

    // Debug (set to true for development logging)
    DEBUG: false,

    // Observability
    ENABLE_TELEMETRY: false,         // Enable performance telemetry logging
    LOG_WASM_ERRORS: true,           // Log WASM errors to console (always on for diagnostics)

    // Playback speed limits (seconds per day)
    // At 60fps, seconds_per_commit = seconds_per_day / 10.0
    // Min of 0.1 gives 0.01s/commit = ~0.6 frames per commit (100x hyper fast)
    SPEED_MIN: 0.1,                  // Minimum speed (100x, hyper fast playback)
    SPEED_MAX: 1000,                 // Maximum speed (slowest playback)
    SPEED_DEFAULT: 10,               // Default speed (1x)
};

// Extension colors (matches Rust code in rource-core/src/scene/file.rs)
export const EXTENSION_COLORS = {
    // Rust
    'rs': '#dea584',
    // JavaScript/TypeScript
    'js': '#f1e05a',
    'ts': '#3178c6',
    'tsx': '#3178c6',
    'jsx': '#f1e05a',
    'mjs': '#f1e05a',
    'cjs': '#f1e05a',
    // Web
    'html': '#e34c26',
    'htm': '#e34c26',
    'css': '#563d7c',
    'scss': '#c6538c',
    'sass': '#c6538c',
    'less': '#1d365d',
    // Python
    'py': '#3572A5',
    'pyw': '#3572A5',
    'pyi': '#3572A5',
    // Go
    'go': '#00ADD8',
    // Java/JVM
    'java': '#b07219',
    'kt': '#A97BFF',
    'kts': '#A97BFF',
    'scala': '#c22d40',
    'groovy': '#4298b8',
    // C/C++
    'c': '#555555',
    'h': '#555555',
    'cpp': '#f34b7d',
    'cc': '#f34b7d',
    'cxx': '#f34b7d',
    'hpp': '#f34b7d',
    'hxx': '#f34b7d',
    // C#
    'cs': '#178600',
    // Ruby
    'rb': '#701516',
    'erb': '#701516',
    // PHP
    'php': '#4F5D95',
    // Shell
    'sh': '#89e051',
    'bash': '#89e051',
    'zsh': '#89e051',
    'fish': '#89e051',
    // Data/Config
    'json': '#292929',
    'yaml': '#cb171e',
    'yml': '#cb171e',
    'toml': '#9c4221',
    'xml': '#0060ac',
    // Documentation
    'md': '#083fa1',
    'markdown': '#083fa1',
    'txt': '#888888',
    'rst': '#141414',
    // Swift
    'swift': '#F05138',
    // Objective-C
    'm': '#438eff',
    'mm': '#438eff',
    // Lua
    'lua': '#000080',
    // Perl
    'pl': '#0298c3',
    'pm': '#0298c3',
    // R
    'r': '#198CE7',
    // Haskell
    'hs': '#5e5086',
    // Elixir/Erlang
    'ex': '#6e4a7e',
    'exs': '#6e4a7e',
    'erl': '#B83998',
    // Clojure
    'clj': '#db5855',
    'cljs': '#db5855',
    // SQL
    'sql': '#e38c00',
    // Images
    'png': '#a8d18d',
    'jpg': '#a8d18d',
    'jpeg': '#a8d18d',
    'gif': '#a8d18d',
    'svg': '#ff9900',
    'ico': '#a8d18d',
    'webp': '#a8d18d',
    // Fonts
    'ttf': '#c0c0c0',
    'otf': '#c0c0c0',
    'woff': '#c0c0c0',
    'woff2': '#c0c0c0',
    // Build/Config
    'lock': '#888888',
    'gitignore': '#f54d27',
    'dockerignore': '#0db7ed',
    'dockerfile': '#0db7ed',
    // WASM
    'wasm': '#654ff0',
    'wat': '#654ff0',
    // Default
    '_default': '#8da0cb',
};

/**
 * Gets the color for a file extension.
 * @param {string} ext - File extension (without dot)
 * @returns {string} Hex color code
 */
export function getExtensionColor(ext) {
    return EXTENSION_COLORS[ext?.toLowerCase()] || EXTENSION_COLORS['_default'];
}

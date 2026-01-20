/**
 * Rource - DOM Element References
 *
 * Centralized access to all DOM elements used by the application.
 * Elements are lazily initialized to ensure the DOM is ready.
 */

// Cache for DOM elements
let elementsInitialized = false;
const elements = {};

/**
 * Initializes all DOM element references.
 * Call this after DOMContentLoaded.
 */
export function initDomElements() {
    if (elementsInitialized) return;

    // Canvas and core visualization
    elements.canvas = document.getElementById('canvas');
    elements.loadingEl = document.getElementById('loading');
    elements.emptyState = document.getElementById('empty-state');

    // Playback controls
    elements.btnPlayMain = document.getElementById('btn-play-main');
    elements.playIconMain = document.getElementById('play-icon-main');
    elements.btnPrev = document.getElementById('btn-prev');
    elements.btnNext = document.getElementById('btn-next');
    elements.btnResetBar = document.getElementById('btn-reset-bar');

    // Labels toggle
    elements.btnLabels = document.getElementById('btn-labels');
    elements.labelsText = document.getElementById('labels-text');

    // Screenshot
    elements.btnScreenshot = document.getElementById('btn-screenshot');

    // WebGL context loss
    elements.contextLostOverlay = document.getElementById('context-lost-overlay');
    elements.btnRestoreContext = document.getElementById('btn-restore-context');

    // Data loading
    elements.btnLoad = document.getElementById('btn-load');
    elements.btnLoadFile = document.getElementById('btn-load-file');
    elements.btnCopyCommand = document.getElementById('btn-copy-command');
    elements.logInput = document.getElementById('log-input');
    elements.fileInput = document.getElementById('file-input');
    elements.fileDropZone = document.getElementById('file-drop-zone');
    elements.fileNameEl = document.getElementById('file-name');

    // GitHub fetch
    elements.btnFetchGithub = document.getElementById('btn-fetch-github');
    elements.githubUrlInput = document.getElementById('github-url');
    elements.fetchStatus = document.getElementById('fetch-status');
    elements.fetchStatusText = document.getElementById('fetch-status-text');
    elements.fetchProgressBar = document.getElementById('fetch-progress-bar');

    // Timeline
    elements.timelineSlider = document.getElementById('timeline-slider');
    elements.timelineInfo = document.getElementById('timeline-info');
    elements.timelineMarkers = document.getElementById('timeline-markers');
    elements.speedSelect = document.getElementById('speed-select');

    // Renderer info
    elements.rendererBadge = document.getElementById('renderer-badge');
    elements.techRenderer = document.getElementById('tech-renderer');

    // Stats overlay
    elements.statsOverlay = document.getElementById('stats-overlay');
    elements.statCommits = document.getElementById('stat-commits');
    elements.statFiles = document.getElementById('stat-files');
    elements.statAuthors = document.getElementById('stat-authors');

    // Toast notification
    elements.toast = document.getElementById('toast');

    // Performance metrics overlay
    elements.perfOverlay = document.getElementById('perf-overlay');
    elements.perfToggle = document.getElementById('perf-toggle');
    elements.perfFps = document.getElementById('perf-fps');
    elements.perfFrameTime = document.getElementById('perf-frame-time');
    elements.perfEntities = document.getElementById('perf-entities');
    elements.perfVisible = document.getElementById('perf-visible');
    elements.perfDraws = document.getElementById('perf-draws');
    elements.perfResolution = document.getElementById('perf-resolution');

    // Showcase panel (Rource repo)
    elements.btnVisualizeRource = document.getElementById('btn-visualize-rource');
    elements.btnRefreshRource = document.getElementById('btn-refresh-rource');
    elements.refreshStatus = document.getElementById('refresh-status');
    elements.showcaseCommits = document.getElementById('showcase-commits');
    elements.showcaseFiles = document.getElementById('showcase-files');
    elements.showcaseAuthors = document.getElementById('showcase-authors');

    // Authors legend
    elements.authorsPanel = document.getElementById('authors-panel');
    elements.authorsItems = document.getElementById('authors-items');
    elements.authorsToggle = document.getElementById('authors-toggle');

    // Legend panel
    elements.legendPanel = document.getElementById('legend-panel');
    elements.legendToggle = document.getElementById('legend-toggle');
    elements.legendItems = document.getElementById('legend-items');

    // Theme toggle
    elements.themeToggle = document.getElementById('btn-theme');

    // Help overlay
    elements.helpBtn = document.getElementById('btn-help');
    elements.helpOverlay = document.getElementById('help-overlay');
    elements.helpClose = document.getElementById('help-close');
    elements.helpGotIt = document.getElementById('help-got-it');

    // Sidebar
    elements.sidebarPanel = document.getElementById('sidebar-panel');
    elements.sidebarToggle = document.getElementById('sidebar-toggle');
    elements.sidebarClose = document.getElementById('sidebar-close');
    elements.sidebarOverlay = document.getElementById('sidebar-overlay');

    // Commit tooltip
    elements.commitTooltip = document.getElementById('commit-tooltip');
    elements.tooltipAuthorColor = document.getElementById('tooltip-author-color');
    elements.tooltipAuthor = document.getElementById('tooltip-author');
    elements.tooltipDate = document.getElementById('tooltip-date');
    elements.tooltipFile = document.getElementById('tooltip-file');
    elements.tooltipAction = document.getElementById('tooltip-action');

    // Fullscreen
    elements.btnFullscreen = document.getElementById('btn-fullscreen');
    elements.fullscreenIcon = document.getElementById('fullscreen-icon');
    elements.canvasContainer = document.getElementById('canvas-container');

    // Share
    elements.btnShare = document.getElementById('btn-share');

    // Mobile fullscreen exit
    elements.mobileFullscreenExit = document.getElementById('mobile-fullscreen-exit');

    elementsInitialized = true;
}

/**
 * Gets a DOM element by key.
 * @param {string} key - Element key
 * @returns {HTMLElement|null} DOM element or null
 */
export function getElement(key) {
    if (!elementsInitialized) {
        initDomElements();
    }
    return elements[key] || null;
}

/**
 * Gets all DOM elements.
 * @returns {Object} All DOM elements
 */
export function getAllElements() {
    if (!elementsInitialized) {
        initDomElements();
    }
    return elements;
}

// Export individual getters for commonly used elements
export const getCanvas = () => getElement('canvas');
export const getToast = () => getElement('toast');
export const getLoadingEl = () => getElement('loadingEl');

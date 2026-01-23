/**
 * Rource - GitHub Repository Fetching
 *
 * Fetches commit history from public GitHub repositories using the GitHub API.
 * Converts commit data into the Rource custom log format for visualization.
 *
 * IMPORTANT: GitHub's unauthenticated API rate limit is 60 requests/hour.
 * This module is designed to work within that constraint by:
 * 1. Limiting the number of commits fetched (default: 50)
 * 2. Tracking and respecting rate limits before making requests
 * 3. Caching results to avoid repeated API calls
 *
 * Production-grade features:
 * - Request timeouts with AbortController
 * - Automatic retry with exponential backoff for transient failures
 * - Concurrent request prevention (fetch lock)
 * - Input validation and sanitization
 * - Bounded cache with LRU eviction
 * - Comprehensive error handling
 * - Observable via debugLog with correlation IDs
 */

import { CONFIG } from './config.js';
import { showToast } from './toast.js';
import { debugLog } from './telemetry.js';

// ============================================================================
// Constants
// ============================================================================

const REQUEST_TIMEOUT_MS = 30000;  // 30 second timeout per request
const MAX_RETRIES = 2;             // Retry transient failures twice
const RETRY_BASE_DELAY_MS = 1000;  // 1 second initial retry delay
const MAX_CACHE_ENTRIES = 20;      // Maximum cached repositories
const GITHUB_OWNER_REPO_REGEX = /^[a-zA-Z0-9](?:[a-zA-Z0-9._-]*[a-zA-Z0-9])?$/;

// ============================================================================
// State
// ============================================================================

// Cache for fetched repository data (bounded LRU-style)
const repoCache = new Map();

// Rate limit tracking (persists across fetches)
let rateLimitState = {
    remaining: 60,  // Conservative default
    reset: 0,       // Unix timestamp when limit resets
    limit: 60,      // Total limit
    lastChecked: 0, // When we last checked
};

// Fetch lock to prevent concurrent requests
let fetchInProgress = false;
let currentAbortController = null;

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Generates a unique correlation ID for request tracing.
 * @returns {string} Short correlation ID
 */
function generateCorrelationId() {
    return Math.random().toString(36).substring(2, 8);
}

/**
 * Creates an AbortController with timeout.
 * @param {number} timeoutMs - Timeout in milliseconds
 * @returns {AbortController} Controller that will abort after timeout
 */
function createTimeoutController(timeoutMs) {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => {
        controller.abort(new Error(`Request timed out after ${timeoutMs}ms`));
    }, timeoutMs);

    // Store timeout ID for cleanup
    controller._timeoutId = timeoutId;
    return controller;
}

/**
 * Cleans up an AbortController's timeout.
 * @param {AbortController} controller - Controller to clean up
 */
function cleanupController(controller) {
    if (controller && controller._timeoutId) {
        clearTimeout(controller._timeoutId);
    }
}

/**
 * Sleeps for specified milliseconds.
 * @param {number} ms - Milliseconds to sleep
 * @returns {Promise<void>}
 */
function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

/**
 * Determines if an error is retryable (transient).
 * @param {Error} error - The error to check
 * @param {number} status - HTTP status code (0 if network error)
 * @returns {boolean} True if the request should be retried
 */
function isRetryableError(error, status) {
    // Network errors (fetch failed)
    if (status === 0) return true;

    // Server errors (5xx) are typically transient
    if (status >= 500 && status < 600) return true;

    // 429 Too Many Requests (but not 403 rate limit)
    if (status === 429) return true;

    // Timeout errors
    if (error && error.message && error.message.includes('timed out')) return true;

    return false;
}

// ============================================================================
// Rate Limit Management
// ============================================================================

/**
 * Updates rate limit state from response headers.
 * Exported so other modules can update rate limit after GitHub API calls.
 * @param {Response} response - Fetch response
 */
export function updateRateLimitFromResponse(response) {
    const remaining = response.headers.get('X-RateLimit-Remaining');
    const reset = response.headers.get('X-RateLimit-Reset');
    const limit = response.headers.get('X-RateLimit-Limit');

    if (remaining !== null) {
        rateLimitState.remaining = parseInt(remaining, 10);
    }
    if (reset !== null) {
        rateLimitState.reset = parseInt(reset, 10);
    }
    if (limit !== null) {
        rateLimitState.limit = parseInt(limit, 10);
    }
    rateLimitState.lastChecked = Date.now();

    debugLog('github', `Rate limit: ${rateLimitState.remaining}/${rateLimitState.limit}, resets at ${new Date(rateLimitState.reset * 1000).toLocaleTimeString()}`);
}

/**
 * Gets the current rate limit status.
 * @returns {Object} Rate limit info
 */
export function getRateLimitStatus() {
    const now = Math.floor(Date.now() / 1000);

    // If the reset time has passed, assume quota is restored
    if (rateLimitState.reset > 0 && rateLimitState.reset <= now) {
        rateLimitState.remaining = rateLimitState.limit;
        rateLimitState.reset = 0;
    }

    const resetTime = rateLimitState.reset > now
        ? new Date(rateLimitState.reset * 1000)
        : null;

    return {
        remaining: rateLimitState.remaining,
        limit: rateLimitState.limit,
        resetTime,
        isLow: rateLimitState.remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER,
        isExhausted: rateLimitState.remaining === 0 && (rateLimitState.reset > now),
    };
}

/**
 * Checks if we have enough rate limit budget for an operation.
 * @param {number} requestsNeeded - Number of API requests needed
 * @returns {Object} { canProceed, message }
 */
function checkRateLimitBudget(requestsNeeded) {
    const status = getRateLimitStatus();

    if (status.isExhausted) {
        return {
            canProceed: false,
            message: `GitHub API rate limit exhausted. Try again after ${status.resetTime?.toLocaleTimeString() || 'some time'}.`,
        };
    }

    if (status.remaining < requestsNeeded) {
        return {
            canProceed: false,
            message: `Not enough API requests remaining (${status.remaining} available, ~${requestsNeeded} needed). ` +
                `Rate limit resets at ${status.resetTime?.toLocaleTimeString() || 'soon'}.`,
        };
    }

    return { canProceed: true, message: null };
}

// ============================================================================
// Input Validation
// ============================================================================

/**
 * Validates a GitHub owner or repo name.
 * @param {string} name - The name to validate
 * @returns {boolean} True if valid
 */
function isValidGitHubName(name) {
    if (!name || typeof name !== 'string') return false;
    if (name.length < 1 || name.length > 100) return false;
    return GITHUB_OWNER_REPO_REGEX.test(name);
}

/**
 * Parses a GitHub URL to extract owner and repo.
 * Supports formats:
 * - https://github.com/owner/repo
 * - https://github.com/owner/repo.git
 * - github.com/owner/repo
 * - owner/repo
 *
 * @param {string} input - GitHub URL or owner/repo string
 * @returns {Object|null} { owner, repo } or null if invalid
 */
export function parseGitHubUrl(input) {
    if (!input || typeof input !== 'string') return null;

    const trimmed = input.trim();

    // Try full URL format
    const urlMatch = trimmed.match(
        /^(?:https?:\/\/)?(?:www\.)?github\.com\/([^/]+)\/([^/.]+)(?:\.git)?(?:\/.*)?$/i
    );
    if (urlMatch) {
        const owner = urlMatch[1];
        const repo = urlMatch[2];
        if (isValidGitHubName(owner) && isValidGitHubName(repo)) {
            return { owner, repo };
        }
        return null;
    }

    // Try owner/repo format
    const shortMatch = trimmed.match(/^([^/]+)\/([^/]+)$/);
    if (shortMatch && !trimmed.includes('.')) {
        const owner = shortMatch[1];
        const repo = shortMatch[2];
        if (isValidGitHubName(owner) && isValidGitHubName(repo)) {
            return { owner, repo };
        }
    }

    return null;
}

// ============================================================================
// Cache Management
// ============================================================================

/**
 * Checks the cache for a repository's data.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @returns {string|null} Cached log data or null if not cached/expired
 */
function getCachedData(owner, repo) {
    const key = `${owner}/${repo}`;
    const cached = repoCache.get(key);

    if (cached) {
        const age = Date.now() - cached.timestamp;
        if (age < CONFIG.GITHUB_CACHE_EXPIRY_MS) {
            // Move to end for LRU behavior (delete and re-add)
            repoCache.delete(key);
            repoCache.set(key, cached);
            debugLog('github', `Cache hit for ${key}, age: ${Math.round(age / 1000)}s`);
            return cached.data;
        }
        repoCache.delete(key);
    }

    return null;
}

/**
 * Stores repository data in cache with LRU eviction.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {string} data - Log data to cache
 */
function setCachedData(owner, repo, data) {
    const key = `${owner}/${repo}`;

    // Remove oldest entries if at capacity (LRU eviction)
    while (repoCache.size >= MAX_CACHE_ENTRIES) {
        const oldestKey = repoCache.keys().next().value;
        repoCache.delete(oldestKey);
        debugLog('github', `Cache evicted: ${oldestKey}`);
    }

    repoCache.set(key, {
        data,
        timestamp: Date.now(),
    });
}

// ============================================================================
// HTTP Fetch with Retry
// ============================================================================

/**
 * Performs a fetch request with timeout, retry, and rate limit tracking.
 * @param {string} url - URL to fetch
 * @param {Object} options - Fetch options
 * @param {string} correlationId - Correlation ID for logging
 * @returns {Promise<Response>} Fetch response
 */
async function fetchWithRetry(url, options = {}, correlationId = '') {
    let lastError = null;
    let lastStatus = 0;

    for (let attempt = 0; attempt <= MAX_RETRIES; attempt++) {
        const controller = createTimeoutController(REQUEST_TIMEOUT_MS);

        // Store controller for potential cancellation
        currentAbortController = controller;

        try {
            const fetchOptions = {
                ...options,
                signal: controller.signal,
                headers: {
                    Accept: 'application/vnd.github.v3+json',
                    ...options.headers,
                },
            };

            const startTime = performance.now();
            const response = await fetch(url, fetchOptions);
            const duration = Math.round(performance.now() - startTime);

            cleanupController(controller);

            // Update rate limit from every response
            updateRateLimitFromResponse(response);

            debugLog('github', `[${correlationId}] ${url} - ${response.status} (${duration}ms, attempt ${attempt + 1})`);

            // Return successful responses and non-retryable errors
            if (response.ok || !isRetryableError(null, response.status)) {
                return response;
            }

            // Retryable error - store for potential retry
            lastStatus = response.status;
            lastError = new Error(`HTTP ${response.status}: ${response.statusText}`);

        } catch (error) {
            cleanupController(controller);
            lastError = error;
            lastStatus = 0;

            // Don't retry if aborted intentionally
            if (error.name === 'AbortError' && !error.message.includes('timed out')) {
                throw error;
            }

            debugLog('github', `[${correlationId}] ${url} - Error: ${error.message} (attempt ${attempt + 1})`);

            if (!isRetryableError(error, 0)) {
                throw error;
            }
        } finally {
            currentAbortController = null;
        }

        // Exponential backoff before retry
        if (attempt < MAX_RETRIES) {
            const delay = RETRY_BASE_DELAY_MS * Math.pow(2, attempt);
            debugLog('github', `[${correlationId}] Retrying in ${delay}ms...`);
            await sleep(delay);
        }
    }

    // All retries exhausted
    throw lastError || new Error(`Request failed after ${MAX_RETRIES + 1} attempts`);
}

// ============================================================================
// GitHub API Methods
// ============================================================================

/**
 * Fetches a single page of commits from the GitHub API.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {number} perPage - Items per page (max 100)
 * @param {string} correlationId - Correlation ID for logging
 * @returns {Promise<Object>} { commits, hasMore }
 */
async function fetchCommitPage(owner, repo, perPage, correlationId) {
    const url = `https://api.github.com/repos/${encodeURIComponent(owner)}/${encodeURIComponent(repo)}/commits?per_page=${perPage}`;

    const response = await fetchWithRetry(url, {}, correlationId);

    if (response.status === 403 && rateLimitState.remaining === 0) {
        const resetTime = new Date(rateLimitState.reset * 1000);
        throw new Error(
            `GitHub API rate limit exceeded. Try again after ${resetTime.toLocaleTimeString()}.`
        );
    }

    if (response.status === 404) {
        throw new Error('Repository not found. Check the URL and ensure it\'s a public repository.');
    }

    if (!response.ok) {
        throw new Error(`GitHub API error: ${response.status} ${response.statusText}`);
    }

    const commits = await response.json();

    // Validate response is an array
    if (!Array.isArray(commits)) {
        throw new Error('Invalid response from GitHub API');
    }

    const hasMore = commits.length === perPage;

    return { commits, hasMore };
}

/**
 * Fetches file changes for a specific commit.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {string} sha - Commit SHA
 * @param {string} correlationId - Correlation ID for logging
 * @returns {Promise<Array>} Array of file changes { filename, status }
 */
async function fetchCommitFiles(owner, repo, sha, correlationId) {
    // Check rate limit before making the request
    if (rateLimitState.remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER) {
        debugLog('github', `[${correlationId}] Skipping commit ${sha.substring(0, 7)} due to low rate limit`);
        return [];
    }

    const url = `https://api.github.com/repos/${encodeURIComponent(owner)}/${encodeURIComponent(repo)}/commits/${encodeURIComponent(sha)}`;

    try {
        const response = await fetchWithRetry(url, {}, correlationId);

        if (response.status === 403 && rateLimitState.remaining === 0) {
            debugLog('github', `[${correlationId}] Rate limit hit during commit file fetch`);
            return [];
        }

        if (!response.ok) {
            debugLog('github', `[${correlationId}] Failed to fetch files for ${sha.substring(0, 7)}: ${response.status}`);
            return [];
        }

        const data = await response.json();
        return Array.isArray(data.files) ? data.files : [];

    } catch (error) {
        // Non-fatal - return empty array on error
        debugLog('github', `[${correlationId}] Error fetching files for ${sha.substring(0, 7)}: ${error.message}`);
        return [];
    }
}

/**
 * Converts a GitHub commit to Rource log format lines.
 * @param {Object} commit - GitHub commit object
 * @param {Array} files - Array of file changes
 * @returns {Array<string>} Array of log lines
 */
function commitToLogLines(commit, files) {
    const lines = [];

    // Safely extract timestamp
    const dateStr = commit?.commit?.author?.date;
    if (!dateStr) return lines;

    const timestamp = Math.floor(new Date(dateStr).getTime() / 1000);
    if (isNaN(timestamp)) return lines;

    // Safely extract author
    const author = (commit.commit?.author?.name || commit.author?.login || 'Unknown')
        .replace(/\|/g, '_');  // Sanitize pipe characters

    for (const file of files) {
        if (!file.filename) continue;

        // Map GitHub status to Rource action
        let action = 'M'; // default to modify
        if (file.status === 'added') action = 'A';
        else if (file.status === 'removed') action = 'D';
        else if (file.status === 'renamed') action = 'M';
        else if (file.status === 'modified') action = 'M';

        // Sanitize filename (remove pipes, ensure no path traversal)
        const filename = file.filename.replace(/\|/g, '_');

        lines.push(`${timestamp}|${author}|${action}|${filename}`);
    }

    return lines;
}

// ============================================================================
// Main Fetch Function
// ============================================================================

/**
 * Fetches commit history from a GitHub repository.
 *
 * RATE LIMIT AWARE: This function carefully manages API calls to stay within
 * GitHub's unauthenticated rate limit (60 requests/hour).
 *
 * API calls needed: 1 (commit list) + N (file details for each commit)
 * For 50 commits = ~51 API calls (leaves buffer for other operations)
 *
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {Object} options - Options
 * @param {number} options.maxCommits - Maximum commits to fetch (default: 50, max: 100)
 * @param {Function} options.onProgress - Progress callback (phase, current, total, message)
 * @param {AbortSignal} options.signal - Optional AbortSignal for cancellation
 * @returns {Promise<string>} Log data in Rource custom format
 */
export async function fetchGitHubCommits(owner, repo, options = {}) {
    const correlationId = generateCorrelationId();
    const startTime = performance.now();

    // Validate inputs
    if (!isValidGitHubName(owner) || !isValidGitHubName(repo)) {
        throw new Error('Invalid repository owner or name');
    }

    // Prevent concurrent fetches
    if (fetchInProgress) {
        throw new Error('A fetch is already in progress. Please wait.');
    }

    fetchInProgress = true;

    try {
        // IMPORTANT: Keep maxCommits low to avoid rate limit exhaustion
        const { maxCommits = 50, onProgress = null } = options;

        // Clamp to reasonable maximum
        const effectiveMax = Math.min(Math.max(1, maxCommits), 100);

        // Check cache first
        const cached = getCachedData(owner, repo);
        if (cached) {
            debugLog('github', `[${correlationId}] Cache hit for ${owner}/${repo}`);
            return cached;
        }

        // Calculate API budget needed
        const estimatedCalls = 1 + effectiveMax;

        // Check rate limit budget BEFORE starting
        const budgetCheck = checkRateLimitBudget(estimatedCalls);
        if (!budgetCheck.canProceed) {
            throw new Error(budgetCheck.message);
        }

        debugLog('github', `[${correlationId}] Fetching ${owner}/${repo} (max ${effectiveMax} commits, ~${estimatedCalls} API calls)`);

        if (onProgress) {
            onProgress('init', 0, effectiveMax, 'Checking repository...');
        }

        // Fetch commits list
        const { commits } = await fetchCommitPage(owner, repo, effectiveMax, correlationId);

        if (commits.length === 0) {
            throw new Error('No commits found in this repository.');
        }

        debugLog('github', `[${correlationId}] Found ${commits.length} commits, rate limit: ${rateLimitState.remaining}`);

        if (onProgress) {
            onProgress('commits', commits.length, commits.length, `Found ${commits.length} commits`);
        }

        // Fetch file details for each commit
        const logLines = [];
        let processed = 0;
        let skippedDueToRateLimit = 0;

        for (const commit of commits) {
            // Check rate limit before each request
            if (rateLimitState.remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER) {
                debugLog('github', `[${correlationId}] Stopping early: rate limit low (${rateLimitState.remaining})`);
                skippedDueToRateLimit = commits.length - processed;
                break;
            }

            const files = await fetchCommitFiles(owner, repo, commit.sha, correlationId);
            const lines = commitToLogLines(commit, files);
            logLines.push(...lines);

            processed++;

            if (onProgress) {
                onProgress('files', processed, commits.length, `Fetching file details... ${processed}/${commits.length}`);
            }

            // Small delay between requests to be nice to the API
            if (processed % 10 === 0 && processed < commits.length) {
                await sleep(50);
            }
        }

        if (skippedDueToRateLimit > 0) {
            debugLog('github', `[${correlationId}] Skipped ${skippedDueToRateLimit} commits due to rate limit`);
        }

        if (logLines.length === 0) {
            throw new Error('No file changes found. The repository may be empty or rate limit was exceeded.');
        }

        // Sort by timestamp (oldest first for visualization)
        logLines.sort((a, b) => {
            const tsA = parseInt(a.split('|')[0], 10);
            const tsB = parseInt(b.split('|')[0], 10);
            return tsA - tsB;
        });

        const logData = logLines.join('\n');

        // Cache the result
        setCachedData(owner, repo, logData);

        const duration = Math.round(performance.now() - startTime);
        debugLog('github', `[${correlationId}] Complete: ${logLines.length} lines, ${processed} commits, ${duration}ms, rate limit: ${rateLimitState.remaining}`);

        return logData;

    } finally {
        fetchInProgress = false;
    }
}

/**
 * Fetches a GitHub repository with progress UI updates.
 *
 * @param {string} input - GitHub URL or owner/repo
 * @param {Object} elements - DOM elements { statusEl, progressEl }
 * @returns {Promise<string|null>} Log data or null on failure
 */
export async function fetchGitHubWithProgress(input, elements = {}) {
    const parsed = parseGitHubUrl(input);

    if (!parsed) {
        showToast('Invalid GitHub URL. Use format: github.com/owner/repo', 'error');
        return null;
    }

    const { owner, repo } = parsed;

    // Check rate limit status before starting
    const status = getRateLimitStatus();
    if (status.isExhausted) {
        const msg = `GitHub API rate limit exhausted. Try again after ${status.resetTime?.toLocaleTimeString() || 'some time'}.`;
        showToast(msg, 'error', 8000);
        if (elements.statusEl) {
            elements.statusEl.textContent = msg;
        }
        return null;
    }

    if (status.remaining < 10) {
        showToast(`Low API quota (${status.remaining} requests left). Fetching may be incomplete.`, 'warning', 5000);
    }

    if (elements.statusEl) {
        elements.statusEl.textContent = `Checking ${owner}/${repo}...`;
    }

    try {
        const logData = await fetchGitHubCommits(owner, repo, {
            maxCommits: 50,
            onProgress: (phase, current, total, message) => {
                if (elements.statusEl) {
                    elements.statusEl.textContent = message;
                }
            },
        });

        if (!logData || logData.trim().length === 0) {
            showToast('No commits found in this repository.', 'error');
            return null;
        }

        const afterStatus = getRateLimitStatus();
        debugLog('github', `Fetch complete. Rate limit: ${afterStatus.remaining}/${afterStatus.limit}`);

        return logData;

    } catch (e) {
        let message = e.message || 'Failed to fetch repository';

        // Categorize and display appropriate error
        if (message.includes('rate limit')) {
            showToast(message, 'error', 8000);
        } else if (message.includes('not found')) {
            showToast(message, 'error');
        } else if (message.includes('No commits') || message.includes('No file changes')) {
            showToast(message, 'error');
        } else if (message.includes('already in progress')) {
            showToast(message, 'warning');
        } else if (message.includes('timed out')) {
            showToast('Request timed out. GitHub may be slow or unreachable.', 'error');
        } else if (message.includes('NetworkError') || message.includes('Failed to fetch')) {
            showToast('Network error. Please check your internet connection.', 'error');
        } else {
            showToast(`Error: ${message}`, 'error');
        }

        if (elements.statusEl) {
            elements.statusEl.textContent = message;
        }

        debugLog('github', `Fetch error: ${message}`);
        return null;
    }
}

// ============================================================================
// Cache Management Exports
// ============================================================================

/**
 * Clears the repository cache.
 */
export function clearCache() {
    repoCache.clear();
    debugLog('github', 'Cache cleared');
}

/**
 * Cancels any in-progress fetch operation.
 */
export function cancelFetch() {
    if (currentAbortController) {
        currentAbortController.abort();
        debugLog('github', 'Fetch cancelled');
    }
}

/**
 * Checks if a fetch is currently in progress.
 * @returns {boolean} True if fetching
 */
export function isFetching() {
    return fetchInProgress;
}

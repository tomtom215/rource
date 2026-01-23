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
 * 3. Using commit list endpoints that include file stats when possible
 */

import { CONFIG } from './config.js';
import { showToast } from './toast.js';
import { debugLog } from './telemetry.js';

// Cache for fetched repository data
const repoCache = new Map();

// Rate limit tracking (persists across fetches)
let rateLimitState = {
    remaining: 60,  // Conservative default
    reset: 0,       // Unix timestamp when limit resets
    limit: 60,      // Total limit
    lastChecked: 0, // When we last checked
};

/**
 * Updates rate limit state from response headers.
 * @param {Response} response - Fetch response
 */
function updateRateLimitFromResponse(response) {
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
        return { owner: urlMatch[1], repo: urlMatch[2] };
    }

    // Try owner/repo format
    const shortMatch = trimmed.match(/^([^/]+)\/([^/]+)$/);
    if (shortMatch && !trimmed.includes('.')) {
        return { owner: shortMatch[1], repo: shortMatch[2] };
    }

    return null;
}

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
            debugLog('github', `Cache hit for ${key}, age: ${Math.round(age / 1000)}s`);
            return cached.data;
        }
        repoCache.delete(key);
    }

    return null;
}

/**
 * Stores repository data in cache.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {string} data - Log data to cache
 */
function setCachedData(owner, repo, data) {
    const key = `${owner}/${repo}`;
    repoCache.set(key, {
        data,
        timestamp: Date.now(),
    });
}

/**
 * Fetches a single page of commits from the GitHub API.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {number} page - Page number (1-indexed)
 * @param {number} perPage - Items per page (max 100)
 * @returns {Promise<Object>} { commits, hasMore }
 */
async function fetchCommitPage(owner, repo, page, perPage = 100) {
    const url = `https://api.github.com/repos/${owner}/${repo}/commits?page=${page}&per_page=${perPage}`;

    const response = await fetch(url, {
        headers: {
            Accept: 'application/vnd.github.v3+json',
            // No auth token - public API only
        },
    });

    // Always update rate limit tracking
    updateRateLimitFromResponse(response);

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

    // Check if there are more pages (GitHub returns empty array at the end)
    const hasMore = commits.length === perPage;

    return { commits, hasMore };
}

/**
 * Fetches file changes for a specific commit.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {string} sha - Commit SHA
 * @returns {Promise<Array>} Array of file changes { filename, status }
 */
async function fetchCommitFiles(owner, repo, sha) {
    // Check rate limit before making the request
    if (rateLimitState.remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER) {
        debugLog('github', `Skipping commit ${sha} due to low rate limit (${rateLimitState.remaining} remaining)`);
        return [];
    }

    const url = `https://api.github.com/repos/${owner}/${repo}/commits/${sha}`;

    const response = await fetch(url, {
        headers: {
            Accept: 'application/vnd.github.v3+json',
        },
    });

    // Always update rate limit tracking
    updateRateLimitFromResponse(response);

    if (response.status === 403 && rateLimitState.remaining === 0) {
        // Rate limit hit during fetch - stop gracefully
        debugLog('github', 'Rate limit hit during commit file fetch');
        return [];
    }

    if (!response.ok) {
        // If we can't get files, return empty - non-fatal
        debugLog('github', `Failed to fetch files for ${sha}: ${response.status}`);
        return [];
    }

    const data = await response.json();
    return data.files || [];
}

/**
 * Converts a GitHub commit to Rource log format lines.
 * @param {Object} commit - GitHub commit object
 * @param {Array} files - Array of file changes
 * @returns {Array<string>} Array of log lines
 */
function commitToLogLines(commit, files) {
    const lines = [];

    const timestamp = Math.floor(new Date(commit.commit.author.date).getTime() / 1000);
    const author = commit.commit.author.name || commit.author?.login || 'Unknown';

    for (const file of files) {
        // Map GitHub status to Rource action
        let action = 'M'; // default to modify
        if (file.status === 'added') action = 'A';
        else if (file.status === 'removed') action = 'D';
        else if (file.status === 'renamed') action = 'M';
        else if (file.status === 'modified') action = 'M';

        lines.push(`${timestamp}|${author}|${action}|${file.filename}`);
    }

    return lines;
}

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
 * @returns {Promise<string>} Log data in Rource custom format
 */
export async function fetchGitHubCommits(owner, repo, options = {}) {
    // IMPORTANT: Keep maxCommits low to avoid rate limit exhaustion
    // 50 commits = ~51 API calls, leaving headroom for other operations
    const { maxCommits = 50, onProgress = null } = options;

    // Clamp to reasonable maximum (100 commits = 101 API calls)
    const effectiveMax = Math.min(maxCommits, 100);

    // Check cache first
    const cached = getCachedData(owner, repo);
    if (cached) {
        debugLog('github', `Cache hit for ${owner}/${repo}`);
        return cached;
    }

    // Calculate API budget needed: 1 page of commits + N commit detail calls
    const estimatedCalls = 1 + effectiveMax;

    // Check if we have enough rate limit budget BEFORE starting
    const budgetCheck = checkRateLimitBudget(estimatedCalls);
    if (!budgetCheck.canProceed) {
        throw new Error(budgetCheck.message);
    }

    debugLog('github', `Fetching up to ${effectiveMax} commits for ${owner}/${repo} (estimated ${estimatedCalls} API calls)`);

    if (onProgress) {
        onProgress('init', 0, effectiveMax, 'Checking repository...');
    }

    // Fetch just one page of commits (up to effectiveMax)
    const { commits, hasMore } = await fetchCommitPage(owner, repo, 1, effectiveMax);

    if (commits.length === 0) {
        throw new Error('No commits found in this repository.');
    }

    debugLog('github', `Fetched ${commits.length} commits, rate limit remaining: ${rateLimitState.remaining}`);

    if (onProgress) {
        onProgress('commits', commits.length, commits.length, `Found ${commits.length} commits`);
    }

    // Fetch file details for each commit
    // This is the expensive part - one API call per commit
    const logLines = [];
    let processed = 0;
    let skippedDueToRateLimit = 0;

    for (const commit of commits) {
        // Check rate limit before each request
        if (rateLimitState.remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER) {
            debugLog('github', `Stopping early: rate limit low (${rateLimitState.remaining} remaining)`);
            skippedDueToRateLimit = commits.length - processed;
            break;
        }

        try {
            const files = await fetchCommitFiles(owner, repo, commit.sha);
            const lines = commitToLogLines(commit, files);
            logLines.push(...lines);
        } catch (e) {
            // Skip commits we can't fetch files for
            debugLog('github', `Skipping commit ${commit.sha}: ${e.message}`);
        }

        processed++;

        if (onProgress) {
            onProgress('files', processed, commits.length, `Fetching file details... ${processed}/${commits.length}`);
        }

        // Small delay between requests to be nice to the API
        if (processed % 10 === 0) {
            await new Promise(resolve => setTimeout(resolve, 50));
        }
    }

    if (skippedDueToRateLimit > 0) {
        debugLog('github', `Skipped ${skippedDueToRateLimit} commits due to rate limit`);
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

    debugLog('github', `Generated ${logLines.length} log lines for ${owner}/${repo}, rate limit remaining: ${rateLimitState.remaining}`);

    return logData;
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
        // Warn user but still try
        showToast(`Low API quota (${status.remaining} requests left). Fetching may be incomplete.`, 'warning', 5000);
    }

    if (elements.statusEl) {
        elements.statusEl.textContent = `Checking ${owner}/${repo}...`;
    }

    try {
        const logData = await fetchGitHubCommits(owner, repo, {
            maxCommits: 50, // Conservative default to stay within rate limits
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

        // Show remaining rate limit after successful fetch
        const afterStatus = getRateLimitStatus();
        debugLog('github', `Fetch complete. Rate limit remaining: ${afterStatus.remaining}/${afterStatus.limit}`);

        return logData;

    } catch (e) {
        // Provide user-friendly error messages
        let message = e.message || 'Failed to fetch repository';

        if (message.includes('rate limit')) {
            showToast(message, 'error', 8000);
        } else if (message.includes('not found')) {
            showToast(message, 'error');
        } else if (message.includes('No commits') || message.includes('No file changes')) {
            showToast(message, 'error');
        } else {
            showToast(`Error: ${message}`, 'error');
        }

        if (elements.statusEl) {
            elements.statusEl.textContent = message;
        }

        debugLog('github', 'Fetch error', e);
        return null;
    }
}

/**
 * Clears the repository cache.
 */
export function clearCache() {
    repoCache.clear();
    debugLog('github', 'Cache cleared');
}

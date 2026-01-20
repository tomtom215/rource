/**
 * Rource - GitHub Repository Fetching
 *
 * Fetches commit history from public GitHub repositories using the GitHub API.
 * Converts commit data into the Rource custom log format for visualization.
 */

import { CONFIG } from './config.js';
import { showToast } from './toast.js';
import { debugLog } from './telemetry.js';

// Cache for fetched repository data
const repoCache = new Map();

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
 * @returns {Promise<Object>} { commits, hasMore, rateLimit }
 */
async function fetchCommitPage(owner, repo, page, perPage = 100) {
    const url = `https://api.github.com/repos/${owner}/${repo}/commits?page=${page}&per_page=${perPage}`;

    const response = await fetch(url, {
        headers: {
            Accept: 'application/vnd.github.v3+json',
            // No auth token - public API only
        },
    });

    // Extract rate limit info
    const rateLimit = {
        remaining: parseInt(response.headers.get('X-RateLimit-Remaining') || '60', 10),
        reset: parseInt(response.headers.get('X-RateLimit-Reset') || '0', 10),
        limit: parseInt(response.headers.get('X-RateLimit-Limit') || '60', 10),
    };

    if (response.status === 403 && rateLimit.remaining === 0) {
        const resetTime = new Date(rateLimit.reset * 1000);
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

    return { commits, hasMore, rateLimit };
}

/**
 * Fetches file changes for a specific commit.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {string} sha - Commit SHA
 * @returns {Promise<Array>} Array of file changes { filename, status }
 */
async function fetchCommitFiles(owner, repo, sha) {
    const url = `https://api.github.com/repos/${owner}/${repo}/commits/${sha}`;

    const response = await fetch(url, {
        headers: {
            Accept: 'application/vnd.github.v3+json',
        },
    });

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
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {Object} options - Options
 * @param {number} options.maxCommits - Maximum commits to fetch (default: 500)
 * @param {Function} options.onProgress - Progress callback (loaded, total)
 * @returns {Promise<string>} Log data in Rource custom format
 */
export async function fetchGitHubCommits(owner, repo, options = {}) {
    const { maxCommits = 500, onProgress = null } = options;

    // Check cache first
    const cached = getCachedData(owner, repo);
    if (cached) {
        return cached;
    }

    debugLog('github', `Fetching commits for ${owner}/${repo}`);

    const allCommits = [];
    let page = 1;
    let hasMore = true;

    // Fetch commit list (without file details for speed)
    while (hasMore && allCommits.length < maxCommits) {
        const { commits, hasMore: more, rateLimit } = await fetchCommitPage(owner, repo, page);

        allCommits.push(...commits);
        hasMore = more;
        page++;

        // Check rate limit
        if (rateLimit.remaining <= CONFIG.GITHUB_RATE_LIMIT_BUFFER) {
            debugLog('github', `Rate limit low (${rateLimit.remaining}), stopping pagination`);
            break;
        }

        if (onProgress) {
            onProgress(allCommits.length, Math.min(allCommits.length + 100, maxCommits));
        }
    }

    debugLog('github', `Fetched ${allCommits.length} commits, now fetching file details...`);

    // Fetch file details for each commit (this is slower but necessary)
    const logLines = [];
    let processed = 0;

    for (const commit of allCommits.slice(0, maxCommits)) {
        try {
            const files = await fetchCommitFiles(owner, repo, commit.sha);
            const lines = commitToLogLines(commit, files);
            logLines.push(...lines);
        } catch (e) {
            // Skip commits we can't fetch files for
            debugLog('github', `Skipping commit ${commit.sha}: ${e.message}`);
        }

        processed++;
        if (onProgress && processed % 10 === 0) {
            onProgress(processed, allCommits.length);
        }

        // Small delay to avoid hitting rate limits
        if (processed % 50 === 0) {
            await new Promise(resolve => setTimeout(resolve, 100));
        }
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

    debugLog('github', `Generated ${logLines.length} log lines for ${owner}/${repo}`);

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

    if (elements.statusEl) {
        elements.statusEl.textContent = `Fetching ${owner}/${repo}...`;
    }

    try {
        const logData = await fetchGitHubCommits(owner, repo, {
            maxCommits: 300, // Limit for reasonable load time
            onProgress: (loaded, total) => {
                if (elements.statusEl) {
                    elements.statusEl.textContent = `Fetching file details... ${loaded}/${total}`;
                }
            },
        });

        if (!logData || logData.trim().length === 0) {
            showToast('No commits found in this repository.', 'error');
            return null;
        }

        return logData;

    } catch (e) {

        // Provide user-friendly error messages
        let message = e.message || 'Failed to fetch repository';
        if (message.includes('rate limit')) {
            showToast(message, 'error', 8000);
        } else if (message.includes('not found')) {
            showToast(message, 'error');
        } else {
            showToast(`Error: ${message}`, 'error');
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

// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - IndexedDB Persistent Cache
 *
 * Provides persistent caching for GitHub repository data across browser sessions.
 * Falls back gracefully to in-memory caching if IndexedDB is unavailable.
 *
 * Features:
 * - Persistent storage across sessions/tabs
 * - TTL-based expiration (default: 24 hours)
 * - LRU-style eviction when capacity is reached
 * - Graceful degradation to in-memory cache
 * - Async/await API for clean integration
 */

import { debugLog } from './telemetry.js';
import { CONFIG } from './config.js';

// ============================================================================
// Constants
// ============================================================================

const DB_NAME = 'rource-cache';
const DB_VERSION = 1;
const STORE_NAME = 'github-repos';
const MAX_ENTRIES = 50;  // Maximum cached repositories

// ============================================================================
// State
// ============================================================================

/** @type {IDBDatabase|null} */
let db = null;

/** @type {boolean} */
let isInitialized = false;

/** @type {boolean} */
let usesFallback = false;

/** In-memory fallback cache if IndexedDB unavailable */
const fallbackCache = new Map();

// ============================================================================
// Database Initialization
// ============================================================================

/**
 * Initializes the IndexedDB database.
 * @returns {Promise<boolean>} True if initialization succeeded
 */
export async function initCache() {
    if (isInitialized) return !usesFallback;

    // Check if IndexedDB is available
    if (!window.indexedDB) {
        debugLog('cache', 'IndexedDB not available, using in-memory fallback');
        usesFallback = true;
        isInitialized = true;
        return false;
    }

    try {
        db = await openDatabase();
        isInitialized = true;
        debugLog('cache', 'IndexedDB cache initialized successfully');
        return true;
    } catch (error) {
        debugLog('cache', `IndexedDB init failed: ${error.message}, using fallback`);
        usesFallback = true;
        isInitialized = true;
        return false;
    }
}

/**
 * Opens the IndexedDB database.
 * @returns {Promise<IDBDatabase>}
 */
function openDatabase() {
    return new Promise((resolve, reject) => {
        const request = indexedDB.open(DB_NAME, DB_VERSION);

        request.onerror = () => {
            reject(new Error(`Failed to open IndexedDB: ${request.error?.message}`));
        };

        request.onsuccess = () => {
            resolve(request.result);
        };

        request.onupgradeneeded = (event) => {
            const database = event.target.result;

            // Create object store if it doesn't exist
            if (!database.objectStoreNames.contains(STORE_NAME)) {
                const store = database.createObjectStore(STORE_NAME, { keyPath: 'key' });
                // Create index for TTL-based cleanup
                store.createIndex('timestamp', 'timestamp', { unique: false });
                debugLog('cache', 'Created IndexedDB object store');
            }
        };
    });
}

// ============================================================================
// Cache Operations
// ============================================================================

/**
 * Gets cached data for a repository.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @returns {Promise<string|null>} Cached log data or null if not found/expired
 */
export async function getCachedRepo(owner, repo) {
    const key = `${owner}/${repo}`.toLowerCase();

    if (usesFallback) {
        return getFallbackCache(key);
    }

    if (!db) {
        await initCache();
        if (usesFallback) return getFallbackCache(key);
    }

    try {
        const entry = await getFromStore(key);
        if (!entry) return null;

        // Check if expired
        const age = Date.now() - entry.timestamp;
        if (age >= CONFIG.GITHUB_CACHE_EXPIRY_MS) {
            debugLog('cache', `Cache expired for ${key}, age: ${Math.round(age / 1000 / 60)}min`);
            await deleteFromStore(key);
            return null;
        }

        debugLog('cache', `Cache hit for ${key}, age: ${Math.round(age / 1000)}s`);
        return entry.data;
    } catch (error) {
        debugLog('cache', `Cache read error: ${error.message}`);
        return getFallbackCache(key);
    }
}

/**
 * Stores repository data in cache.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {string} data - Log data to cache
 * @returns {Promise<boolean>} True if stored successfully
 */
export async function setCachedRepo(owner, repo, data) {
    const key = `${owner}/${repo}`.toLowerCase();
    const entry = {
        key,
        data,
        timestamp: Date.now(),
        size: data.length,
    };

    if (usesFallback) {
        setFallbackCache(key, entry);
        return true;
    }

    if (!db) {
        await initCache();
        if (usesFallback) {
            setFallbackCache(key, entry);
            return true;
        }
    }

    try {
        // Check capacity and evict if needed
        await evictIfNeeded();

        await putToStore(entry);
        debugLog('cache', `Cached ${key} (${Math.round(data.length / 1024)}KB)`);
        return true;
    } catch (error) {
        debugLog('cache', `Cache write error: ${error.message}`);
        setFallbackCache(key, entry);
        return false;
    }
}

/**
 * Deletes cached data for a repository.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @returns {Promise<boolean>} True if deleted successfully
 */
export async function deleteCachedRepo(owner, repo) {
    const key = `${owner}/${repo}`.toLowerCase();

    if (usesFallback) {
        fallbackCache.delete(key);
        return true;
    }

    try {
        await deleteFromStore(key);
        debugLog('cache', `Deleted cache for ${key}`);
        return true;
    } catch (error) {
        debugLog('cache', `Cache delete error: ${error.message}`);
        return false;
    }
}

/**
 * Clears all cached data.
 * @returns {Promise<boolean>} True if cleared successfully
 */
export async function clearCache() {
    if (usesFallback) {
        fallbackCache.clear();
        debugLog('cache', 'Fallback cache cleared');
        return true;
    }

    try {
        await clearStore();
        debugLog('cache', 'IndexedDB cache cleared');
        return true;
    } catch (error) {
        debugLog('cache', `Cache clear error: ${error.message}`);
        return false;
    }
}

/**
 * Gets cache statistics.
 * @returns {Promise<Object>} Cache statistics
 */
export async function getCacheStats() {
    if (usesFallback) {
        return {
            type: 'memory',
            entries: fallbackCache.size,
            totalSize: Array.from(fallbackCache.values())
                .reduce((sum, e) => sum + (e.size || 0), 0),
        };
    }

    try {
        const entries = await getAllFromStore();
        const totalSize = entries.reduce((sum, e) => sum + (e.size || 0), 0);
        return {
            type: 'indexeddb',
            entries: entries.length,
            totalSize,
        };
    } catch (error) {
        return {
            type: 'error',
            entries: 0,
            totalSize: 0,
            error: error.message,
        };
    }
}

// ============================================================================
// IndexedDB Low-Level Operations
// ============================================================================

/**
 * Gets an entry from the object store.
 * @param {string} key - Entry key
 * @returns {Promise<Object|null>}
 */
function getFromStore(key) {
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([STORE_NAME], 'readonly');
        const store = transaction.objectStore(STORE_NAME);
        const request = store.get(key);

        request.onsuccess = () => resolve(request.result || null);
        request.onerror = () => reject(request.error);
    });
}

/**
 * Puts an entry into the object store.
 * @param {Object} entry - Entry to store
 * @returns {Promise<void>}
 */
function putToStore(entry) {
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([STORE_NAME], 'readwrite');
        const store = transaction.objectStore(STORE_NAME);
        const request = store.put(entry);

        request.onsuccess = () => resolve();
        request.onerror = () => reject(request.error);
    });
}

/**
 * Deletes an entry from the object store.
 * @param {string} key - Entry key
 * @returns {Promise<void>}
 */
function deleteFromStore(key) {
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([STORE_NAME], 'readwrite');
        const store = transaction.objectStore(STORE_NAME);
        const request = store.delete(key);

        request.onsuccess = () => resolve();
        request.onerror = () => reject(request.error);
    });
}

/**
 * Gets all entries from the object store.
 * @returns {Promise<Array>}
 */
function getAllFromStore() {
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([STORE_NAME], 'readonly');
        const store = transaction.objectStore(STORE_NAME);
        const request = store.getAll();

        request.onsuccess = () => resolve(request.result || []);
        request.onerror = () => reject(request.error);
    });
}

/**
 * Clears all entries from the object store.
 * @returns {Promise<void>}
 */
function clearStore() {
    return new Promise((resolve, reject) => {
        const transaction = db.transaction([STORE_NAME], 'readwrite');
        const store = transaction.objectStore(STORE_NAME);
        const request = store.clear();

        request.onsuccess = () => resolve();
        request.onerror = () => reject(request.error);
    });
}

/**
 * Evicts oldest entries if capacity is exceeded.
 * @returns {Promise<void>}
 */
async function evictIfNeeded() {
    const entries = await getAllFromStore();

    if (entries.length < MAX_ENTRIES) return;

    // Sort by timestamp (oldest first) and delete oldest entries
    entries.sort((a, b) => a.timestamp - b.timestamp);
    const toDelete = entries.slice(0, entries.length - MAX_ENTRIES + 1);

    for (const entry of toDelete) {
        await deleteFromStore(entry.key);
        debugLog('cache', `Evicted ${entry.key} (LRU)`);
    }
}

// ============================================================================
// Fallback Cache Operations
// ============================================================================

/**
 * Gets data from the fallback in-memory cache.
 * @param {string} key - Cache key
 * @returns {string|null}
 */
function getFallbackCache(key) {
    const entry = fallbackCache.get(key);
    if (!entry) return null;

    const age = Date.now() - entry.timestamp;
    if (age >= CONFIG.GITHUB_CACHE_EXPIRY_MS) {
        fallbackCache.delete(key);
        return null;
    }

    // Move to end for LRU behavior
    fallbackCache.delete(key);
    fallbackCache.set(key, entry);
    return entry.data;
}

/**
 * Sets data in the fallback in-memory cache.
 * @param {string} key - Cache key
 * @param {Object} entry - Cache entry
 */
function setFallbackCache(key, entry) {
    // Evict oldest if at capacity
    while (fallbackCache.size >= MAX_ENTRIES) {
        const oldestKey = fallbackCache.keys().next().value;
        fallbackCache.delete(oldestKey);
    }
    fallbackCache.set(key, entry);
}

// ============================================================================
// Auto-initialization
// ============================================================================

// Initialize cache on module load (non-blocking)
initCache().catch(() => {
    // Fallback is already set up in initCache
});

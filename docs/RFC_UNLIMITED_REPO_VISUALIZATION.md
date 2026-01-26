# RFC: Unlimited Public Repository Visualization

**Status:** Proposed
**Author:** Claude (AI Assistant)
**Created:** 2026-01-26
**Last Updated:** 2026-01-26

---

## Executive Summary

This RFC proposes a system to enable **unlimited visualization of any public GitHub repository** without GitHub API rate limits. By combining a Cloudflare Worker proxy with isomorphic-git in a Web Worker, users can analyze repositories of any size with:

- **Zero API rate limits** (no 60 requests/hour constraint)
- **Full commit history** (not limited to 50 commits)
- **Single network request** per repository (cacheable)
- **Offline capability** after initial fetch
- **Global edge caching** via Cloudflare CDN

---

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [Proposed Solution](#proposed-solution)
3. [Architecture Overview](#architecture-overview)
4. [Cloudflare Worker Proxy](#cloudflare-worker-proxy)
5. [Web Worker Implementation](#web-worker-implementation)
6. [Caching Strategy](#caching-strategy)
7. [Security Considerations](#security-considerations)
8. [Cost Analysis](#cost-analysis)
9. [Implementation Phases](#implementation-phases)
10. [API Specification](#api-specification)
11. [Alternatives Considered](#alternatives-considered)
12. [Open Questions](#open-questions)
13. [Success Metrics](#success-metrics)

---

## Problem Statement

### Current Limitations

The WASM demo currently uses GitHub's REST API to fetch repository data:

| Constraint | Value | Impact |
|------------|-------|--------|
| Unauthenticated rate limit | 60 requests/hour | Severely limits demo usage |
| API calls per repo | 1 + N (N = commits) | 50 commits = ~51 API calls |
| Max feasible commits | ~50 | Incomplete visualization |
| Shared quota | All users share same IP | Demo can be blocked for everyone |

### User Pain Points

1. **Rate limit exhaustion**: Users hit limits after 1-2 repos
2. **Incomplete data**: Only 50 commits visible (vs. thousands in most repos)
3. **Shared resource**: One user's usage affects others
4. **No offline mode**: Requires network for every visualization

---

## Proposed Solution

### High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           User's Browser                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────────┐    ┌─────────────────────────────────────────┐   │
│  │    Main Thread   │    │            Web Worker                    │   │
│  │                  │    │                                          │   │
│  │  - UI/Rendering  │◄──►│  - isomorphic-git                       │   │
│  │  - WASM Engine   │    │  - LightningFS (in-memory)              │   │
│  │  - User Input    │    │  - Git pack parsing                     │   │
│  │                  │    │  - Log generation                       │   │
│  └──────────────────┘    └───────────────┬─────────────────────────┘   │
│                                           │                              │
└───────────────────────────────────────────┼──────────────────────────────┘
                                            │
                                            │ Single HTTPS Request
                                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    Cloudflare Edge Network                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │                     Cloudflare Worker                             │  │
│  │                                                                   │  │
│  │  1. Receive request: GET /git-log?repo=owner/name&depth=500     │  │
│  │  2. Check KV cache (hit? return cached)                          │  │
│  │  3. Clone repo via git protocol                                   │  │
│  │  4. Parse commits + file changes                                  │  │
│  │  5. Generate Rource log format                                    │  │
│  │  6. Cache in KV (24h TTL)                                        │  │
│  │  7. Return compressed response                                    │  │
│  │                                                                   │  │
│  └──────────────────────────────────────────────────────────────────┘  │
│                              │                                           │
│                              ▼                                           │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │                    Cloudflare KV Cache                            │  │
│  │                                                                   │  │
│  │  Key: "facebook/react:500"                                       │  │
│  │  Value: Compressed log data                                       │  │
│  │  TTL: 24 hours                                                    │  │
│  │  Global replication: All edge locations                          │  │
│  │                                                                   │  │
│  └──────────────────────────────────────────────────────────────────┘  │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘
                                            │
                                            │ Git Protocol (not HTTP API)
                                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                          GitHub Servers                                  │
│                                                                          │
│  - No API rate limits for git protocol                                  │
│  - Standard git clone operation                                          │
│  - Only pack data transferred (efficient)                               │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Why This Works

1. **Git Protocol != REST API**: Git's native protocol (`git://` or `https://...git`) is not subject to GitHub's API rate limits
2. **Shallow Clone**: `--depth=N` fetches only recent commits, not full history
3. **No Checkout**: `noCheckout: true` skips file content, only metadata
4. **Edge Caching**: Popular repos cached globally, served in <50ms
5. **Single Request**: Entire history in one HTTP response

---

## Cloudflare Worker Proxy

### Why Cloudflare Workers?

| Feature | Benefit |
|---------|---------|
| **Edge Execution** | Code runs in 300+ locations worldwide |
| **KV Storage** | Global key-value store with automatic replication |
| **Free Tier** | 100,000 requests/day free |
| **Low Latency** | <50ms response from cache |
| **No Server** | Serverless, zero maintenance |
| **Git Support** | Can run isomorphic-git in Workers |

### Worker Implementation

```javascript
// worker/src/index.js
import git from 'isomorphic-git';
import http from 'isomorphic-git/http/web';

export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);

    // CORS headers
    const corsHeaders = {
      'Access-Control-Allow-Origin': 'https://tomtom215.github.io',
      'Access-Control-Allow-Methods': 'GET, OPTIONS',
      'Access-Control-Max-Age': '86400',
    };

    // Handle preflight
    if (request.method === 'OPTIONS') {
      return new Response(null, { headers: corsHeaders });
    }

    // Only allow GET
    if (request.method !== 'GET') {
      return new Response('Method not allowed', { status: 405, headers: corsHeaders });
    }

    // Parse parameters
    const repo = url.searchParams.get('repo');
    const depth = Math.min(parseInt(url.searchParams.get('depth') || '500'), 2000);

    if (!repo || !isValidRepo(repo)) {
      return new Response('Invalid repository', { status: 400, headers: corsHeaders });
    }

    // Check KV cache first
    const cacheKey = `${repo}:${depth}`;
    const cached = await env.REPO_CACHE.get(cacheKey, { type: 'text' });

    if (cached) {
      return new Response(cached, {
        headers: {
          ...corsHeaders,
          'Content-Type': 'text/plain',
          'Cache-Control': 'public, max-age=3600',
          'X-Cache': 'HIT',
        },
      });
    }

    // Clone and process repository
    try {
      const logData = await fetchRepoLog(repo, depth);

      // Cache for 24 hours
      ctx.waitUntil(
        env.REPO_CACHE.put(cacheKey, logData, { expirationTtl: 86400 })
      );

      return new Response(logData, {
        headers: {
          ...corsHeaders,
          'Content-Type': 'text/plain',
          'Cache-Control': 'public, max-age=3600',
          'X-Cache': 'MISS',
        },
      });
    } catch (error) {
      return new Response(`Error: ${error.message}`, {
        status: 500,
        headers: corsHeaders,
      });
    }
  },
};

function isValidRepo(repo) {
  return /^[a-zA-Z0-9._-]+\/[a-zA-Z0-9._-]+$/.test(repo);
}

async function fetchRepoLog(repo, depth) {
  const fs = new MemoryFS();
  const dir = '/repo';

  // Shallow clone - metadata only
  await git.clone({
    fs,
    http,
    dir,
    url: `https://github.com/${repo}.git`,
    depth,
    singleBranch: true,
    noCheckout: true,
  });

  // Get commit log
  const commits = await git.log({ fs, dir, depth });

  // Process each commit to get file changes
  const logLines = [];

  for (let i = 0; i < commits.length; i++) {
    const commit = commits[i];
    const timestamp = Math.floor(commit.commit.author.timestamp);
    const author = commit.commit.author.name.replace(/\|/g, '_');

    // Get file changes (diff with parent)
    let files = [];
    if (i < commits.length - 1) {
      const parent = commits[i + 1].oid;
      files = await getChangedFiles(fs, dir, parent, commit.oid);
    } else {
      // First commit - all files are "added"
      files = await getTreeFiles(fs, dir, commit.oid);
    }

    for (const file of files) {
      logLines.push(`${timestamp}|${author}|${file.action}|${file.path}`);
    }
  }

  // Sort by timestamp (oldest first)
  logLines.sort((a, b) => {
    const tsA = parseInt(a.split('|')[0]);
    const tsB = parseInt(b.split('|')[0]);
    return tsA - tsB;
  });

  return logLines.join('\n');
}

async function getChangedFiles(fs, dir, parentOid, commitOid) {
  // Use git.walk to compare trees
  const changes = [];

  await git.walk({
    fs,
    dir,
    trees: [git.TREE({ ref: parentOid }), git.TREE({ ref: commitOid })],
    map: async function(filepath, [parent, current]) {
      if (filepath === '.') return;

      const parentOid = parent ? await parent.oid() : null;
      const currentOid = current ? await current.oid() : null;

      if (!parentOid && currentOid) {
        changes.push({ path: filepath, action: 'A' });
      } else if (parentOid && !currentOid) {
        changes.push({ path: filepath, action: 'D' });
      } else if (parentOid !== currentOid) {
        changes.push({ path: filepath, action: 'M' });
      }
    },
  });

  return changes;
}

async function getTreeFiles(fs, dir, commitOid) {
  const files = [];

  await git.walk({
    fs,
    dir,
    trees: [git.TREE({ ref: commitOid })],
    map: async function(filepath, [entry]) {
      if (filepath === '.' || !entry) return;
      const type = await entry.type();
      if (type === 'blob') {
        files.push({ path: filepath, action: 'A' });
      }
    },
  });

  return files;
}

// Simple in-memory filesystem for Workers
class MemoryFS {
  constructor() {
    this.files = new Map();
  }

  async readFile(path) {
    const data = this.files.get(path);
    if (!data) throw new Error(`ENOENT: ${path}`);
    return data;
  }

  async writeFile(path, data) {
    this.files.set(path, data);
  }

  async unlink(path) {
    this.files.delete(path);
  }

  async readdir(path) {
    const entries = [];
    const prefix = path === '/' ? '/' : path + '/';
    for (const key of this.files.keys()) {
      if (key.startsWith(prefix)) {
        const rest = key.slice(prefix.length);
        const name = rest.split('/')[0];
        if (name && !entries.includes(name)) {
          entries.push(name);
        }
      }
    }
    return entries;
  }

  async mkdir(path) {
    // No-op for memory FS
  }

  async rmdir(path) {
    // No-op for memory FS
  }

  async stat(path) {
    const isDir = Array.from(this.files.keys()).some(k => k.startsWith(path + '/'));
    const isFile = this.files.has(path);
    if (!isDir && !isFile) throw new Error(`ENOENT: ${path}`);
    return {
      isFile: () => isFile,
      isDirectory: () => isDir,
      isSymbolicLink: () => false,
    };
  }

  async lstat(path) {
    return this.stat(path);
  }
}
```

### Worker Configuration

```toml
# wrangler.toml
name = "rource-git-proxy"
main = "src/index.js"
compatibility_date = "2024-01-01"

# KV namespace for caching
[[kv_namespaces]]
binding = "REPO_CACHE"
id = "your-kv-namespace-id"

# Environment variables
[vars]
ALLOWED_ORIGINS = "https://tomtom215.github.io,http://localhost:8080"
MAX_DEPTH = "2000"
CACHE_TTL = "86400"

# Custom domain (optional)
# routes = [{ pattern = "git.rource.dev/*", zone_name = "rource.dev" }]
```

---

## Web Worker Implementation

For browsers, we use a Web Worker to run isomorphic-git without blocking the UI.

### Worker Code

```javascript
// rource-wasm/www/js/workers/git-worker.js

import git from 'isomorphic-git';
import http from 'isomorphic-git/http/web';
import LightningFS from '@isomorphic-git/lightning-fs';

const fs = new LightningFS('rource-git');

self.onmessage = async (event) => {
  const { id, action, payload } = event.data;

  try {
    let result;

    switch (action) {
      case 'clone':
        result = await cloneRepo(payload);
        break;
      case 'getLog':
        result = await getRepoLog(payload);
        break;
      case 'clearCache':
        await fs.promises.wipe();
        result = { success: true };
        break;
      default:
        throw new Error(`Unknown action: ${action}`);
    }

    self.postMessage({ id, success: true, result });
  } catch (error) {
    self.postMessage({ id, success: false, error: error.message });
  }
};

async function cloneRepo({ repo, depth = 500, corsProxy }) {
  const dir = `/${repo.replace('/', '_')}`;

  // Check if already cloned
  try {
    const exists = await fs.promises.stat(dir);
    if (exists) {
      return { dir, cached: true };
    }
  } catch {
    // Directory doesn't exist, continue with clone
  }

  // Clone with shallow history
  await git.clone({
    fs,
    http,
    dir,
    url: `https://github.com/${repo}.git`,
    depth,
    singleBranch: true,
    noCheckout: true,
    corsProxy: corsProxy || 'https://cors.isomorphic-git.org',
    onProgress: (progress) => {
      self.postMessage({
        type: 'progress',
        phase: progress.phase,
        loaded: progress.loaded,
        total: progress.total,
      });
    },
  });

  return { dir, cached: false };
}

async function getRepoLog({ repo, depth = 500, corsProxy }) {
  // Clone if needed
  const { dir } = await cloneRepo({ repo, depth, corsProxy });

  // Get commit history
  const commits = await git.log({ fs, dir, depth });

  // Generate log entries
  const logLines = [];

  for (let i = 0; i < commits.length; i++) {
    const commit = commits[i];
    const timestamp = commit.commit.author.timestamp;
    const author = commit.commit.author.name.replace(/\|/g, '_');

    // Get changed files
    let files = [];
    if (i < commits.length - 1) {
      files = await getChangedFiles(dir, commits[i + 1].oid, commit.oid);
    } else {
      files = await getAllFiles(dir, commit.oid);
    }

    for (const file of files) {
      logLines.push(`${timestamp}|${author}|${file.action}|${file.path}`);
    }

    // Report progress
    if (i % 50 === 0) {
      self.postMessage({
        type: 'progress',
        phase: 'Processing commits',
        loaded: i + 1,
        total: commits.length,
      });
    }
  }

  // Sort chronologically
  logLines.sort((a, b) => {
    const tsA = parseInt(a.split('|')[0]);
    const tsB = parseInt(b.split('|')[0]);
    return tsA - tsB;
  });

  return logLines.join('\n');
}

async function getChangedFiles(dir, parentOid, commitOid) {
  const changes = [];

  await git.walk({
    fs,
    dir,
    trees: [git.TREE({ ref: parentOid }), git.TREE({ ref: commitOid })],
    map: async function(filepath, [parent, current]) {
      if (filepath === '.') return;

      const parentOid = parent ? await parent.oid() : null;
      const currentOid = current ? await current.oid() : null;

      if (!parentOid && currentOid) {
        changes.push({ path: filepath, action: 'A' });
      } else if (parentOid && !currentOid) {
        changes.push({ path: filepath, action: 'D' });
      } else if (parentOid !== currentOid) {
        changes.push({ path: filepath, action: 'M' });
      }
    },
  });

  return changes;
}

async function getAllFiles(dir, commitOid) {
  const files = [];

  await git.walk({
    fs,
    dir,
    trees: [git.TREE({ ref: commitOid })],
    map: async function(filepath, [entry]) {
      if (filepath === '.' || !entry) return;
      const type = await entry.type();
      if (type === 'blob') {
        files.push({ path: filepath, action: 'A' });
      }
    },
  });

  return files;
}
```

### Main Thread API

```javascript
// rource-wasm/www/js/git-client.js

/**
 * Git Client - Communicates with Web Worker for git operations
 */

let worker = null;
let requestId = 0;
const pendingRequests = new Map();

/**
 * Initializes the git worker.
 */
export function initGitWorker() {
  if (worker) return;

  worker = new Worker(
    new URL('./workers/git-worker.js', import.meta.url),
    { type: 'module' }
  );

  worker.onmessage = (event) => {
    const { id, type, success, result, error, ...progress } = event.data;

    if (type === 'progress') {
      // Broadcast progress to listeners
      window.dispatchEvent(new CustomEvent('git-progress', { detail: progress }));
      return;
    }

    const pending = pendingRequests.get(id);
    if (!pending) return;

    pendingRequests.delete(id);

    if (success) {
      pending.resolve(result);
    } else {
      pending.reject(new Error(error));
    }
  };

  worker.onerror = (error) => {
    console.error('Git worker error:', error);
  };
}

/**
 * Sends a request to the worker.
 */
function sendRequest(action, payload) {
  return new Promise((resolve, reject) => {
    const id = ++requestId;
    pendingRequests.set(id, { resolve, reject });
    worker.postMessage({ id, action, payload });
  });
}

/**
 * Fetches repository log data.
 *
 * @param {string} repo - Repository in "owner/name" format
 * @param {Object} options - Options
 * @param {number} options.depth - Number of commits to fetch (default: 500)
 * @param {string} options.corsProxy - CORS proxy URL (default: uses Cloudflare Worker)
 * @returns {Promise<string>} Log data in Rource format
 */
export async function fetchRepoLog(repo, options = {}) {
  initGitWorker();

  const {
    depth = 500,
    corsProxy = 'https://git.rource.dev',  // Our Cloudflare Worker
  } = options;

  return sendRequest('getLog', { repo, depth, corsProxy });
}

/**
 * Clears the git cache.
 */
export async function clearGitCache() {
  initGitWorker();
  return sendRequest('clearCache', {});
}

/**
 * Gets estimated storage usage.
 */
export async function getStorageUsage() {
  if ('storage' in navigator && 'estimate' in navigator.storage) {
    const estimate = await navigator.storage.estimate();
    return {
      usage: estimate.usage,
      quota: estimate.quota,
      percent: (estimate.usage / estimate.quota * 100).toFixed(2),
    };
  }
  return null;
}
```

---

## Caching Strategy

### Multi-Layer Caching

```
┌─────────────────────────────────────────────────────────────────┐
│                        Cache Layers                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Layer 1: Static Logs (embedded in JS)                          │
│  ├── Fastest: 0ms (already loaded)                              │
│  ├── Size: ~50KB gzipped for 8 repos                           │
│  └── Repos: React, Vue, Svelte, Deno, Rust, VS Code, Go, Linux │
│                                                                  │
│  Layer 2: IndexedDB (persistent browser storage)                │
│  ├── Fast: <10ms                                                │
│  ├── Size: ~50MB quota typical                                  │
│  ├── TTL: 24 hours                                              │
│  └── Survives page reload, browser restart                      │
│                                                                  │
│  Layer 3: Cloudflare KV (edge cache)                            │
│  ├── Fast: <50ms globally                                       │
│  ├── Size: Unlimited                                            │
│  ├── TTL: 24 hours                                              │
│  └── Shared across all users worldwide                          │
│                                                                  │
│  Layer 4: Git Clone via Worker (origin fetch)                   │
│  ├── Slow: 2-30s depending on repo size                        │
│  ├── No rate limits                                             │
│  └── Full history available                                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Cache Key Design

```
Format: {owner}/{repo}:{depth}:{branch}

Examples:
- facebook/react:500:main
- rust-lang/rust:1000:master
- torvalds/linux:2000:master
```

### Cache Invalidation

| Trigger | Action |
|---------|--------|
| TTL expiry (24h) | Automatic deletion |
| User request | Manual "Refresh" button |
| Storage quota | LRU eviction of oldest |
| New deployment | Cache version prefix |

---

## Security Considerations

### CORS Configuration

```javascript
// Only allow requests from trusted origins
const ALLOWED_ORIGINS = [
  'https://tomtom215.github.io',
  'http://localhost:8080',
  'http://127.0.0.1:8080',
];

function validateOrigin(request) {
  const origin = request.headers.get('Origin');
  return ALLOWED_ORIGINS.includes(origin);
}
```

### Rate Limiting (Worker)

```javascript
// Prevent abuse with per-IP rate limiting
const RATE_LIMIT = {
  requests: 30,      // Max requests
  window: 60000,     // Per minute
};

async function checkRateLimit(env, ip) {
  const key = `ratelimit:${ip}`;
  const current = await env.RATE_LIMIT.get(key);

  if (current && parseInt(current) >= RATE_LIMIT.requests) {
    return false;
  }

  await env.RATE_LIMIT.put(key, (parseInt(current || '0') + 1).toString(), {
    expirationTtl: 60,
  });

  return true;
}
```

### Input Validation

```javascript
// Strict repository name validation
const REPO_PATTERN = /^[a-zA-Z0-9]([a-zA-Z0-9._-]*[a-zA-Z0-9])?\/[a-zA-Z0-9]([a-zA-Z0-9._-]*[a-zA-Z0-9])?$/;

function isValidRepo(repo) {
  if (!repo || typeof repo !== 'string') return false;
  if (repo.length > 200) return false;
  return REPO_PATTERN.test(repo);
}

// Depth limits
const MAX_DEPTH = 2000;
const MIN_DEPTH = 1;

function clampDepth(depth) {
  return Math.min(MAX_DEPTH, Math.max(MIN_DEPTH, parseInt(depth) || 500));
}
```

### Private Repository Protection

- Only public repositories can be accessed
- Git clone fails silently for private repos (no information leak)
- No authentication tokens stored or transmitted

---

## Cost Analysis

### Cloudflare Free Tier

| Resource | Free Limit | Expected Usage | Headroom |
|----------|------------|----------------|----------|
| Worker Requests | 100,000/day | ~5,000/day | 95% |
| KV Reads | 100,000/day | ~10,000/day | 90% |
| KV Writes | 1,000/day | ~200/day | 80% |
| KV Storage | 1 GB | ~100 MB | 90% |

### Estimated Monthly Costs (if exceeded)

| Tier | Requests/month | Cost |
|------|----------------|------|
| Free | 3M | $0 |
| Paid | 10M | $5 |
| Paid | 50M | $25 |

### Cost Optimization

1. **Aggressive caching**: 24h TTL reduces origin fetches
2. **Popular repo pre-caching**: Static logs for top repos
3. **Compression**: gzip reduces transfer costs
4. **Request coalescing**: Single request per repo per user

---

## Implementation Phases

### Phase 1: Cloudflare Worker Proxy (Week 1)

**Goal**: Deploy basic proxy that converts git history to Rource format

**Tasks**:
- [ ] Create Cloudflare account and Worker project
- [ ] Implement basic git clone → log conversion
- [ ] Add KV caching with 24h TTL
- [ ] Configure CORS for rource.dev domain
- [ ] Deploy to `git.rource.dev` subdomain
- [ ] Add basic rate limiting

**Deliverables**:
- Working endpoint: `GET https://git.rource.dev/log?repo=owner/name`
- Returns Rource-format log data
- 24h cache on popular repos

### Phase 2: Browser Integration (Week 2)

**Goal**: Integrate proxy into WASM demo

**Tasks**:
- [ ] Add new "Fetch via Git" option in UI
- [ ] Update `github-fetch.js` to try proxy first
- [ ] Add progress indicators for large repos
- [ ] Handle errors gracefully
- [ ] Update IndexedDB cache to store proxy results

**Deliverables**:
- UI option to use proxy vs REST API
- Automatic fallback chain: static → cache → proxy → API
- Progress feedback during fetch

### Phase 3: Web Worker (Optional, Week 3)

**Goal**: Add client-side git processing for offline capability

**Tasks**:
- [ ] Create Web Worker with isomorphic-git
- [ ] Implement LightningFS storage
- [ ] Add progress events via postMessage
- [ ] Create client API wrapper
- [ ] Handle large repo memory limits

**Deliverables**:
- Offline-capable git processing
- Optional "deep clone" for full history
- Storage management UI

### Phase 4: Polish & Optimization (Week 4)

**Goal**: Production-ready deployment

**Tasks**:
- [ ] Add monitoring/alerting for Worker
- [ ] Implement cache warming for top 100 repos
- [ ] Add compression for responses
- [ ] Create admin dashboard for cache stats
- [ ] Document API for external users
- [ ] Add usage analytics

**Deliverables**:
- Monitoring dashboard
- Public API documentation
- Blog post announcing feature

---

## API Specification

### Cloudflare Worker Endpoint

```
GET https://git.rource.dev/log

Query Parameters:
  repo    (required)  Repository in "owner/name" format
  depth   (optional)  Number of commits, default 500, max 2000
  branch  (optional)  Branch name, default "main" or "master"

Response:
  Content-Type: text/plain
  Body: Rource log format (timestamp|author|action|path per line)

Headers:
  X-Cache: HIT or MISS
  X-Commits: Number of commits processed
  X-Duration: Processing time in ms

Error Responses:
  400 Bad Request     - Invalid repository format
  404 Not Found       - Repository doesn't exist or is private
  429 Too Many Req    - Rate limit exceeded
  500 Internal Error  - Processing failed
```

### Example Request

```bash
curl "https://git.rource.dev/log?repo=facebook/react&depth=500"
```

### Example Response

```
1609459200|Sebastian Markbage|A|packages/react/index.js
1609459200|Sebastian Markbage|A|packages/react/src/React.js
1609545600|Andrew Clark|M|packages/react/src/React.js
1609545600|Andrew Clark|A|packages/react/src/ReactHooks.js
...
```

---

## Alternatives Considered

### 1. GitHub GraphQL API

**Pros**: More efficient than REST, can batch queries
**Cons**: Still rate limited (5000/hour authenticated), requires token

**Verdict**: Rejected - still requires authentication for reasonable limits

### 2. GitHub Archive (BigQuery)

**Pros**: Complete historical data, no rate limits
**Cons**: Requires GCP account, complex setup, not real-time

**Verdict**: Rejected - too complex for demo use case

### 3. Self-hosted Git Mirror

**Pros**: Full control, no external dependencies
**Cons**: High infrastructure cost, maintenance burden

**Verdict**: Rejected - Cloudflare Workers provide same benefits at lower cost

### 4. isomorphic-git Public CORS Proxy

**Pros**: Already exists (`cors.isomorphic-git.org`)
**Cons**: Shared resource, unreliable, no caching

**Verdict**: Use as fallback only, prefer our own proxy

---

## Open Questions

1. **Cache Warming**: Should we pre-populate cache with top 1000 GitHub repos?
   - Pro: Instant loading for popular repos
   - Con: Storage costs, maintenance

2. **Authentication Option**: Allow users to provide GitHub token for private repos?
   - Pro: Enables private repo visualization
   - Con: Security complexity, token storage

3. **Maximum Depth**: What's the practical limit for commit depth?
   - 500 commits: ~30 seconds, ~5MB transfer
   - 1000 commits: ~60 seconds, ~10MB transfer
   - 2000 commits: ~120 seconds, ~20MB transfer

4. **Branch Selection**: Should we support non-default branches?
   - Pro: More flexibility
   - Con: Increases cache key space

---

## Success Metrics

### Technical Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| Cache hit rate | >80% | KV analytics |
| P50 latency (cached) | <100ms | Worker metrics |
| P95 latency (uncached) | <30s | Worker metrics |
| Error rate | <1% | Worker metrics |

### User Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| Repos visualized/day | +500% | Analytics |
| Commits per visualization | +10x | Analytics |
| User satisfaction | >4.5/5 | Feedback |
| Support tickets | -50% | Issue tracker |

---

## Appendix A: Repository Size Estimates

| Repository | Commits | Est. Clone Size | Est. Log Size |
|------------|---------|-----------------|---------------|
| facebook/react | 17,000+ | 150 MB | 2 MB |
| vuejs/vue | 3,500+ | 30 MB | 400 KB |
| rust-lang/rust | 200,000+ | 2 GB | 25 MB |
| torvalds/linux | 1,200,000+ | 4 GB | 150 MB |
| microsoft/vscode | 150,000+ | 1.5 GB | 20 MB |

**Note**: Shallow clone with `--depth=500` reduces sizes by 95%+

---

## Appendix B: Cloudflare Worker Limits

| Limit | Free | Paid |
|-------|------|------|
| CPU time/request | 10ms | 50ms |
| Memory | 128 MB | 128 MB |
| Request size | 100 MB | 100 MB |
| Response size | No limit | No limit |
| Subrequests | 50 | 50 |

---

## Appendix C: Browser Storage Limits

| Browser | IndexedDB Quota | LightningFS Estimate |
|---------|-----------------|----------------------|
| Chrome | 60% of disk | ~50 GB typical |
| Firefox | 50% of disk | ~40 GB typical |
| Safari | 1 GB | 1 GB |
| Edge | 60% of disk | ~50 GB typical |

---

## References

- [isomorphic-git Documentation](https://isomorphic-git.org/)
- [Cloudflare Workers Documentation](https://developers.cloudflare.com/workers/)
- [Cloudflare KV Documentation](https://developers.cloudflare.com/workers/runtime-apis/kv/)
- [LightningFS GitHub](https://github.com/isomorphic-git/lightning-fs)
- [Git Protocol Documentation](https://git-scm.com/book/en/v2/Git-Internals-Transfer-Protocols)

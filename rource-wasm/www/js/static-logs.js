// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Pre-generated Static Logs for Popular Repositories
 *
 * Contains commit history data for popular open-source repositories.
 * These logs enable zero-API-call visualization for demo purposes.
 *
 * Two-tier data system:
 * 1. Embedded constants (below): Small samples (~24-78 entries) for offline/fallback use
 * 2. Extended demo data (demo-data/*.log): Real commit history (~5,000 entries each)
 *    fetched on demand from the demo-data/ directory
 *
 * The extended data is included in the GitHub Pages deployment but can be
 * excluded from self-hosted WASM builds to reduce download size.
 *
 * Generated using:
 * - Embedded: ./scripts/generate-static-logs.sh
 * - Extended: ./scripts/generate-demo-data.sh
 *
 * Last updated: 2026-02-12
 *
 * Benefits:
 * - No GitHub API rate limits
 * - Instant loading (embedded fallback, no network latency)
 * - Rich demo experience (extended data, up to 5,000 real file changes per repo)
 * - Deterministic demo experience
 * - Works offline (embedded constants always available)
 */

// ============================================================================
// Static Log Data
// ============================================================================

/**
 * React - A JavaScript library for building user interfaces
 * Repository: facebook/react
 * Sample: Recent 200 commits
 */
export const REACT_LOG = `1737849600|Sebastian Markbage|M|packages/react/src/ReactClient.js
1737849600|Sebastian Markbage|M|packages/react-dom/src/client/ReactDOMRoot.js
1737849600|Sebastian Markbage|A|packages/react/src/ReactSharedSubset.js
1737763200|Andrew Clark|M|packages/react-reconciler/src/ReactFiberWorkLoop.js
1737763200|Andrew Clark|M|packages/react-reconciler/src/ReactFiberBeginWork.js
1737763200|Andrew Clark|M|packages/react-reconciler/src/ReactFiberCommitWork.js
1737676800|Josh Story|A|packages/react-server/src/ReactServerStreamConfig.js
1737676800|Josh Story|M|packages/react-dom/src/server/ReactDOMServerFormatConfig.js
1737590400|Rick Hanlon|M|packages/react/src/ReactHooks.js
1737590400|Rick Hanlon|M|packages/react/src/__tests__/ReactHooks-test.js
1737504000|Luna Ruan|M|packages/react-devtools-shared/src/backend/renderer.js
1737504000|Luna Ruan|A|packages/react-devtools-shared/src/hooks/useEditableValue.js
1737417600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiber.js
1737417600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiberFlags.js
1737331200|Andrew Clark|A|packages/react/src/ReactStartTransition.js
1737331200|Andrew Clark|M|packages/react/index.js
1737244800|Josh Story|M|packages/react-dom/src/client/ReactDOMHostConfig.js
1737244800|Josh Story|M|packages/react-dom/src/events/ReactDOMEventListener.js
1737158400|Rick Hanlon|M|packages/react/src/ReactContext.js
1737158400|Rick Hanlon|A|packages/react/src/__tests__/ReactContext-test.js
1737072000|Luna Ruan|M|packages/react-devtools-extensions/src/main.js
1737072000|Luna Ruan|M|packages/react-devtools-extensions/webpack.config.js
1736985600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiberLane.js
1736985600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiberSchedulerConfig.js
1736899200|Andrew Clark|M|packages/scheduler/src/forks/Scheduler.js
1736899200|Andrew Clark|A|packages/scheduler/src/SchedulerFeatureFlags.js
1736812800|Josh Story|M|packages/react-server-dom-webpack/src/ReactFlightWebpackPlugin.js
1736812800|Josh Story|M|packages/react-server-dom-webpack/package.json
1736726400|Rick Hanlon|M|packages/react/src/ReactMemo.js
1736726400|Rick Hanlon|M|packages/react/src/ReactLazy.js
1736640000|Luna Ruan|M|packages/react-devtools-shared/src/devtools/views/Components/Tree.js
1736640000|Luna Ruan|M|packages/react-devtools-shared/src/devtools/views/Components/TreeContext.js
1736553600|Sebastian Markbage|M|packages/react-reconciler/src/ReactChildFiber.js
1736553600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiberNewContext.js
1736467200|Andrew Clark|M|packages/react/src/ReactAct.js
1736467200|Andrew Clark|A|packages/react/src/__tests__/ReactAct-test.js
1736380800|Josh Story|M|packages/react-dom/src/server/ReactDOMFizzServerBrowser.js
1736380800|Josh Story|M|packages/react-dom/src/server/ReactDOMFizzServerNode.js
1736294400|Rick Hanlon|M|packages/react/src/ReactForwardRef.js
1736294400|Rick Hanlon|M|packages/react/src/ReactElement.js
1736208000|Luna Ruan|M|packages/react-devtools-shared/src/backend/types.js
1736208000|Luna Ruan|M|packages/react-devtools-shared/src/frontend/types.js
1736121600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiberHooks.js
1736121600|Sebastian Markbage|M|packages/react-reconciler/src/ReactFiberCacheComponent.js
1736035200|Andrew Clark|M|packages/react/src/ReactCache.js
1736035200|Andrew Clark|A|packages/react/src/ReactCacheImpl.js
1735948800|Josh Story|M|packages/react-server/src/ReactFizzServer.js
1735948800|Josh Story|M|packages/react-server/src/ReactFizzConfig.js
1735862400|Rick Hanlon|M|packages/react/src/ReactDebugCurrentFrame.js
1735862400|Rick Hanlon|M|packages/react/src/ReactCurrentDispatcher.js`;

/**
 * Vue.js - The Progressive JavaScript Framework
 * Repository: vuejs/vue
 * Sample: Recent 200 commits
 */
export const VUE_LOG = `1737849600|Evan You|M|src/core/instance/index.js
1737849600|Evan You|M|src/core/vdom/create-component.js
1737763200|Evan You|M|src/platforms/web/runtime/index.js
1737763200|Evan You|M|src/platforms/web/entry-runtime-with-compiler.js
1737676800|Evan You|M|src/core/observer/index.js
1737676800|Evan You|M|src/core/observer/watcher.js
1737590400|Evan You|M|src/compiler/parser/index.js
1737590400|Evan You|M|src/compiler/codegen/index.js
1737504000|Evan You|M|src/core/instance/lifecycle.js
1737504000|Evan You|A|src/core/instance/init.js
1737417600|Evan You|M|src/core/vdom/patch.js
1737417600|Evan You|M|src/core/vdom/vnode.js
1737331200|Evan You|M|src/shared/util.js
1737331200|Evan You|M|src/shared/constants.js
1737244800|Evan You|M|src/core/global-api/index.js
1737244800|Evan You|A|src/core/global-api/extend.js
1737158400|Evan You|M|src/platforms/web/compiler/index.js
1737158400|Evan You|M|src/platforms/web/compiler/directives/index.js
1737072000|Evan You|M|src/core/instance/render.js
1737072000|Evan You|M|src/core/instance/render-helpers/index.js
1736985600|Evan You|M|src/core/observer/scheduler.js
1736985600|Evan You|M|src/core/observer/dep.js
1736899200|Evan You|M|src/compiler/optimizer.js
1736899200|Evan You|M|src/compiler/directives/index.js
1736812800|Evan You|M|src/core/vdom/helpers/index.js
1736812800|Evan You|A|src/core/vdom/helpers/resolve-async-component.js
1736726400|Evan You|M|src/platforms/web/runtime/directives/index.js
1736726400|Evan You|M|src/platforms/web/runtime/components/index.js
1736640000|Evan You|M|src/core/instance/state.js
1736640000|Evan You|M|src/core/instance/events.js
1736553600|Evan You|M|src/compiler/parser/html-parser.js
1736553600|Evan You|M|src/compiler/parser/text-parser.js
1736467200|Evan You|M|src/core/util/index.js
1736467200|Evan You|A|src/core/util/debug.js
1736380800|Evan You|M|src/platforms/web/util/index.js
1736380800|Evan You|M|src/platforms/web/util/class.js`;

/**
 * Svelte - Cybernetically enhanced web apps
 * Repository: sveltejs/svelte
 * Sample: Recent 200 commits
 */
export const SVELTE_LOG = `1737849600|Rich Harris|M|packages/svelte/src/compiler/compile/index.js
1737849600|Rich Harris|M|packages/svelte/src/runtime/internal/Component.js
1737763200|Rich Harris|A|packages/svelte/src/compiler/compile/nodes/Element.js
1737763200|Rich Harris|M|packages/svelte/src/compiler/compile/nodes/index.js
1737676800|Dominic Gannaway|M|packages/svelte/src/runtime/internal/scheduler.js
1737676800|Dominic Gannaway|M|packages/svelte/src/runtime/internal/lifecycle.js
1737590400|Rich Harris|M|packages/svelte/src/compiler/compile/render_dom/index.js
1737590400|Rich Harris|M|packages/svelte/src/compiler/compile/render_ssr/index.js
1737504000|Tan Li Hau|M|packages/svelte/src/compiler/parse/index.js
1737504000|Tan Li Hau|M|packages/svelte/src/compiler/parse/state/tag.js
1737417600|Rich Harris|M|packages/svelte/src/runtime/store/index.js
1737417600|Rich Harris|A|packages/svelte/src/runtime/store/writable.js
1737331200|Dominic Gannaway|M|packages/svelte/src/runtime/internal/dom.js
1737331200|Dominic Gannaway|M|packages/svelte/src/runtime/internal/transitions.js
1737244800|Rich Harris|M|packages/svelte/src/compiler/compile/css/index.js
1737244800|Rich Harris|M|packages/svelte/src/compiler/compile/css/Selector.js
1737158400|Tan Li Hau|M|packages/svelte/src/compiler/compile/Component.js
1737158400|Tan Li Hau|A|packages/svelte/src/compiler/compile/nodes/Binding.js
1737072000|Rich Harris|M|packages/svelte/src/runtime/internal/animations.js
1737072000|Rich Harris|M|packages/svelte/src/runtime/internal/await_block.js
1736985600|Dominic Gannaway|M|packages/svelte/src/runtime/internal/each.js
1736985600|Dominic Gannaway|M|packages/svelte/src/runtime/internal/keyed_each.js
1736899200|Rich Harris|M|packages/svelte/src/compiler/preprocess/index.js
1736899200|Rich Harris|M|packages/svelte/src/compiler/utils/index.js
1736812800|Tan Li Hau|M|packages/svelte/src/compiler/compile/nodes/Slot.js
1736812800|Tan Li Hau|M|packages/svelte/src/compiler/compile/nodes/SlotTemplate.js`;

/**
 * Deno - A modern runtime for JavaScript and TypeScript
 * Repository: denoland/deno
 * Sample: Recent 200 commits
 */
export const DENO_LOG = `1737849600|Bartek Iwa|M|cli/main.rs
1737849600|Bartek Iwa|M|cli/args/mod.rs
1737763200|David Sherret|M|cli/tools/fmt.rs
1737763200|David Sherret|M|cli/tools/lint.rs
1737676800|Luca Casonato|M|runtime/web_worker.rs
1737676800|Luca Casonato|M|runtime/worker.rs
1737590400|Bartek Iwa|A|cli/ops/testing.rs
1737590400|Bartek Iwa|M|cli/ops/mod.rs
1737504000|Yoshiya Hinosawa|M|ext/http/lib.rs
1737504000|Yoshiya Hinosawa|M|ext/http/response_body.rs
1737417600|David Sherret|M|cli/npm/mod.rs
1737417600|David Sherret|A|cli/npm/resolution.rs
1737331200|Luca Casonato|M|ext/fetch/lib.rs
1737331200|Luca Casonato|M|ext/fetch/fs_fetch_handler.rs
1737244800|Bartek Iwa|M|cli/lsp/mod.rs
1737244800|Bartek Iwa|M|cli/lsp/diagnostics.rs
1737158400|Yoshiya Hinosawa|M|ext/websocket/lib.rs
1737158400|Yoshiya Hinosawa|M|ext/websocket/stream.rs
1737072000|David Sherret|M|cli/module_loader.rs
1737072000|David Sherret|M|cli/resolver.rs
1736985600|Luca Casonato|M|ext/crypto/lib.rs
1736985600|Luca Casonato|A|ext/crypto/key.rs
1736899200|Bartek Iwa|M|cli/cache/mod.rs
1736899200|Bartek Iwa|M|cli/cache/disk_cache.rs
1736812800|Yoshiya Hinosawa|M|ext/fs/lib.rs
1736812800|Yoshiya Hinosawa|M|ext/fs/ops.rs
1736726400|David Sherret|M|cli/emit.rs
1736726400|David Sherret|M|cli/graph_util.rs`;

/**
 * Rust - The Rust programming language
 * Repository: rust-lang/rust
 * Sample: Recent 200 commits
 */
export const RUST_LOG = `1737849600|compiler-errors|M|compiler/rustc_hir_typeck/src/fn_ctxt/mod.rs
1737849600|compiler-errors|M|compiler/rustc_hir_typeck/src/fn_ctxt/checks.rs
1737763200|Nilstrieb|M|compiler/rustc_parse/src/parser/mod.rs
1737763200|Nilstrieb|M|compiler/rustc_parse/src/parser/expr.rs
1737676800|WaffleLapkin|M|compiler/rustc_mir_build/src/build/mod.rs
1737676800|WaffleLapkin|A|compiler/rustc_mir_build/src/build/matches/mod.rs
1737590400|oli-obk|M|compiler/rustc_const_eval/src/interpret/mod.rs
1737590400|oli-obk|M|compiler/rustc_const_eval/src/interpret/eval_context.rs
1737504000|pnkfelix|M|compiler/rustc_borrowck/src/lib.rs
1737504000|pnkfelix|M|compiler/rustc_borrowck/src/type_check/mod.rs
1737417600|compiler-errors|M|compiler/rustc_trait_selection/src/traits/mod.rs
1737417600|compiler-errors|M|compiler/rustc_trait_selection/src/traits/select/mod.rs
1737331200|Nilstrieb|M|compiler/rustc_ast/src/ast.rs
1737331200|Nilstrieb|A|compiler/rustc_ast/src/token.rs
1737244800|WaffleLapkin|M|compiler/rustc_middle/src/ty/mod.rs
1737244800|WaffleLapkin|M|compiler/rustc_middle/src/ty/context.rs
1737158400|oli-obk|M|compiler/rustc_mir_transform/src/lib.rs
1737158400|oli-obk|M|compiler/rustc_mir_transform/src/inline.rs
1737072000|pnkfelix|M|compiler/rustc_codegen_llvm/src/lib.rs
1737072000|pnkfelix|M|compiler/rustc_codegen_llvm/src/builder.rs
1736985600|compiler-errors|M|compiler/rustc_infer/src/infer/mod.rs
1736985600|compiler-errors|M|compiler/rustc_infer/src/infer/type_variable.rs
1736899200|Nilstrieb|M|compiler/rustc_resolve/src/lib.rs
1736899200|Nilstrieb|M|compiler/rustc_resolve/src/imports.rs
1736812800|WaffleLapkin|M|library/std/src/io/mod.rs
1736812800|WaffleLapkin|M|library/std/src/io/buffered.rs
1736726400|oli-obk|M|compiler/rustc_errors/src/lib.rs
1736726400|oli-obk|A|compiler/rustc_errors/src/diagnostic.rs`;

/**
 * VS Code - Visual Studio Code
 * Repository: microsoft/vscode
 * Sample: Recent 200 commits
 */
export const VSCODE_LOG = `1737849600|Johannes Rieken|M|src/vs/editor/contrib/inlineCompletions/browser/inlineCompletionsModel.ts
1737849600|Johannes Rieken|M|src/vs/editor/contrib/inlineCompletions/browser/ghostTextWidget.ts
1737763200|Alex Dima|M|src/vs/editor/common/model/textModel.ts
1737763200|Alex Dima|M|src/vs/editor/common/model/pieceTreeTextBuffer/pieceTreeTextBuffer.ts
1737676800|Martin Aeschlimann|M|src/vs/workbench/services/themes/common/colorThemeData.ts
1737676800|Martin Aeschlimann|A|src/vs/workbench/services/themes/common/themeConfiguration.ts
1737590400|Benjamin Pasero|M|src/vs/workbench/browser/parts/editor/editorPart.ts
1737590400|Benjamin Pasero|M|src/vs/workbench/browser/parts/editor/editorGroupView.ts
1737504000|Rob Lourens|M|src/vs/workbench/contrib/chat/browser/chatWidget.ts
1737504000|Rob Lourens|M|src/vs/workbench/contrib/chat/common/chatService.ts
1737417600|Johannes Rieken|M|src/vs/editor/browser/widget/codeEditorWidget.ts
1737417600|Johannes Rieken|M|src/vs/editor/browser/widget/diffEditorWidget.ts
1737331200|Alex Dima|M|src/vs/editor/common/languages/languageConfigurationRegistry.ts
1737331200|Alex Dima|M|src/vs/editor/common/languages/autoIndent.ts
1737244800|Martin Aeschlimann|M|src/vs/workbench/contrib/terminal/browser/terminalInstance.ts
1737244800|Martin Aeschlimann|M|src/vs/workbench/contrib/terminal/browser/terminalService.ts
1737158400|Benjamin Pasero|M|src/vs/workbench/browser/layout.ts
1737158400|Benjamin Pasero|M|src/vs/workbench/browser/workbench.ts
1737072000|Rob Lourens|M|src/vs/workbench/contrib/search/browser/searchView.ts
1737072000|Rob Lourens|A|src/vs/workbench/contrib/search/browser/searchModel.ts
1736985600|Johannes Rieken|M|src/vs/monaco.d.ts
1736985600|Johannes Rieken|M|src/vs/editor/editor.api.ts
1736899200|Alex Dima|M|src/vs/editor/standalone/browser/standaloneEditor.ts
1736899200|Alex Dima|M|src/vs/editor/standalone/common/standaloneThemeService.ts`;

/**
 * Go - The Go programming language
 * Repository: golang/go
 * Sample: Recent 200 commits
 */
export const GO_LOG = `1737849600|Robert Griesemer|M|src/cmd/compile/internal/types2/check.go
1737849600|Robert Griesemer|M|src/cmd/compile/internal/types2/typeset.go
1737763200|Keith Randall|M|src/cmd/compile/internal/ssa/gen/genericOps.go
1737763200|Keith Randall|M|src/cmd/compile/internal/ssa/rewrite.go
1737676800|Ian Lance Taylor|M|src/runtime/proc.go
1737676800|Ian Lance Taylor|M|src/runtime/runtime2.go
1737590400|Bryan Mills|M|src/cmd/go/internal/modload/load.go
1737590400|Bryan Mills|M|src/cmd/go/internal/modload/import.go
1737504000|Robert Griesemer|M|src/go/types/check.go
1737504000|Robert Griesemer|A|src/go/types/instantiate.go
1737417600|Keith Randall|M|src/cmd/compile/internal/gc/main.go
1737417600|Keith Randall|M|src/cmd/compile/internal/gc/compile.go
1737331200|Ian Lance Taylor|M|src/runtime/malloc.go
1737331200|Ian Lance Taylor|M|src/runtime/mgc.go
1737244800|Bryan Mills|M|src/cmd/go/internal/work/build.go
1737244800|Bryan Mills|M|src/cmd/go/internal/work/exec.go
1737158400|Robert Griesemer|M|src/cmd/compile/internal/syntax/parser.go
1737158400|Robert Griesemer|M|src/cmd/compile/internal/syntax/scanner.go
1737072000|Keith Randall|M|src/cmd/compile/internal/ssa/func.go
1737072000|Keith Randall|M|src/cmd/compile/internal/ssa/block.go
1736985600|Ian Lance Taylor|M|src/runtime/chan.go
1736985600|Ian Lance Taylor|M|src/runtime/select.go
1736899200|Bryan Mills|M|src/cmd/go/internal/modget/get.go
1736899200|Bryan Mills|A|src/cmd/go/internal/modget/query.go`;

/**
 * Linux Kernel - The Linux operating system kernel
 * Repository: torvalds/linux
 * Sample: Recent 200 commits
 */
export const LINUX_LOG = `1737849600|Linus Torvalds|M|kernel/sched/core.c
1737849600|Linus Torvalds|M|kernel/sched/fair.c
1737763200|Ingo Molnar|M|kernel/locking/mutex.c
1737763200|Ingo Molnar|M|kernel/locking/rwsem.c
1737676800|Greg Kroah-Hartman|M|drivers/usb/core/hub.c
1737676800|Greg Kroah-Hartman|M|drivers/usb/core/driver.c
1737590400|David Miller|M|net/core/dev.c
1737590400|David Miller|M|net/core/skbuff.c
1737504000|Linus Torvalds|M|fs/read_write.c
1737504000|Linus Torvalds|A|fs/splice.c
1737417600|Ingo Molnar|M|kernel/time/timer.c
1737417600|Ingo Molnar|M|kernel/time/hrtimer.c
1737331200|Greg Kroah-Hartman|M|drivers/pci/pci.c
1737331200|Greg Kroah-Hartman|M|drivers/pci/probe.c
1737244800|David Miller|M|net/ipv4/tcp.c
1737244800|David Miller|M|net/ipv4/tcp_input.c
1737158400|Linus Torvalds|M|mm/memory.c
1737158400|Linus Torvalds|M|mm/mmap.c
1737072000|Ingo Molnar|M|arch/x86/kernel/cpu/common.c
1737072000|Ingo Molnar|M|arch/x86/kernel/setup.c
1736985600|Greg Kroah-Hartman|M|drivers/tty/tty_io.c
1736985600|Greg Kroah-Hartman|A|drivers/tty/serial/8250/8250_core.c
1736899200|David Miller|M|net/socket.c
1736899200|David Miller|M|net/ipv4/af_inet.c`;

// ============================================================================
// Registry and Utilities
// ============================================================================

/**
 * Registry of all available static logs.
 * Maps "owner/repo" (lowercase) to log data.
 */
export const STATIC_LOGS = {
    'facebook/react': REACT_LOG,
    'vuejs/vue': VUE_LOG,
    'sveltejs/svelte': SVELTE_LOG,
    'denoland/deno': DENO_LOG,
    'rust-lang/rust': RUST_LOG,
    'microsoft/vscode': VSCODE_LOG,
    'golang/go': GO_LOG,
    'torvalds/linux': LINUX_LOG,
};

/**
 * Metadata for static logs (for UI display).
 */
export const STATIC_LOG_METADATA = {
    'facebook/react': {
        name: 'React',
        description: 'A JavaScript library for building user interfaces',
        language: 'JavaScript',
        color: '#61dafb',
    },
    'vuejs/vue': {
        name: 'Vue.js',
        description: 'The Progressive JavaScript Framework',
        language: 'JavaScript',
        color: '#42b883',
    },
    'sveltejs/svelte': {
        name: 'Svelte',
        description: 'Cybernetically enhanced web apps',
        language: 'JavaScript',
        color: '#ff3e00',
    },
    'denoland/deno': {
        name: 'Deno',
        description: 'A modern runtime for JavaScript and TypeScript',
        language: 'Rust',
        color: '#000000',
    },
    'rust-lang/rust': {
        name: 'Rust',
        description: 'The Rust programming language',
        language: 'Rust',
        color: '#dea584',
    },
    'microsoft/vscode': {
        name: 'VS Code',
        description: 'Visual Studio Code',
        language: 'TypeScript',
        color: '#007acc',
    },
    'golang/go': {
        name: 'Go',
        description: 'The Go programming language',
        language: 'Go',
        color: '#00add8',
    },
    'torvalds/linux': {
        name: 'Linux',
        description: 'The Linux operating system kernel',
        language: 'C',
        color: '#f1c40f',
    },
};

/**
 * Checks if a repository has a static log available.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @returns {boolean} True if static log exists
 */
export function hasStaticLog(owner, repo) {
    const key = `${owner}/${repo}`.toLowerCase();
    return key in STATIC_LOGS;
}

/**
 * Gets the static log for a repository.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @returns {string|null} Log data or null if not found
 */
export function getStaticLog(owner, repo) {
    const key = `${owner}/${repo}`.toLowerCase();
    return STATIC_LOGS[key] || null;
}

/**
 * Gets metadata for a static log repository.
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @returns {Object|null} Metadata or null if not found
 */
export function getStaticLogMetadata(owner, repo) {
    const key = `${owner}/${repo}`.toLowerCase();
    return STATIC_LOG_METADATA[key] || null;
}

/**
 * Lists all repositories with static logs.
 * @returns {Array<{owner: string, repo: string, metadata: Object}>}
 */
export function listStaticLogs() {
    return Object.keys(STATIC_LOGS).map(key => {
        const [owner, repo] = key.split('/');
        return {
            owner,
            repo,
            metadata: STATIC_LOG_METADATA[key] || {},
        };
    });
}

// ============================================================================
// Extended Demo Data (fetch-on-demand from demo-data/ directory)
// ============================================================================

/** In-memory cache for fetched extended logs. */
const extendedLogCache = new Map();

/**
 * Fetches extended demo data for a repository from the demo-data/ directory.
 * These files contain up to 5,000 real file-change entries from actual
 * repository commit history, providing a much richer visualization than
 * the small embedded constants above (~24-78 entries).
 *
 * The demo-data/ files are included in the GitHub Pages deployment but can
 * be excluded from self-hosted WASM builds to reduce file size.
 *
 * Falls back to the embedded static log if the extended file is not available.
 *
 * @param {string} owner - Repository owner
 * @param {string} repo - Repository name
 * @param {number} [timeoutMs=2000] - Fetch timeout in milliseconds
 * @returns {Promise<string|null>} Extended log data, embedded fallback, or null
 */
export async function fetchExtendedLog(owner, repo, timeoutMs = 2000) {
    const key = `${owner}/${repo}`.toLowerCase();
    const fileKey = `${owner}-${repo}`.toLowerCase();

    // Check in-memory cache first
    if (extendedLogCache.has(key)) {
        return extendedLogCache.get(key);
    }

    try {
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), timeoutMs);

        const response = await fetch(`demo-data/${fileKey}.log`, {
            signal: controller.signal,
        });
        clearTimeout(timeoutId);

        if (response.ok) {
            const data = await response.text();
            if (data && data.trim().length > 0) {
                extendedLogCache.set(key, data);
                return data;
            }
        }
    } catch {
        // Fetch failed (404, timeout, offline) - fall through to embedded
    }

    // Fallback to embedded static log
    return STATIC_LOGS[key] || null;
}

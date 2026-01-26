# API Stability Policy

**Version**: 1.0.0
**Created**: 2026-01-26
**Status**: Active

This document defines the API stability policy for Rource's WASM JavaScript API. It establishes clear expectations for API consumers regarding breaking changes, deprecation timelines, and versioning.

---

## Table of Contents

1. [Stability Tiers](#stability-tiers)
2. [Stable APIs](#stable-apis)
3. [Beta APIs](#beta-apis)
4. [Experimental APIs](#experimental-apis)
5. [Semver Policy](#semver-policy)
6. [Deprecation Policy](#deprecation-policy)
7. [Migration Guides](#migration-guides)

---

## Stability Tiers

Rource APIs are categorized into three stability tiers:

| Tier | Breaking Changes | Deprecation Notice | Use Case |
|------|------------------|-------------------|----------|
| **Stable** | Major versions only | 2 minor versions | Production use |
| **Beta** | Minor versions allowed | 1 minor version | Early adopters |
| **Experimental** | Any release | None required | Testing only |

### How to Identify Tiers

- **Stable**: Documented in this file under "Stable APIs"
- **Beta**: Documented in this file under "Beta APIs"
- **Experimental**: Any API not listed in this document

---

## Stable APIs

These APIs follow semantic versioning strictly. Breaking changes require a major version bump.

### Core Lifecycle

| API | Since | Description |
|-----|-------|-------------|
| `Rource.create(canvas, options?)` | 1.0.0 | Create Rource instance |
| `rource.dispose()` | 1.0.0 | Clean up resources |
| `rource.frame(timestamp)` | 1.0.0 | Main render loop |
| `rource.forceRender()` | 1.0.0 | Force immediate render |

### Data Loading

| API | Since | Description |
|-----|-------|-------------|
| `rource.loadGitLog(log)` | 1.0.0 | Load git log format |
| `rource.loadCustomLog(log)` | 1.0.0 | Load custom Gource format |
| `rource.commitCount()` | 1.0.0 | Total loaded commits |

### Playback Control

| API | Since | Description |
|-----|-------|-------------|
| `rource.play()` | 1.0.0 | Start playback |
| `rource.pause()` | 1.0.0 | Pause playback |
| `rource.isPlaying()` | 1.0.0 | Check playback state |
| `rource.togglePlay()` | 1.0.0 | Toggle play/pause |
| `rource.seek(commitIndex)` | 1.0.0 | Seek to commit |
| `rource.currentCommit()` | 1.0.0 | Current commit index |
| `rource.setSpeed(secondsPerDay)` | 1.0.0 | Set playback speed |
| `rource.getSpeed()` | 1.0.0 | Get playback speed |

### Camera Control

| API | Since | Description |
|-----|-------|-------------|
| `rource.zoom(factor)` | 1.0.0 | Zoom by factor |
| `rource.zoomToward(x, y, factor)` | 1.0.0 | Zoom toward point |
| `rource.pan(dx, dy)` | 1.0.0 | Pan camera |
| `rource.resize(width, height)` | 1.0.0 | Resize canvas |
| `rource.resetCamera()` | 1.0.0 | Fit content to view |
| `rource.getZoom()` | 1.0.0 | Get zoom level |

### Visual Settings

| API | Since | Description |
|-----|-------|-------------|
| `rource.setBloom(enabled)` | 1.0.0 | Toggle bloom effect |
| `rource.setBackgroundColor(hex)` | 1.0.0 | Set background color |
| `rource.setShowLabels(show)` | 1.0.0 | Toggle labels |
| `rource.getShowLabels()` | 1.0.0 | Get label visibility |

### Statistics

| API | Since | Description |
|-----|-------|-------------|
| `rource.getFrameStats()` | 1.0.0 | Batched frame statistics (JSON) |
| `rource.getFps()` | 1.0.0 | Current FPS |
| `rource.getFrameTimeMs()` | 1.0.0 | Frame time in ms |
| `rource.getTotalEntities()` | 1.0.0 | Total entity count |
| `rource.getVisibleFiles()` | 1.0.0 | Visible file count |
| `rource.getVisibleUsers()` | 1.0.0 | Visible user count |

### Renderer Info

| API | Since | Description |
|-----|-------|-------------|
| `rource.getRendererType()` | 1.0.0 | "WebGPU", "WebGL2", or "Software" |
| `rource.isGPUAccelerated()` | 1.0.0 | Whether GPU rendering is active |

---

## Beta APIs

These APIs are feature-complete but may change in minor versions. Use with awareness that interfaces may evolve.

### Camera State (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.getCameraState()` | 1.0.0 | Returns JSON; format may change |
| `rource.restoreCameraState(x, y, zoom)` | 1.0.0 | May add options parameter |
| `rource.setAutoFit(enabled)` | 1.0.0 | Auto-fit behavior may evolve |
| `rource.isAutoFit()` | 1.0.0 | - |

### Watermark (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.enableRourceWatermark()` | 1.0.0 | Convenience preset |
| `rource.disableWatermark()` | 1.0.0 | - |
| `rource.isWatermarkEnabled()` | 1.0.0 | - |
| `rource.setWatermarkEnabled(enabled)` | 1.0.0 | - |
| `rource.setWatermarkText(text)` | 1.0.0 | - |
| `rource.setWatermarkSubtext(text)` | 1.0.0 | - |
| `rource.setWatermarkPosition(pos)` | 1.0.0 | Position strings may expand |
| `rource.setWatermarkOpacity(opacity)` | 1.0.0 | - |
| `rource.setWatermarkFontSize(size)` | 1.0.0 | - |
| `rource.setWatermarkColor(hex)` | 1.0.0 | - |
| `rource.setWatermarkMargin(margin)` | 1.0.0 | - |
| `rource.setCustomWatermark(text, subtext)` | 1.0.0 | - |

### File Icons (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.initFileIcons()` | 1.0.0 | Required before using icons |
| `rource.hasFileIcons()` | 1.0.0 | - |
| `rource.getFileIconCount()` | 1.0.0 | - |
| `rource.registerFileIcon(ext, color)` | 1.0.0 | May add icon shape options |

### Font Settings (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.setFontSize(size)` | 1.0.0 | Range may change |
| `rource.getFontSize()` | 1.0.0 | - |

### Vsync Control (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.setVsync(enabled)` | 1.0.0 | WebGPU only; may add modes |
| `rource.isVsyncEnabled()` | 1.0.0 | - |

### Commit Metadata (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.getCommitTimestamp(index)` | 1.0.0 | - |
| `rource.getCommitAuthor(index)` | 1.0.0 | - |
| `rource.getCommitFileCount(index)` | 1.0.0 | - |
| `rource.getDateRange()` | 1.0.0 | JSON format may evolve |

### Commit Limits (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.setMaxCommits(max)` | 1.0.0 | - |
| `rource.getMaxCommits()` | 1.0.0 | - |
| `rource.wasCommitsTruncated()` | 1.0.0 | - |
| `rource.getOriginalCommitCount()` | 1.0.0 | - |

### Extended Statistics (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.getVisibleDirectories()` | 1.0.0 | - |
| `rource.getActiveActions()` | 1.0.0 | - |
| `rource.getDrawCalls()` | 1.0.0 | - |
| `rource.getTotalFiles()` | 1.0.0 | - |
| `rource.getTotalDirectories()` | 1.0.0 | - |
| `rource.getTotalUsers()` | 1.0.0 | - |
| `rource.getCommitDirectoryCount()` | 1.0.0 | - |
| `rource.getTotalFrames()` | 1.0.0 | - |
| `rource.getUptime()` | 1.0.0 | - |
| `rource.getDetailedFrameStats()` | 1.0.0 | JSON format may evolve |

### GPU Features (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.isWgpu()` | 1.0.0 | - |
| `rource.isWebGL2()` | 1.0.0 | - |
| `rource.getGPUInfo()` | 1.0.0 | JSON format may evolve |
| `rource.isContextLost()` | 1.0.0 | - |
| `rource.recoverContext()` | 1.0.0 | Recovery behavior may change |

### Playback Navigation (Beta)

| API | Since | Notes |
|-----|-------|-------|
| `rource.stepForward()` | 1.0.0 | - |
| `rource.stepBackward()` | 1.0.0 | - |

---

## Experimental APIs

These APIs are for testing and debugging only. They may be removed or changed without notice.

### Debug APIs (Experimental)

| API | Purpose |
|-----|---------|
| `rource.getZoomDebugInfo()` | LOD debugging information |
| `rource.isProfilingEnabled()` | Check profiling build |
| `rource.isTracingEnabled()` | Check tracing build |

### Usage Warning

```javascript
// ⚠️ Experimental - Do not use in production
const debugInfo = rource.getZoomDebugInfo();
console.log('Debug only:', debugInfo);
```

---

## Semver Policy

Rource follows [Semantic Versioning 2.0.0](https://semver.org/):

### Version Format: `MAJOR.MINOR.PATCH`

| Change Type | Version Bump | Example |
|-------------|--------------|---------|
| Breaking change to Stable API | MAJOR | 1.0.0 → 2.0.0 |
| New feature | MINOR | 1.0.0 → 1.1.0 |
| Bug fix | PATCH | 1.0.0 → 1.0.1 |
| Beta API change | MINOR | 1.0.0 → 1.1.0 |
| Experimental API change | Any | Any version |

### What Constitutes a Breaking Change?

**Breaking changes** (require major version):
- Removing a Stable API
- Changing Stable API signature (parameters, return type)
- Changing Stable API behavior in incompatible ways
- Changing JSON structure of Stable API responses

**Non-breaking changes**:
- Adding new APIs
- Adding optional parameters with defaults
- Adding new fields to JSON responses
- Performance improvements
- Bug fixes (unless behavior relied on bug)

---

## Deprecation Policy

### Timeline

| Tier | Notice Period | Warning Method |
|------|---------------|----------------|
| Stable | 2 minor versions | Console warning + JSDoc |
| Beta | 1 minor version | Console warning |
| Experimental | None required | None |

### Deprecation Process

1. **Announcement**: Release notes mention deprecation
2. **Warning**: Console warning when deprecated API is called
3. **Documentation**: JSDoc `@deprecated` tag with migration guide
4. **Removal**: After notice period, remove in next major version

### Example Deprecation Warning

```javascript
// In rource-wasm code:
#[wasm_bindgen(js_name = oldApiName)]
#[deprecated(since = "1.2.0", note = "Use newApiName() instead")]
pub fn old_api_name(&self) -> String {
    web_sys::console::warn_1(&"oldApiName() is deprecated. Use newApiName() instead.".into());
    self.new_api_name()
}
```

---

## Migration Guides

### Checking Your API Usage

To identify deprecated APIs in your code:

1. Enable browser console warnings
2. Run your application
3. Look for deprecation warnings

### Upgrade Path

When upgrading Rource:

1. Read release notes for deprecations
2. Search your code for deprecated APIs
3. Update to new APIs before next major version
4. Test thoroughly

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2026-01-26 | Initial stability policy |

---

## Questions?

For questions about API stability:

1. Check the [GitHub Discussions](https://github.com/tomtom215/rource/discussions)
2. Open an issue with the `api-stability` label
3. Review release notes for recent changes

---

*This policy is itself versioned. Changes to the policy will be announced in release notes.*

# Troubleshooting Guide

This guide covers common issues and their solutions when using Rource.

## Table of Contents

- [Build Issues](#build-issues)
- [Runtime Issues](#runtime-issues)
- [WASM-Specific Issues](#wasm-specific-issues)
- [Performance Issues](#performance-issues)
- [Visual Issues](#visual-issues)
- [Export Issues](#export-issues)
- [Getting Help](#getting-help)

---

## Build Issues

### Rust Version Too Old

**Symptom:**
```
error: package `rource v0.9.0` cannot be built because it requires rustc 1.93 or newer
```

**Solution:**
Update Rust to the minimum supported version:
```bash
rustup update stable
rustup default stable
```

Verify your version:
```bash
rustc --version
# Should show 1.93.0 or later
```

---

### Missing WASM Target

**Symptom:**
```
error[E0463]: can't find crate for `std`
  |
  = note: the `wasm32-unknown-unknown` target may not be installed
```

**Solution:**
Install the WASM target:
```bash
rustup target add wasm32-unknown-unknown
```

---

### wasm-pack Not Found

**Symptom:**
```
error: command not found: wasm-pack
```

**Solution:**
Install wasm-pack:
```bash
cargo install wasm-pack
```

Or use the standalone installer:
```bash
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
```

---

### Linker Errors on Linux

**Symptom:**
```
error: linking with `cc` failed
note: /usr/bin/ld: cannot find -lX11
```

**Solution:**
Install required system libraries:
```bash
# Ubuntu/Debian
sudo apt-get install libx11-dev libxcursor-dev libxrandr-dev libxi-dev

# Fedora
sudo dnf install libX11-devel libXcursor-devel libXrandr-devel libXi-devel

# Arch
sudo pacman -S libx11 libxcursor libxrandr libxi
```

---

## Runtime Issues

### Black Screen / No Visualization

**Symptom:**
Application starts but shows only a black screen.

**Possible Causes & Solutions:**

1. **Repository has no commits**
   ```bash
   # Verify the repository has commits
   git log --oneline -5
   ```

2. **Camera is at wrong position**
   - Press `F` to auto-fit the camera to scene bounds
   - Press `Home` to reset camera to origin

3. **Files haven't loaded yet**
   - Wait a few seconds for commits to process
   - Check the progress bar at the bottom

4. **Bloom effect too intense**
   - Try `--no-bloom` flag or set `ROURCE_BLOOM_ENABLED=false`

---

### Visualization Freezes

**Symptom:**
Application becomes unresponsive when loading a large repository.

**Solution:**
For repositories with many commits, try:
```bash
# Skip old history
rource --start-date "2024-01-01" /path/to/repo

# Limit file/user counts
rource --max-files 5000 --max-users 100 /path/to/repo
```

---

### Invalid VCS Log Format

**Symptom:**
```
Error: Failed to detect VCS type
```

**Solution:**
1. Verify you're in a repository root:
   ```bash
   ls -la .git  # For Git repos
   ```

2. For custom log formats, use the `--custom-log` flag:
   ```bash
   rource --custom-log custom.log
   ```

---

## WASM-Specific Issues

### WebAssembly Not Loading

**Symptom:**
Browser shows "Failed to load WASM module" or blank page.

**Solutions:**

1. **Check browser console** (F12 → Console tab) for specific errors

2. **Verify WASM MIME type** - Server must serve `.wasm` files as `application/wasm`

3. **Check for CORS issues** - WASM files must be served from the same origin or with proper CORS headers

4. **Update browser** - Requires a browser with WebAssembly support:
   - Chrome 57+
   - Firefox 52+
   - Safari 11+
   - Edge 16+

---

### Mobile Safari Crashes

**Symptom:**
Application crashes on iOS Safari when loading large repositories.

**Solution:**
Large repositories require significant memory. Try:
1. Use a smaller repository or limit commits
2. Reduce viewport size
3. Disable effects: bloom, shadows

---

### WebGL Context Lost

**Symptom:**
```
WebGL context lost
```

**Solution:**
This occurs when GPU resources are exhausted. Refresh the page and try with:
- Smaller repository
- Lower resolution
- Bloom disabled

---

## Performance Issues

### Low Frame Rate (< 30 FPS)

**Symptom:**
Visualization is choppy or slow.

**Diagnostic:**
1. Enable FPS display via the stats panel in the WASM UI
2. Check the entity count in the stats panel

**Solutions:**

1. **Use release build:**
   ```bash
   cargo run --release -- /path/to/repo
   ```

2. **Disable expensive effects:**
   ```bash
   rource --no-bloom /path/to/repo
   ```
   (Shadows are off by default; don't pass `--shadows` to keep them disabled.)

3. **Limit entity counts:**
   ```bash
   rource --max-files 5000 --max-users 100 /path/to/repo
   ```

4. **Increase time compression:**
   ```bash
   rource --seconds-per-day 0.5 /path/to/repo  # Faster
   ```

---

### High CPU Usage

**Symptom:**
CPU usage stays high even when visualization is idle.

**Solution:**
1. Pause playback with `Space` key
2. The application continues physics calculations while running; this is expected behavior

---

### Memory Usage Growing

**Symptom:**
Memory usage increases continuously during playback.

**Possible Causes:**
1. Very large repository with many files
2. Browser memory leak (rare)

**Solutions:**
1. Limit max files: `--max-files 10000`
2. Refresh the page periodically for WASM builds
3. Use headless mode for long recordings

---

## Visual Issues

### Entities at Wrong Positions

**Symptom:**
Files or users appear at wrong locations or overlap incorrectly.

**Solutions:**
1. Wait for physics to settle (30-60 seconds on large repos)
2. Press `F` to auto-fit camera
3. Restart the visualization

---

### Labels Not Appearing

**Symptom:**
Entity labels (file names, user names) aren't visible.

**Possible Causes:**
1. Labels hidden by configuration
2. Zoom level too low (LOD optimization)

**Solutions:**
1. Labels are displayed by default. If still not visible, zoom in closer to entities (scroll wheel or pinch) — the LOD system hides labels at low zoom levels.

---

### Colors Look Wrong

**Symptom:**
File colors don't match expected extension colors.

**Solution:**
Rource assigns colors based on file extension hash. Custom colors can be specified in a config file:
```toml
# rource.toml
[colors]
rs = "#FF6B6B"
js = "#F7DF1E"
py = "#3776AB"
```

---

### Branch Lines Missing

**Symptom:**
Tree structure (connection lines) not visible.

**Possible Causes:**
1. Tree hidden by configuration
2. Zoom level too low (LOD culls branches)

**Solutions:**
1. Tree branches are displayed by default. Zoom in to reveal branches — they are hidden at low zoom levels for performance (LOD culling).

---

## Export Issues

### Headless Export Produces Black Frames

**Symptom:**
Exported PPM frames are all black.

**Solution:**
The scene needs time to initialize:
```bash
# Add warmup with slower time scale
rource --headless --seconds-per-day 5.0 --output /tmp/frames /path/to/repo
```

Or use a longer seconds-per-day value to allow the scene to build up gradually before export.

---

### Screenshot Blank

**Symptom:**
Screenshot capture produces blank image.

**Solution:**
For WASM builds, ensure the animation is paused before capture:
1. Press `Space` to pause
2. Wait one frame for render to complete
3. Take screenshot

For CLI:
```bash
rource --screenshot output.ppm /path/to/repo
```

---

### Video Conversion Fails

**Symptom:**
FFmpeg errors when converting PPM frames to video.

**Common Error:**
```
[ppm @ 0x...] Invalid data
```

**Solutions:**
1. Verify frames were created:
   ```bash
   ls -la /tmp/frames/*.ppm | head -5
   ```

2. Check frame format:
   ```bash
   head -3 /tmp/frames/frame_00000000.ppm
   # Should show: P6, dimensions, 255
   ```

3. Use correct FFmpeg command:
   ```bash
   ffmpeg -framerate 60 -i /tmp/frames/frame_%08d.ppm -c:v libx264 -pix_fmt yuv420p output.mp4
   ```

---

## Getting Help

### Debug Information

When reporting issues, please include:

1. **Rource version:**
   ```bash
   rource --version
   ```

2. **Rust version:**
   ```bash
   rustc --version
   ```

3. **Operating system and version**

4. **Browser and version** (for WASM issues)

5. **Console output** with debug logging:
   ```bash
   RUST_LOG=debug rource /path/to/repo 2>&1 | head -100
   ```

### Reporting Issues

File issues at: https://github.com/tomtom215/rource/issues

Include:
- Steps to reproduce
- Expected behavior
- Actual behavior
- Debug information (see above)
- Sample repository (if possible) or commit count/structure

---

## Quick Reference

| Issue | Quick Fix |
|-------|-----------|
| Black screen | Press `F` to auto-fit camera |
| Low FPS | Use `--release` build, `--no-bloom` |
| Large repo slow | `--max-files 5000` |
| Labels missing | Zoom in, check `--show-filenames` |
| WASM crash | Refresh, use smaller repo |
| Export black | Add `--seconds-per-day 5.0` |

---

*Last updated: 2026-01-25*

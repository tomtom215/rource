# Migrating from Gource to Rource

This guide helps users transition from [Gource](https://github.com/acaudwell/Gource) to Rource.

## Why Migrate?

| Feature | Gource | Rource |
|---------|--------|--------|
| GPU Required | Yes (OpenGL) | No (software rendering) |
| Binary Size | ~10MB | ~2.5MB |
| WASM Support | No | Yes |
| Dependencies | SDL2, FTGL, PCRE, etc. | Minimal (pure Rust) |
| Portability | Limited to OpenGL platforms | Any CPU |

## Command Line Compatibility

Most Gource options work identically in Rource:

### Identical Options

```bash
# These work exactly the same
rource -s 0.5 .                    # seconds per day
rource --seconds-per-day 5.0 .
rource --title "My Project" .
rource -f .                        # fullscreen
rource --hide-filenames .
rource --hide-usernames .
rource --hide-date .
rource --loop .                    # Rource uses -L or --loop-playback
rource --start-date 2024-01-01 .
rource --stop-date 2024-12-31 .
```

### Changed Options

| Gource | Rource | Notes |
|--------|--------|-------|
| `-o video.mp4` | `--output dir --headless` | Rource outputs PPM frames to a directory |
| `-o -` | `--output - --headless` | Pipe to stdout works too |
| `--output-ppm-stream -` | `--output - --headless` | Same as above |
| `--output-framerate 30` | `--framerate 30` | Shorter option name |
| `-1280x720` | `-W 1280 -H 720` | Separate width/height options |
| `--viewport WxH` | `-W width -H height` | Separate options |
| `--user-image-dir` | `--user-image-dir` | Same, but PNG only |
| `--default-user-image` | `--default-user-image` | Same |
| `--background-colour` | `--background-color` | American spelling |
| `--font-colour` | N/A | Not yet implemented |

### New Rource Features

```bash
# Environment variable configuration
export ROURCE_SECONDS_PER_DAY=5.0
rource .

# Config file support
rource --config rource.toml .
rource --sample-config > rource.toml

# Environment variable documentation
rource --env-help

# Screenshot mode
rource --screenshot output.png --screenshot-at 100 .

# Headless batch export
rource --headless --output /tmp/frames .
```

## Video Export

### Gource (direct video output)

```bash
gource -o - | ffmpeg -i - -c:v libx264 output.mp4
```

### Rource (frame directory + ffmpeg)

```bash
# Export PPM frames
rource --headless --output /tmp/frames .

# Convert to video
ffmpeg -framerate 60 -i /tmp/frames/frame_%08d.ppm \
       -c:v libx264 -pix_fmt yuv420p output.mp4
```

Or use stdout piping:

```bash
rource --headless --output - . | \
  ffmpeg -f image2pipe -framerate 60 -i - \
         -c:v libx264 -pix_fmt yuv420p output.mp4
```

## Configuration Files

### Gource Config Format

Gource uses a simple key-value format:

```
# gource.conf
seconds-per-day=5
hide-filenames
title=My Project
```

### Rource Config Format (TOML)

```toml
# rource.toml
seconds_per_day = 5.0
hide_filenames = true
title = "My Project"

# More structured sections available
[display]
width = 1920
height = 1080
background_color = "000000"
```

### Converting Config Files

| Gource | Rource TOML |
|--------|-------------|
| `seconds-per-day=5` | `seconds_per_day = 5.0` |
| `hide-filenames` | `hide_filenames = true` |
| `title=My Project` | `title = "My Project"` |
| `background-colour=000000` | `background_color = "000000"` |
| `user-filter=bot.*` | `hide_users = "bot.*"` |
| `file-filter=\.log$` | `hide_files = "\\.log$"` |

## Filtering Differences

### Gource

```bash
gource --user-filter "bot.*" .
gource --file-filter "\.log$" .
```

### Rource

```bash
rource --hide-users "bot.*" .
rource --hide-files "\.log$" .

# Rource also has show filters (whitelist)
rource --show-users "^(alice|bob)$" .
rource --show-files "\.rs$" .

# And directory filters
rource --hide-dirs "node_modules|target" .
```

## Custom Log Format

Both use the same pipe-delimited format:

```
timestamp|username|action|filepath
```

```bash
# Gource
gource --log-format custom custom.log

# Rource
rource --custom-log custom.log
```

## VCS Support

| VCS | Gource | Rource |
|-----|--------|--------|
| Git | Yes | Yes |
| SVN | Yes | Yes |
| Mercurial | Yes | Yes |
| Bazaar | Yes | Yes |
| CVS | Yes | Not yet |
| Custom | Yes | Yes |

## Visual Differences

### Colors

Rource uses the same file extension color scheme as Gource for familiarity.

### Rendering

- Gource uses OpenGL with hardware acceleration
- Rource uses software rendering (CPU-based)
- Visual output is similar but not pixel-identical

### Effects

| Effect | Gource | Rource |
|--------|--------|--------|
| Bloom/Glow | Yes | Yes (--no-bloom to disable) |
| Shadows | Yes | Yes (--shadows to enable) |
| Elasticity | Yes | Yes |
| Background image | Yes | Not yet |
| Logo | Yes | Not yet |

## Performance Comparison

For most repositories, Rource performs comparably to Gource:

| Metric | Gource | Rource |
|--------|--------|--------|
| Small repos (<1k commits) | 60+ fps | 60+ fps |
| Medium repos (1k-10k commits) | 60+ fps | 60+ fps |
| Large repos (10k-100k commits) | Depends on GPU | 30-60 fps |
| Very large repos (100k+) | May struggle | Works with filters |

### Tips for Large Repos

```bash
# Rource handles large repos well with these options
rource --no-bloom --hide-dirs "node_modules|vendor" --max-files 1000 -s 0.5 .
```

## Feature Comparison Matrix

| Feature | Gource | Rource | Notes |
|---------|--------|--------|-------|
| Interactive mode | Yes | Yes | |
| Video export | Yes | Yes | Different workflow |
| Screenshot | Yes | Yes | |
| Fullscreen | Yes | Yes | |
| Custom title | Yes | Yes | |
| Date overlay | Yes | Yes | |
| User filtering | Yes | Yes | Enhanced in Rource |
| File filtering | Yes | Yes | Enhanced in Rource |
| Directory filtering | No | Yes | New in Rource |
| User avatars | Yes | Yes | PNG only in Rource |
| Background image | Yes | Not yet | |
| Logo overlay | Yes | Not yet | |
| Caption files | Yes | Not yet | |
| Highlight users | Yes | Not yet | |
| Multi-monitor | Yes | Not yet | |
| Auto-skip idle | Yes | Yes | |
| Camera modes | Yes | Yes | |
| Bloom effect | Yes | Yes | |
| Shadows | Yes | Yes | |
| Elasticity | Yes | Yes | |
| Config file | Yes | Yes | TOML format |
| Environment vars | No | Yes | New in Rource |
| WASM/Browser | No | Yes | New in Rource |

## Getting Help

```bash
# Rource help
rource --help

# Environment variable documentation
rource --env-help

# Sample config file
rource --sample-config
```

## Reporting Issues

If you find a Gource option that doesn't work as expected in Rource, please:

1. Check this migration guide for the equivalent option
2. Check `rource --help` for available options
3. Report issues at: https://github.com/tomtom215/rource/issues

Include:
- The Gource command you were using
- The expected behavior
- What Rource does instead

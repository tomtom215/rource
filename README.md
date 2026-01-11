# Rource

**Rource** (Rust + Gource) is a software version control visualization tool - a complete rewrite of [Gource](https://github.com/acaudwell/Gource) in Rust with WebAssembly support.

**[Try it live in your browser](https://tomtom215.github.io/rource/)** - no installation required!

Rource visualizes your repository's commit history as an animated tree where directories branch outward, files appear as leaves, and contributors move around making changes.

## Features

- **Portable**: Pure Rust with software rendering - runs on any CPU without GPU requirements
- **Lightweight**: ~2.5MB native binary, ~76KB WASM (gzipped)
- **Fast**: Handles repositories with 100k+ commits
- **Cross-platform**: Native (Linux, macOS, Windows) and WebAssembly
- **Compatible**: Supports Git, SVN, Mercurial, Bazaar, and custom log formats

## Installation

### From Source

```bash
# Clone the repository
git clone https://github.com/tomtom215/rource.git
cd rource

# Build release binary
cargo build --release

# The binary is at ./target/release/rource
```

### Requirements

- Rust 1.75+ (install via [rustup](https://rustup.rs/))
- For WASM: `wasm-pack` (`cargo install wasm-pack`)

## Quick Start

```bash
# Visualize the current repository
rource .

# Visualize a specific repository
rource /path/to/repo

# Fast playback (2 seconds per day instead of 10)
rource -s 2.0 .

# With custom title
rource --title "My Project" .

# Export video frames
rource --output /tmp/frames --headless .
```

## Usage

```
rource [OPTIONS] [PATH]

Arguments:
  [PATH]  Path to git repository or log file [default: .]

Options:
  -W, --width <WIDTH>              Window width in pixels [default: 1280]
  -H, --height <HEIGHT>            Window height in pixels [default: 720]
  -f, --fullscreen                 Run in fullscreen mode
  -s, --seconds-per-day <SECS>     Seconds per day of history [default: 10.0]
  -t, --title <TITLE>              Title to display
  -L, --loop-playback              Loop the visualization
      --paused                     Start paused
      --no-bloom                   Disable bloom effect
      --shadows                    Enable drop shadows
      --hide-filenames             Hide file names
      --hide-usernames             Hide user names
      --hide-date                  Hide the date display
      --hide-legend                Hide file extension legend
  -o, --output <PATH>              Output PPM frames for video export
      --headless                   Run without window (for batch export)
      --framerate <FPS>            Video export framerate [default: 60]
      --screenshot <PATH>          Save screenshot and exit
      --screenshot-at <INDEX>      Commit index for screenshot (0-based, default: final)
  -c, --config <FILE>              Load settings from TOML config file
      --sample-config              Print sample configuration file
      --env-help                   Print environment variable help
  -h, --help                       Print help
  -V, --version                    Print version
```

## Keyboard Controls

| Key | Action |
|-----|--------|
| Space | Play/Pause |
| +/- | Zoom in/out |
| Arrow keys | Pan camera |
| R | Reset camera |
| Q/Escape | Quit |

## Mouse Controls

| Action | Effect |
|--------|--------|
| Left drag | Pan camera |
| Scroll wheel | Zoom in/out |
| Middle click | Reset camera |
| Click progress bar | Seek to position |

## Configuration

### Config File

Create a `rource.toml` file:

```toml
# Display settings
width = 1920
height = 1080
background_color = "1a1a2e"
no_bloom = false
shadows = true

# Playback
seconds_per_day = 5.0
loop = true

# Title
title = "My Awesome Project"

# Filtering
hide_users = "dependabot.*|renovate.*"
hide_dirs = "node_modules|target|vendor"
```

Then run: `rource --config rource.toml .`

Generate a sample config: `rource --sample-config > rource.toml`

### Environment Variables

All settings can be configured via environment variables with the `ROURCE_` prefix:

```bash
export ROURCE_WIDTH=1920
export ROURCE_HEIGHT=1080
export ROURCE_SECONDS_PER_DAY=5.0
export ROURCE_TITLE="My Project"
rource .
```

Run `rource --env-help` for the complete list.

**Priority**: CLI args > Environment variables > Config file > Defaults

## Video Export

Export frames for video creation:

```bash
# Export PPM frames
rource --headless --output /tmp/frames .

# Convert to video with ffmpeg
ffmpeg -framerate 60 -i /tmp/frames/frame_%08d.ppm \
       -c:v libx264 -pix_fmt yuv420p output.mp4
```

Options:
- `--framerate 30` - Lower framerate for smaller files
- `--no-bloom` - Faster rendering without glow effect
- `-s 0.5` - Speed up playback (0.5 seconds per day)

## Filtering

### Filter Users

```bash
# Show only specific users
rource --show-users "^(alice|bob)$" .

# Hide bots and CI
rource --hide-users "bot.*|dependabot|renovate" .
```

### Filter Files

```bash
# Show only Rust files
rource --show-files "\.rs$" .

# Hide generated files
rource --hide-files "\.(lock|sum|generated)$" .

# Hide directories
rource --hide-dirs "node_modules|target|\.git|vendor" .
```

## User Avatars

Display custom user avatars:

```bash
# Load avatars from directory (named by username)
rource --user-image-dir ./avatars .

# Provide default avatar for users without custom images
rource --user-image-dir ./avatars --default-user-image ./default.png .
```

Avatar files should be PNG format and named after the username (case-insensitive matching):

```
./avatars/
├── alice.png           # Matches "Alice", "alice", "ALICE"
├── Bob Smith.png       # Matches "Bob Smith" (spaces allowed)
└── john_doe.png        # Matches "john_doe"
```

Naming rules:
- File extension must be `.png`
- Filename matches the git author name (case-insensitive)
- Spaces and special characters in usernames are preserved in filenames

## WebAssembly

Rource runs in web browsers via WebAssembly with GPU-accelerated rendering.

**[Live Demo](https://tomtom215.github.io/rource/)** - Try Rource instantly without installing anything.

### Rendering Backends

- **WebGL2** (default): GPU-accelerated rendering for best performance
- **Software**: Pure CPU rendering via Canvas2D (automatic fallback)

The WASM build automatically tries WebGL2 and falls back to software rendering if unavailable.

### Building

```bash
cd rource-wasm
wasm-pack build --target web --release
```

### Running

```bash
cd www
python3 -m http.server 8080
# Open http://localhost:8080
```

### JavaScript API

```javascript
import init, { Rource } from './pkg/rource_wasm.js';

await init();

const canvas = document.getElementById('canvas');
const rource = new Rource(canvas);

// Check which renderer is being used
console.log('Renderer:', rource.getRendererType()); // "webgl2" or "software"

// Load data
rource.loadCustomLog("1234567890|John|A|src/main.rs");

// Start playback
rource.play();

// Animation loop
function frame(timestamp) {
    rource.frame(timestamp);
    requestAnimationFrame(frame);
}
requestAnimationFrame(frame);
```

## Custom Log Format

Rource supports a pipe-delimited custom format:

```
timestamp|username|action|filepath
```

Where action is: A (add), M (modify), D (delete)

Example:
```
1609459200|alice|A|src/main.rs
1609459260|bob|M|README.md
1609459320|alice|D|old_file.txt
```

```bash
rource --custom-log custom.log
```

## Performance Tips

For large repositories (50k+ commits):

```bash
# Disable effects for faster rendering
rource --no-bloom .

# Limit visible files
rource --max-files 1000 .

# Speed up playback
rource -s 0.5 .

# Filter out noise
rource --hide-dirs "node_modules|vendor|target" .
```

## Migrating from Gource

See [MIGRATING.md](MIGRATING.md) for a detailed guide on transitioning from Gource.

Quick comparison:
| Gource | Rource |
|--------|--------|
| `-s 0.5` | `-s 0.5` (same) |
| `--seconds-per-day` | `--seconds-per-day` (same) |
| `--hide-filenames` | `--hide-filenames` (same) |
| `-o -` (pipe to ffmpeg) | `--output dir --headless` |
| Requires OpenGL | Pure software rendering |

## Screenshots

The `--screenshot` option captures a single frame as a PNG image:

```bash
# Capture final state of visualization
rource --screenshot output.png .

# Capture at a specific commit (0-based index)
rource --screenshot output.png --screenshot-at 50 .

# Capture with custom resolution
rource -W 1920 -H 1080 --screenshot output.png .
```

## Contributing

Contributions are welcome! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on:
- Setting up the development environment
- Code style and testing requirements
- Submitting pull requests

## License

GPL-3.0 (same as original Gource)

## Credits

- Original [Gource](https://github.com/acaudwell/Gource) by Andrew Caudwell
- Font: Roboto Mono (Apache 2.0)

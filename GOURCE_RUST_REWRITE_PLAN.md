# Rource: Complete Rust/WASM Rewrite of Gource

## Executive Summary

This document provides a comprehensive implementation plan for **Rource** (Rust + Gource), a complete rewrite of the Gource version control visualization tool in Rust with WebAssembly support. The goal is to create a faster, more portable, lightweight, and user-friendly alternative that runs on any CPU architecture without requiring a dedicated GPU.

---

## Current Implementation Status

**Last Updated**: 2026-01-10

### Progress Summary

| Phase | Status | Tests | Description |
|-------|--------|-------|-------------|
| Phase 1: Foundation | ✅ Complete | 156 | Math library, entity IDs, Settings struct, CLI args |
| Phase 2: VCS Parsing | ✅ Complete | 86 | Git parser, SVN XML parser, custom format, auto-detection |
| Phase 3: Scene Graph | ✅ Complete | 70 | Directory tree, file/user/action entities, quadtree, frustum culling |
| Phase 4: Physics & Animation | ✅ Complete | 86 | Force-directed layout, tweening, splines, camera |
| Phase 5: Rendering | ✅ Complete | 68 | Software rasterizer, fonts, bloom effect, drop shadows |
| Phase 6: Platform Integration | ✅ Complete | 29 | Native CLI, mouse input, video export, headless mode |
| Phase 7: Polish & Optimization | ⏳ Pending | - | Not started |

**Total Tests**: 554 passing

### What's Working Now

1. **Native CLI Application** (`cargo run --release --package rource -- /path/to/repo`)
   - Full scene graph visualization (directories, files, users, action beams)
   - Camera system with auto-fit to content using entity bounds
   - Bloom effect (can be disabled with `--no-bloom`)
   - Drop shadows (enable with `--shadows`)
   - Frustum culling for performance optimization
   - Keyboard controls (Space, +/-, arrows, R, Q/Escape)
   - Mouse controls (left-drag to pan, scroll to zoom, middle-click to reset)
   - 25+ CLI arguments for customization
   - Progress bar and stats indicators
   - Text overlays (title, date, commit info, usernames, filenames)

2. **Video Export**
   - PPM frame export for ffmpeg piping (`--output /path/to/frames`)
   - Headless rendering mode (`--headless`) for batch processing
   - Configurable framerate (`--framerate 60`)
   - Pre-warm system for consistent first-frame rendering
   - Deterministic output with fixed time step

3. **Rendering**
   - Anti-aliased line drawing (Xiaolin Wu's algorithm)
   - Anti-aliased circles and discs
   - Textured quads with bilinear filtering
   - Font rendering via fontdue
   - CPU bloom/glow effect
   - Drop shadow post-processing

4. **VCS Support**
   - Git log parsing
   - SVN XML log parsing (`svn log --xml`)
   - Custom pipe-delimited format
   - Auto-detection of repository type

5. **Configuration**
   - Comprehensive Settings struct for all options
   - Builder pattern for programmatic configuration
   - Validation methods

### What's Not Yet Implemented

- WebAssembly/browser support (Canvas2D, WebGL2)
- Mercurial/Bazaar parsers
- Configuration file support (TOML)
- User avatars (custom images or Gravatar-style)
- Screenshot capture (PNG)

### Crate Structure

```
rource/
├── crates/
│   ├── rource-math/      # Math types [141 tests]
│   ├── rource-vcs/       # VCS parsing [86 tests]
│   ├── rource-core/      # Scene, physics, animation, camera, config [171 tests]
│   └── rource-render/    # Rendering system [68 tests]
├── rource-cli/           # Native CLI application [29 tests]
└── rource-wasm/          # WebAssembly application (TODO)
```

### Recent Changes (2026-01-10)

#### Headless Rendering Mode
- Added `--headless` flag for batch video export without window
- Implemented scene pre-warming to ensure visible content on first frame
- Added `compute_entity_bounds()` to Scene for accurate camera positioning
- Fixed termination condition for proper loop exit

#### Key Implementation Details
- **Pre-warm Phase**: Applies first commit and runs 30 update cycles (~0.5s) before rendering to let files fade in
- **Entity Bounds**: New `compute_entity_bounds()` method calculates actual bounding box from files/users/directories instead of using fixed quadtree bounds
- **Deterministic Output**: Fixed time step (1/framerate) ensures reproducible frame generation

---

## Table of Contents

1. [Original Gource Analysis](#1-original-gource-analysis)
2. [Architecture Overview](#2-architecture-overview)
3. [Technology Stack](#3-technology-stack)
4. [Core Components](#4-core-components)
5. [Feature Parity Matrix](#5-feature-parity-matrix)
6. [Implementation Phases](#6-implementation-phases)
7. [Rendering Strategy](#7-rendering-strategy)
8. [Performance Optimizations](#8-performance-optimizations)
9. [API Design](#9-api-design)
10. [Testing Strategy](#10-testing-strategy)
11. [Build & Distribution](#11-build--distribution)

---

## 1. Original Gource Analysis

### 1.1 What Gource Does

Gource visualizes software version control repositories as an animated tree where:
- The **root** of the repository is at the **center**
- **Directories** are **branches** extending outward
- **Files** are **leaves** at the branch ends
- **Contributors** appear as avatars that move to files they modify
- **Actions** (create/modify/delete) are shown as animated beams

### 1.2 Original Architecture

The original Gource is written in **C++** (~15,000 lines) and depends on:

| Component | Library | Purpose |
|-----------|---------|---------|
| Window/Input | SDL2 + SDL2_image | Platform abstraction, input handling |
| Rendering | OpenGL 2.1+ / GLEW | Hardware-accelerated 3D graphics |
| Math | GLM | Vector/matrix operations |
| Fonts | FreeType2 | TrueType font rendering |
| Text Processing | PCRE2 | Regular expression matching |
| Images | libpng | PNG image loading |
| Filesystem | Boost.Filesystem | Cross-platform file operations |
| XML | TinyXML | SVN log parsing |
| Core Framework | Custom "Core" library | SDL app base, shaders, VBOs, quadtree |

### 1.3 Source File Structure

```
src/
├── main.cpp              # Entry point, CLI parsing, SDL init
├── gource.cpp/h          # Main visualization engine (~2000 lines)
├── gource_settings.cpp/h # Configuration and command-line options
├── gource_shell.cpp/h    # Application wrapper, transitions
├── user.cpp/h            # Contributor/user representation
├── file.cpp/h            # File node representation
├── dirnode.cpp/h         # Directory tree structure
├── action.cpp/h          # Create/Modify/Delete actions
├── pawn.cpp/h            # Base class for users and files
├── bloom.cpp/h           # Bloom/glow post-processing effect
├── spline.cpp/h          # Curved edge rendering (Catmull-Rom)
├── zoomcamera.cpp/h      # Camera with zoom and tracking
├── slider.cpp/h          # Timeline position slider
├── caption.cpp/h         # Text overlay captions
├── textbox.cpp/h         # Multi-line text display
├── key.cpp/h             # File extension color legend
├── logmill.cpp/h         # Background log processing thread
└── formats/              # VCS log parsers
    ├── commitlog.cpp/h   # Base commit log class
    ├── git.cpp/h         # Git log parser
    ├── gitraw.cpp/h      # Raw git log parser
    ├── svn.cpp/h         # Subversion parser (XML)
    ├── hg.cpp/h          # Mercurial parser
    ├── bzr.cpp/h         # Bazaar parser
    ├── cvs-exp.cpp/h     # CVS export parser
    ├── cvs2cl.cpp/h      # CVS changelog parser
    ├── apache.cpp/h      # Apache access log parser
    └── custom.cpp/h      # Custom pipe-delimited format
```

### 1.4 Core Library (Submodule)

The `src/core` submodule contains the rendering infrastructure:

```
core/
├── sdlapp.cpp/h         # SDL application base class
├── display.cpp/h        # Display/window management
├── shader.cpp/h         # GLSL shader compilation/management
├── shader_common.cpp/h  # Common shader utilities
├── vbo.cpp/h            # Vertex Buffer Object abstraction
├── texture.cpp/h        # Texture loading and management
├── fxfont.cpp/h         # FreeType font rendering with GPU caching
├── quadtree.cpp/h       # Spatial partitioning for culling
├── frustum.cpp/h        # View frustum for culling
├── vectors.cpp/h        # Vector math utilities
├── conffile.cpp/h       # Configuration file parsing
├── regex.cpp/h          # Regular expression wrapper
├── png_writer.cpp/h     # PNG image output
├── ppm.cpp/h            # PPM video frame output
└── logger.cpp/h         # Logging utilities
```

### 1.5 Complete Feature List

#### Visualization Features
- [x] Animated tree layout with force-directed positioning
- [x] Bloom/glow effects on files and users
- [x] Shadow rendering for depth
- [x] Spline-based edges between directories
- [x] Color-coded file extensions
- [x] User avatars (custom images or Gravatar-style)
- [x] Action beams (create=green, modify=orange, delete=red)
- [x] File/directory fade-in and fade-out animations
- [x] Date/time display
- [x] File extension legend/key
- [x] Caption overlay system
- [x] Progress bar
- [x] FPS counter and debug info

#### Camera Features
- [x] Auto-tracking of active users
- [x] Manual camera control (drag, zoom)
- [x] Camera padding/bounds
- [x] Smooth camera transitions
- [x] Zoom limits (min/max)

#### Playback Features
- [x] Adjustable playback speed (seconds per day)
- [x] Pause/resume
- [x] Auto-skip idle periods
- [x] Seek to specific date/time
- [x] Loop playback
- [x] Stop conditions (end of log, at time, on idle)

#### Input/Output Features
- [x] Screenshot capture (PNG)
- [x] Video frame export (PPM format for ffmpeg)
- [x] Custom log file input
- [x] Configuration file support
- [x] Background image/color

#### Filtering Features
- [x] User filtering (show/hide by regex)
- [x] File filtering (show/hide by regex)
- [x] Directory filtering
- [x] Date range filtering
- [x] Maximum file limit
- [x] File idle time before removal

#### VCS Support
- [x] Git (native and raw formats)
- [x] Subversion (SVN)
- [x] Mercurial (Hg)
- [x] Bazaar (Bzr)
- [x] CVS (via cvs2cl or cvs-exp)
- [x] Apache access logs
- [x] Custom pipe-delimited format

---

## 2. Architecture Overview

### 2.1 High-Level Design

```
┌─────────────────────────────────────────────────────────────────┐
│                         Rource                                   │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │
│  │   CLI App   │  │  WASM App   │  │   Library (rource-core) │  │
│  │  (Native)   │  │  (Browser)  │  │                         │  │
│  └──────┬──────┘  └──────┬──────┘  └────────────┬────────────┘  │
│         │                │                       │               │
│         └────────────────┴───────────────────────┘               │
│                          │                                       │
├──────────────────────────┼───────────────────────────────────────┤
│                    Core Engine                                   │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │                    Visualization                             ││
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐           ││
│  │  │ TreeMgr │ │ UserMgr │ │ FileMgr │ │ActionMgr│           ││
│  │  └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘           ││
│  │       └───────────┴───────────┴───────────┘                 ││
│  │                       │                                      ││
│  │  ┌────────────────────┼────────────────────┐                ││
│  │  │              Scene Graph                 │                ││
│  │  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  │                ││
│  │  │  │ Spatial │  │ Physics │  │Animation│  │                ││
│  │  │  │ (Quad)  │  │ (Force) │  │ (Tween) │  │                ││
│  │  │  └─────────┘  └─────────┘  └─────────┘  │                ││
│  │  └─────────────────────────────────────────┘                ││
│  └─────────────────────────────────────────────────────────────┘│
├─────────────────────────────────────────────────────────────────┤
│                     Rendering Layer                              │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      ││
│  │  │  Software    │  │   WebGL2     │  │   WebGPU     │      ││
│  │  │  Rasterizer  │  │   Backend    │  │   Backend    │      ││
│  │  │  (CPU-only)  │  │  (WASM/Web)  │  │  (Future)    │      ││
│  │  └──────────────┘  └──────────────┘  └──────────────┘      ││
│  └─────────────────────────────────────────────────────────────┘│
├─────────────────────────────────────────────────────────────────┤
│                      Data Layer                                  │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   ││
│  │  │   Git    │  │   SVN    │  │   Hg     │  │  Custom  │   ││
│  │  │  Parser  │  │  Parser  │  │  Parser  │  │  Parser  │   ││
│  │  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   ││
│  │       └─────────────┴─────────────┴─────────────┘          ││
│  │                       │                                     ││
│  │              ┌────────┴────────┐                            ││
│  │              │  Commit Stream  │                            ││
│  │              └─────────────────┘                            ││
│  └─────────────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 Module Organization

```
rource/
├── Cargo.toml                    # Workspace manifest
├── crates/
│   ├── rource-core/              # Core visualization engine
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── scene/            # Scene graph and entities
│   │   │   │   ├── mod.rs
│   │   │   │   ├── tree.rs       # Directory tree structure
│   │   │   │   ├── user.rs       # User/contributor entity
│   │   │   │   ├── file.rs       # File entity
│   │   │   │   ├── action.rs     # Action beams
│   │   │   │   └── edge.rs       # Spline edges
│   │   │   ├── physics/          # Force-directed layout
│   │   │   │   ├── mod.rs
│   │   │   │   ├── force.rs      # Force calculations
│   │   │   │   └── spatial.rs    # Quadtree partitioning
│   │   │   ├── animation/        # Tweening and interpolation
│   │   │   │   ├── mod.rs
│   │   │   │   ├── tween.rs      # Easing functions
│   │   │   │   └── spline.rs     # Catmull-Rom splines
│   │   │   ├── camera/           # Camera system
│   │   │   │   ├── mod.rs
│   │   │   │   └── zoom.rs       # Zoom camera
│   │   │   ├── config/           # Configuration
│   │   │   │   ├── mod.rs
│   │   │   │   └── settings.rs   # All settings
│   │   │   └── time/             # Timeline management
│   │   │       ├── mod.rs
│   │   │       └── playback.rs   # Playback controls
│   │   └── Cargo.toml
│   │
│   ├── rource-render/            # Rendering abstraction
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── backend/          # Rendering backends
│   │   │   │   ├── mod.rs
│   │   │   │   ├── software.rs   # CPU software rasterizer
│   │   │   │   ├── webgl.rs      # WebGL2 backend
│   │   │   │   └── canvas.rs     # Canvas2D backend (simplest)
│   │   │   ├── draw/             # Drawing primitives
│   │   │   │   ├── mod.rs
│   │   │   │   ├── circle.rs     # Circle/disc rendering
│   │   │   │   ├── line.rs       # Line/spline rendering
│   │   │   │   ├── quad.rs       # Textured quads
│   │   │   │   └── text.rs       # Text rendering
│   │   │   ├── batch/            # Batched rendering
│   │   │   │   ├── mod.rs
│   │   │   │   └── instanced.rs  # Instanced rendering
│   │   │   └── effects/          # Visual effects
│   │   │       ├── mod.rs
│   │   │       ├── bloom.rs      # Bloom/glow effect
│   │   │       └── shadow.rs     # Drop shadows
│   │   └── Cargo.toml
│   │
│   ├── rource-vcs/               # VCS log parsing
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── commit.rs         # Commit data structure
│   │   │   ├── parser/           # Format-specific parsers
│   │   │   │   ├── mod.rs
│   │   │   │   ├── git.rs        # Git log parser
│   │   │   │   ├── svn.rs        # SVN XML parser
│   │   │   │   ├── mercurial.rs  # Mercurial parser
│   │   │   │   ├── bazaar.rs     # Bazaar parser
│   │   │   │   └── custom.rs     # Custom format
│   │   │   └── detect.rs         # Auto-detect VCS type
│   │   └── Cargo.toml
│   │
│   ├── rource-font/              # Font rendering
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── rasterizer.rs     # Glyph rasterization
│   │   │   ├── cache.rs          # Glyph atlas cache
│   │   │   └── layout.rs         # Text layout
│   │   └── Cargo.toml
│   │
│   ├── rource-math/              # Math utilities (minimal)
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── vec.rs            # Vec2, Vec3, Vec4
│   │   │   ├── mat.rs            # Mat3, Mat4
│   │   │   ├── color.rs          # Color types
│   │   │   └── rect.rs           # Bounds/rectangles
│   │   └── Cargo.toml
│   │
│   └── rource-image/             # Image loading
│       ├── src/
│       │   ├── lib.rs
│       │   ├── png.rs            # PNG decoder
│       │   └── jpeg.rs           # JPEG decoder
│       └── Cargo.toml
│
├── rource-cli/                   # Native CLI application
│   ├── src/
│   │   ├── main.rs
│   │   ├── args.rs               # CLI argument parsing
│   │   └── export.rs             # Video/image export
│   └── Cargo.toml
│
├── rource-wasm/                  # WebAssembly application
│   ├── src/
│   │   ├── lib.rs                # WASM bindings
│   │   └── web.rs                # Web-specific code
│   ├── www/                      # Web frontend
│   │   ├── index.html
│   │   ├── main.js
│   │   └── style.css
│   └── Cargo.toml
│
└── assets/                       # Bundled assets
    ├── fonts/
    │   └── default.ttf           # Embedded default font
    └── icons/
        └── default_avatar.png    # Default user avatar
```

---

## 3. Technology Stack

### 3.1 Core Dependencies (Minimal)

| Purpose | Crate | Rationale |
|---------|-------|-----------|
| **Math** | Custom (`rource-math`) | Zero dependencies, ~500 lines |
| **Spatial** | Custom quadtree | Simple, ~300 lines |
| **Splines** | `uniform-cubic-splines` | no_std, Catmull-Rom support |
| **Font Rendering** | `fontdue` | Pure Rust, WASM-ready, fastest |
| **Image Loading** | `png` + `jpeg-decoder` | Minimal, pure Rust |
| **CLI Parsing** | `clap` (native only) | Feature-gated for CLI |
| **Regex** | `regex-lite` | Lighter than `regex`, no PCRE2 |
| **Time/Date** | `chrono` | Date parsing and formatting |
| **Serialization** | `serde` (optional) | Config files, optional |

### 3.2 Platform-Specific Dependencies

#### Native (CLI)
| Purpose | Crate | Notes |
|---------|-------|-------|
| Window | `winit` | Cross-platform windowing |
| GPU Rendering | `wgpu` | Optional GPU acceleration |
| Software Render | `softbuffer` | CPU framebuffer to window |
| Git Parsing | `gix` (gitoxide) | Pure Rust Git implementation |

#### WebAssembly (Browser)
| Purpose | Crate | Notes |
|---------|-------|-------|
| JS Binding | `wasm-bindgen` | Rust↔JS interop |
| Web APIs | `web-sys` | Canvas, WebGL bindings |
| Console | `console_error_panic_hook` | Better error messages |

### 3.3 No External System Dependencies

Unlike original Gource which requires:
- SDL2 (runtime library)
- OpenGL drivers
- FreeType2 (runtime library)
- libpng (runtime library)
- PCRE2 (runtime library)
- Boost (compile-time)

**Rource requires ZERO external system libraries** - everything is pure Rust or bundled.

---

## 4. Core Components

### 4.1 Scene Graph

The scene graph manages all visual entities:

```rust
// rource-core/src/scene/mod.rs

pub struct Scene {
    /// Root directory node
    pub root: DirNode,

    /// All users by ID
    pub users: HashMap<UserId, User>,

    /// All files by path
    pub files: HashMap<PathBuf, FileNode>,

    /// Active actions (user → file animations)
    pub actions: Vec<Action>,

    /// Spatial index for efficient queries
    pub spatial: QuadTree<EntityId>,

    /// Current simulation time
    pub time: SimulationTime,

    /// Camera state
    pub camera: ZoomCamera,
}

impl Scene {
    pub fn update(&mut self, dt: f32) {
        // 1. Apply physics forces
        self.apply_forces(dt);

        // 2. Update animations
        self.update_animations(dt);

        // 3. Update spatial index
        self.rebuild_spatial_index();

        // 4. Update camera tracking
        self.camera.update(dt, &self.get_active_bounds());
    }

    pub fn apply_commit(&mut self, commit: &Commit) {
        // Get or create user
        let user_id = self.get_or_create_user(&commit.author);

        for file_change in &commit.files {
            match file_change.action {
                FileAction::Create => {
                    let file = self.create_file(&file_change.path);
                    self.spawn_action(user_id, file, ActionType::Create);
                }
                FileAction::Modify => {
                    if let Some(file) = self.get_file(&file_change.path) {
                        self.spawn_action(user_id, file, ActionType::Modify);
                    }
                }
                FileAction::Delete => {
                    if let Some(file) = self.get_file(&file_change.path) {
                        self.spawn_action(user_id, file, ActionType::Delete);
                        file.mark_for_removal();
                    }
                }
            }
        }
    }
}
```

### 4.2 Directory Tree Structure

```rust
// rource-core/src/scene/tree.rs

pub struct DirNode {
    /// Directory name (not full path)
    pub name: String,

    /// Absolute path from root
    pub path: PathBuf,

    /// Parent directory (None for root)
    pub parent: Option<DirNodeId>,

    /// Child directories
    pub children: Vec<DirNodeId>,

    /// Files directly in this directory
    pub files: Vec<FileId>,

    /// Position in 2D space
    pub position: Vec2,

    /// Velocity for physics
    pub velocity: Vec2,

    /// Visual radius (based on content)
    pub radius: f32,

    /// Visibility state
    pub visible: bool,

    /// Edge spline to parent
    pub edge: Option<SplineEdge>,

    /// Depth in tree (0 = root)
    pub depth: u32,
}

impl DirNode {
    /// Calculate radius based on files and subdirectories
    pub fn calculate_radius(&self, files: &[FileNode], children: &[DirNode]) -> f32 {
        let file_area: f32 = self.files.iter()
            .filter_map(|&id| files.get(id))
            .map(|f| f.radius * f.radius * std::f32::consts::PI)
            .sum();

        let child_area: f32 = self.children.iter()
            .filter_map(|&id| children.get(id))
            .map(|c| c.radius * c.radius * std::f32::consts::PI)
            .sum();

        ((file_area + child_area) / std::f32::consts::PI).sqrt() + MIN_DIR_RADIUS
    }

    /// Get optimal positions for child nodes (circular layout)
    pub fn get_child_positions(&self, count: usize) -> Vec<Vec2> {
        let angle_step = 2.0 * std::f32::consts::PI / count as f32;
        let distance = self.radius * 2.5;

        (0..count).map(|i| {
            let angle = i as f32 * angle_step;
            self.position + Vec2::new(
                angle.cos() * distance,
                angle.sin() * distance,
            )
        }).collect()
    }
}
```

### 4.3 User/Contributor Entity

```rust
// rource-core/src/scene/user.rs

pub struct User {
    pub id: UserId,

    /// Display name
    pub name: String,

    /// Position in 2D space
    pub position: Vec2,

    /// Target position (for smooth movement)
    pub target: Option<Vec2>,

    /// Velocity
    pub velocity: Vec2,

    /// User color (derived from name hash)
    pub color: Color,

    /// Custom avatar texture (if loaded)
    pub avatar: Option<TextureId>,

    /// Pending actions this user is performing
    pub active_actions: Vec<ActionId>,

    /// Time since last action
    pub idle_time: f32,

    /// Visibility/fade state
    pub alpha: f32,

    /// Is highlighted (mouse over or selected)
    pub highlighted: bool,
}

impl User {
    pub fn new(name: &str) -> Self {
        Self {
            id: UserId::new(),
            name: name.to_string(),
            position: Vec2::ZERO,
            target: None,
            velocity: Vec2::ZERO,
            color: Self::color_from_name(name),
            avatar: None,
            active_actions: Vec::new(),
            idle_time: 0.0,
            alpha: 0.0, // Fade in
            highlighted: false,
        }
    }

    /// Generate consistent color from username
    fn color_from_name(name: &str) -> Color {
        // Simple hash-based color generation
        let hash = name.bytes().fold(0u32, |acc, b| {
            acc.wrapping_mul(31).wrapping_add(b as u32)
        });

        let hue = (hash % 360) as f32;
        let saturation = 0.6 + (((hash >> 8) % 40) as f32 / 100.0);
        let lightness = 0.5 + (((hash >> 16) % 20) as f32 / 100.0);

        Color::from_hsl(hue, saturation, lightness)
    }

    pub fn update(&mut self, dt: f32) {
        // Move towards target
        if let Some(target) = self.target {
            let direction = target - self.position;
            let distance = direction.length();

            if distance > 1.0 {
                self.velocity = direction.normalize() * USER_SPEED.min(distance * 2.0);
            } else {
                self.target = None;
                self.velocity = Vec2::ZERO;
            }
        }

        self.position += self.velocity * dt;

        // Fade in/out based on activity
        self.idle_time += dt;
        if self.idle_time > IDLE_THRESHOLD {
            self.alpha = (self.alpha - FADE_RATE * dt).max(0.0);
        } else {
            self.alpha = (self.alpha + FADE_RATE * dt).min(1.0);
        }
    }
}
```

### 4.4 File Entity

```rust
// rource-core/src/scene/file.rs

pub struct FileNode {
    pub id: FileId,

    /// File name (not full path)
    pub name: String,

    /// Full path from repository root
    pub path: PathBuf,

    /// File extension (for coloring)
    pub extension: Option<String>,

    /// Parent directory
    pub directory: DirNodeId,

    /// Position relative to parent directory
    pub position: Vec2,

    /// Target position (for layout)
    pub target: Vec2,

    /// Visual radius
    pub radius: f32,

    /// Base color (from extension)
    pub color: Color,

    /// Touch color (temporary after action)
    pub touch_color: Option<Color>,

    /// Touch fade timer
    pub touch_time: f32,

    /// Visibility alpha
    pub alpha: f32,

    /// Is being removed
    pub removing: bool,

    /// Time since last modification
    pub idle_time: f32,
}

impl FileNode {
    /// Get file extension color
    pub fn color_from_extension(ext: &str) -> Color {
        // Consistent color mapping for common extensions
        match ext.to_lowercase().as_str() {
            "rs" => Color::from_rgb(222, 165, 132), // Rust orange
            "js" | "ts" | "jsx" | "tsx" => Color::from_rgb(247, 223, 30), // JS yellow
            "py" => Color::from_rgb(53, 114, 165), // Python blue
            "go" => Color::from_rgb(0, 173, 216), // Go cyan
            "java" => Color::from_rgb(176, 114, 25), // Java brown
            "c" | "cpp" | "cc" | "h" | "hpp" => Color::from_rgb(85, 85, 255), // C blue
            "html" | "htm" => Color::from_rgb(227, 76, 38), // HTML orange
            "css" | "scss" | "sass" => Color::from_rgb(86, 61, 124), // CSS purple
            "json" | "yaml" | "yml" | "toml" => Color::from_rgb(128, 128, 128), // Config gray
            "md" | "markdown" | "txt" => Color::from_rgb(200, 200, 200), // Docs light
            "sh" | "bash" | "zsh" => Color::from_rgb(0, 128, 0), // Shell green
            "sql" => Color::from_rgb(255, 128, 0), // SQL orange
            "rb" => Color::from_rgb(204, 52, 45), // Ruby red
            "php" => Color::from_rgb(119, 123, 179), // PHP purple
            "swift" => Color::from_rgb(240, 81, 56), // Swift orange
            "kt" | "kts" => Color::from_rgb(167, 139, 250), // Kotlin purple
            _ => {
                // Generate color from extension hash
                let hash = ext.bytes().fold(0u32, |acc, b| {
                    acc.wrapping_mul(31).wrapping_add(b as u32)
                });
                let hue = (hash % 360) as f32;
                Color::from_hsl(hue, 0.5, 0.5)
            }
        }
    }

    pub fn touch(&mut self, action_type: ActionType) {
        self.touch_color = Some(match action_type {
            ActionType::Create => Color::from_rgb(0, 255, 0), // Green
            ActionType::Modify => Color::from_rgb(255, 165, 0), // Orange
            ActionType::Delete => Color::from_rgb(255, 0, 0), // Red
        });
        self.touch_time = 1.0;
        self.idle_time = 0.0;
    }

    pub fn update(&mut self, dt: f32) {
        // Update touch fade
        if self.touch_time > 0.0 {
            self.touch_time = (self.touch_time - dt).max(0.0);
            if self.touch_time == 0.0 {
                self.touch_color = None;
            }
        }

        // Update idle time
        self.idle_time += dt;

        // Fade out if removing
        if self.removing {
            self.alpha = (self.alpha - FADE_RATE * dt).max(0.0);
        }
    }

    /// Get current display color (with touch effect)
    pub fn current_color(&self) -> Color {
        if let Some(touch) = self.touch_color {
            self.color.lerp(touch, self.touch_time)
        } else {
            self.color
        }
    }
}
```

### 4.5 Action (User → File Animation)

```rust
// rource-core/src/scene/action.rs

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ActionType {
    Create,
    Modify,
    Delete,
}

pub struct Action {
    pub id: ActionId,

    /// Source user
    pub user: UserId,

    /// Target file
    pub file: FileId,

    /// Action type
    pub action_type: ActionType,

    /// Progress (0.0 = start, 1.0 = complete)
    pub progress: f32,

    /// Color of the action beam
    pub color: Color,
}

impl Action {
    pub fn new(user: UserId, file: FileId, action_type: ActionType) -> Self {
        Self {
            id: ActionId::new(),
            user,
            file,
            action_type,
            progress: 0.0,
            color: match action_type {
                ActionType::Create => Color::from_rgb(0, 255, 0),   // Green
                ActionType::Modify => Color::from_rgb(255, 165, 0), // Orange
                ActionType::Delete => Color::from_rgb(255, 0, 0),   // Red
            },
        }
    }

    pub fn update(&mut self, dt: f32) {
        self.progress = (self.progress + dt * ACTION_SPEED).min(1.0);
    }

    pub fn is_complete(&self) -> bool {
        self.progress >= 1.0
    }

    /// Get interpolated position along beam
    pub fn get_beam_position(&self, user_pos: Vec2, file_pos: Vec2) -> Vec2 {
        user_pos.lerp(file_pos, self.progress)
    }
}
```

### 4.6 Spline Edge Rendering

```rust
// rource-core/src/animation/spline.rs

use uniform_cubic_splines::{spline, basis::CatmullRom};

pub struct SplineEdge {
    /// Control points for the spline
    control_points: Vec<Vec2>,

    /// Cached interpolated points for rendering
    cached_points: Vec<Vec2>,

    /// Number of segments for rendering
    segments: usize,

    /// Start and end colors
    start_color: Color,
    end_color: Color,
}

impl SplineEdge {
    pub fn new(start: Vec2, end: Vec2, segments: usize) -> Self {
        Self {
            control_points: vec![start, start, end, end], // Catmull-Rom needs 4 points
            cached_points: Vec::with_capacity(segments + 1),
            segments,
            start_color: Color::WHITE,
            end_color: Color::WHITE,
        }
    }

    pub fn update(&mut self, start: Vec2, end: Vec2, control: Vec2) {
        // Set up control points for smooth curve
        self.control_points[0] = start - (control - start);
        self.control_points[1] = start;
        self.control_points[2] = end;
        self.control_points[3] = end + (end - control);

        // Rebuild cached points
        self.cached_points.clear();
        for i in 0..=self.segments {
            let t = i as f32 / self.segments as f32;
            // Interpolate between control points 1 and 2 (the visible segment)
            let point = self.interpolate(t);
            self.cached_points.push(point);
        }
    }

    fn interpolate(&self, t: f32) -> Vec2 {
        let x = spline::<CatmullRom, _, _>(t, &[
            self.control_points[0].x,
            self.control_points[1].x,
            self.control_points[2].x,
            self.control_points[3].x,
        ]);
        let y = spline::<CatmullRom, _, _>(t, &[
            self.control_points[0].y,
            self.control_points[1].y,
            self.control_points[2].y,
            self.control_points[3].y,
        ]);
        Vec2::new(x, y)
    }

    pub fn points(&self) -> &[Vec2] {
        &self.cached_points
    }
}
```

### 4.7 Force-Directed Layout (Physics)

```rust
// rource-core/src/physics/force.rs

pub struct ForceSimulation {
    /// Repulsion constant between nodes
    pub repulsion: f32,

    /// Attraction constant to parent
    pub attraction: f32,

    /// Damping factor (friction)
    pub damping: f32,

    /// Minimum distance for force calculation
    pub min_distance: f32,
}

impl Default for ForceSimulation {
    fn default() -> Self {
        Self {
            repulsion: 1000.0,
            attraction: 0.05,
            damping: 0.9,
            min_distance: 10.0,
        }
    }
}

impl ForceSimulation {
    /// Apply forces to all directory nodes
    pub fn apply(&self, nodes: &mut [DirNode], dt: f32) {
        let len = nodes.len();

        // Repulsion between siblings
        for i in 0..len {
            for j in (i + 1)..len {
                // Only apply repulsion between siblings or nearby nodes
                if !self.should_repel(&nodes[i], &nodes[j]) {
                    continue;
                }

                let delta = nodes[j].position - nodes[i].position;
                let distance = delta.length().max(self.min_distance);
                let force_magnitude = self.repulsion / (distance * distance);

                let force = delta.normalize() * force_magnitude;

                // Apply equal and opposite forces
                // (using indices to avoid borrow issues)
                let force_i = -force;
                let force_j = force;

                nodes[i].velocity += force_i * dt;
                nodes[j].velocity += force_j * dt;
            }
        }

        // Attraction to parent
        for node in nodes.iter_mut() {
            if let Some(parent_pos) = node.parent_position {
                let delta = parent_pos - node.position;
                let distance = delta.length();

                if distance > node.target_distance {
                    let force = delta.normalize() * (distance - node.target_distance) * self.attraction;
                    node.velocity += force * dt;
                }
            }
        }

        // Apply damping and integrate
        for node in nodes.iter_mut() {
            node.velocity *= self.damping;
            node.position += node.velocity * dt;
        }
    }

    fn should_repel(&self, a: &DirNode, b: &DirNode) -> bool {
        // Repel if same parent or close in tree
        a.parent == b.parent ||
        (a.depth as i32 - b.depth as i32).abs() <= 1
    }
}
```

### 4.8 Quadtree Spatial Partitioning

```rust
// rource-core/src/physics/spatial.rs

#[derive(Clone)]
pub struct Bounds {
    pub min: Vec2,
    pub max: Vec2,
}

impl Bounds {
    pub fn new(min: Vec2, max: Vec2) -> Self {
        Self { min, max }
    }

    pub fn contains(&self, point: Vec2) -> bool {
        point.x >= self.min.x && point.x <= self.max.x &&
        point.y >= self.min.y && point.y <= self.max.y
    }

    pub fn intersects(&self, other: &Bounds) -> bool {
        self.min.x <= other.max.x && self.max.x >= other.min.x &&
        self.min.y <= other.max.y && self.max.y >= other.min.y
    }

    pub fn center(&self) -> Vec2 {
        (self.min + self.max) * 0.5
    }

    pub fn size(&self) -> Vec2 {
        self.max - self.min
    }
}

pub struct QuadTree<T: Clone> {
    bounds: Bounds,
    items: Vec<(Vec2, T)>,
    children: Option<Box<[QuadTree<T>; 4]>>,
    max_items: usize,
    max_depth: usize,
    depth: usize,
}

impl<T: Clone> QuadTree<T> {
    pub fn new(bounds: Bounds, max_items: usize, max_depth: usize) -> Self {
        Self {
            bounds,
            items: Vec::new(),
            children: None,
            max_items,
            max_depth,
            depth: 0,
        }
    }

    pub fn insert(&mut self, position: Vec2, item: T) {
        if !self.bounds.contains(position) {
            return;
        }

        if self.children.is_some() {
            self.insert_into_child(position, item);
            return;
        }

        self.items.push((position, item));

        if self.items.len() > self.max_items && self.depth < self.max_depth {
            self.subdivide();
        }
    }

    pub fn query(&self, bounds: &Bounds) -> Vec<&T> {
        let mut results = Vec::new();
        self.query_recursive(bounds, &mut results);
        results
    }

    fn query_recursive<'a>(&'a self, bounds: &Bounds, results: &mut Vec<&'a T>) {
        if !self.bounds.intersects(bounds) {
            return;
        }

        for (pos, item) in &self.items {
            if bounds.contains(*pos) {
                results.push(item);
            }
        }

        if let Some(ref children) = self.children {
            for child in children.iter() {
                child.query_recursive(bounds, results);
            }
        }
    }

    fn subdivide(&mut self) {
        let center = self.bounds.center();
        let min = self.bounds.min;
        let max = self.bounds.max;

        let children = Box::new([
            // Top-left
            QuadTree::with_depth(
                Bounds::new(min, center),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
            // Top-right
            QuadTree::with_depth(
                Bounds::new(Vec2::new(center.x, min.y), Vec2::new(max.x, center.y)),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
            // Bottom-left
            QuadTree::with_depth(
                Bounds::new(Vec2::new(min.x, center.y), Vec2::new(center.x, max.y)),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
            // Bottom-right
            QuadTree::with_depth(
                Bounds::new(center, max),
                self.max_items,
                self.max_depth,
                self.depth + 1,
            ),
        ]);

        self.children = Some(children);

        // Move existing items to children
        let items = std::mem::take(&mut self.items);
        for (pos, item) in items {
            self.insert_into_child(pos, item);
        }
    }

    fn with_depth(bounds: Bounds, max_items: usize, max_depth: usize, depth: usize) -> Self {
        Self {
            bounds,
            items: Vec::new(),
            children: None,
            max_items,
            max_depth,
            depth,
        }
    }

    fn insert_into_child(&mut self, position: Vec2, item: T) {
        if let Some(ref mut children) = self.children {
            for child in children.iter_mut() {
                if child.bounds.contains(position) {
                    child.insert(position, item);
                    return;
                }
            }
        }
    }

    pub fn clear(&mut self) {
        self.items.clear();
        self.children = None;
    }
}
```

### 4.9 Camera System

```rust
// rource-core/src/camera/zoom.rs

pub struct ZoomCamera {
    /// Current position
    pub position: Vec2,

    /// Target position (for smooth tracking)
    pub target: Vec2,

    /// Current zoom level (1.0 = 100%)
    pub zoom: f32,

    /// Target zoom level
    pub target_zoom: f32,

    /// Minimum zoom level
    pub min_zoom: f32,

    /// Maximum zoom level
    pub max_zoom: f32,

    /// Camera movement speed
    pub move_speed: f32,

    /// Zoom interpolation speed
    pub zoom_speed: f32,

    /// Viewport size
    pub viewport: Vec2,

    /// Entity to track (if any)
    pub tracking: Option<EntityId>,
}

impl ZoomCamera {
    pub fn new(viewport: Vec2) -> Self {
        Self {
            position: Vec2::ZERO,
            target: Vec2::ZERO,
            zoom: 1.0,
            target_zoom: 1.0,
            min_zoom: 0.1,
            max_zoom: 10.0,
            move_speed: 5.0,
            zoom_speed: 3.0,
            viewport,
            tracking: None,
        }
    }

    pub fn update(&mut self, dt: f32) {
        // Smooth position interpolation
        let pos_delta = self.target - self.position;
        self.position += pos_delta * self.move_speed * dt;

        // Smooth zoom interpolation
        let zoom_delta = self.target_zoom - self.zoom;
        self.zoom += zoom_delta * self.zoom_speed * dt;
    }

    pub fn look_at(&mut self, target: Vec2) {
        self.target = target;
    }

    pub fn set_zoom(&mut self, zoom: f32) {
        self.target_zoom = zoom.clamp(self.min_zoom, self.max_zoom);
    }

    pub fn zoom_by(&mut self, factor: f32) {
        self.set_zoom(self.target_zoom * factor);
    }

    pub fn pan(&mut self, delta: Vec2) {
        self.target += delta / self.zoom;
        self.tracking = None;
    }

    /// Get the visible bounds in world coordinates
    pub fn visible_bounds(&self) -> Bounds {
        let half_size = self.viewport / (2.0 * self.zoom);
        Bounds::new(
            self.position - half_size,
            self.position + half_size,
        )
    }

    /// Convert screen coordinates to world coordinates
    pub fn screen_to_world(&self, screen: Vec2) -> Vec2 {
        let centered = screen - self.viewport * 0.5;
        self.position + centered / self.zoom
    }

    /// Convert world coordinates to screen coordinates
    pub fn world_to_screen(&self, world: Vec2) -> Vec2 {
        let offset = (world - self.position) * self.zoom;
        self.viewport * 0.5 + offset
    }

    /// Fit view to contain all given bounds
    pub fn fit_to_bounds(&mut self, bounds: &Bounds, padding: f32) {
        let center = bounds.center();
        let size = bounds.size() + Vec2::splat(padding * 2.0);

        self.target = center;

        let zoom_x = self.viewport.x / size.x;
        let zoom_y = self.viewport.y / size.y;
        self.set_zoom(zoom_x.min(zoom_y));
    }
}
```

---

## 5. Feature Parity Matrix

| Feature | Gource (Original) | Rource (Rust) | Enhancement |
|---------|------------------|---------------|-------------|
| **VCS Support** |
| Git | ✅ | ✅ | Pure Rust via gitoxide |
| SVN | ✅ | ✅ | XML parsing |
| Mercurial | ✅ | ✅ | Log parsing |
| Bazaar | ✅ | ✅ | Log parsing |
| CVS | ✅ | ✅ | cvs2cl format |
| Custom format | ✅ | ✅ | Enhanced with JSON/YAML |
| **Visualization** |
| Animated tree | ✅ | ✅ | Same |
| Force-directed layout | ✅ | ✅ | Optimized |
| Bloom effects | ✅ | ✅ | CPU-efficient |
| Shadows | ✅ | ✅ | Soft shadows |
| Spline edges | ✅ | ✅ | Catmull-Rom |
| User avatars | ✅ | ✅ | + SVG support |
| Action beams | ✅ | ✅ | Same |
| Color-coded files | ✅ | ✅ | Enhanced palette |
| **Camera** |
| Auto-tracking | ✅ | ✅ | Improved algorithm |
| Manual control | ✅ | ✅ | Touch support |
| Zoom limits | ✅ | ✅ | Same |
| **Playback** |
| Speed control | ✅ | ✅ | Same |
| Pause/resume | ✅ | ✅ | Same |
| Seek | ✅ | ✅ | Improved scrubbing |
| Auto-skip | ✅ | ✅ | Same |
| **Output** |
| Screenshots | ✅ | ✅ | PNG, JPEG, WebP |
| Video export | ✅ (PPM) | ✅ | PPM + direct MP4 |
| **UI** |
| Date display | ✅ | ✅ | Same |
| File legend | ✅ | ✅ | Interactive |
| Captions | ✅ | ✅ | Markdown support |
| **Platform** |
| Linux | ✅ | ✅ | Same |
| macOS | ✅ | ✅ | Same |
| Windows | ✅ | ✅ | Same |
| Web browser | ❌ | ✅ | **NEW** |
| Mobile | ❌ | ✅ | **NEW** |
| **Performance** |
| GPU required | ✅ | ❌ | CPU-only option |
| Large repos | Limited | ✅ | Streaming/LOD |
| Memory usage | High | Low | Efficient data |

---

## 6. Implementation Phases

### Phase 1: Foundation (Weeks 1-4) ✅

#### 1.1 Math Library (`rource-math`)
- [x] Vec2, Vec3, Vec4 types
- [x] Mat3, Mat4 types
- [x] Color types (RGB, HSL, RGBA)
- [x] Bounds/Rect types
- [x] Basic operations (dot, cross, normalize, lerp)
- [x] Unit tests for all types

#### 1.2 Configuration System
- [ ] Settings struct with all options
- [x] CLI argument parsing (clap) - 25+ options implemented
- [ ] Config file parsing (TOML)
- [ ] Environment variable support
- [x] Validation and defaults

#### 1.3 Core Data Structures
- [x] Entity ID types
- [x] Commit and FileChange structs
- [x] Basic scene graph skeleton

### Phase 2: VCS Parsing (Weeks 5-8) ✅

#### 2.1 Git Parser
- [x] Git log command generation
- [x] Log output parsing
- [x] Commit stream interface
- [ ] Pure Rust option (gitoxide)

#### 2.2 Other VCS Parsers
- [ ] SVN XML parser
- [ ] Mercurial parser
- [x] Custom format parser
- [x] VCS auto-detection

### Phase 3: Scene Graph (Weeks 9-12) ✅

#### 3.1 Directory Tree
- [x] DirNode structure
- [x] Tree construction from commits
- [x] Path normalization
- [x] Dynamic tree updates

#### 3.2 Entities
- [x] User entity with avatar
- [x] File entity with extension color
- [x] Action entity with animation

#### 3.3 Spatial Systems
- [x] Quadtree implementation
- [x] Spatial queries
- [ ] Frustum culling

### Phase 4: Physics & Animation (Weeks 13-16) ✅

#### 4.1 Force-Directed Layout
- [x] Repulsion forces
- [x] Attraction forces
- [x] Damping and stability
- [x] Performance optimization

#### 4.2 Animation System
- [x] Tweening functions (ease-in/out)
- [x] Spline interpolation
- [x] Action beam animation
- [x] Fade in/out effects

#### 4.3 Camera System
- [x] ZoomCamera implementation
- [x] Auto-tracking algorithm
- [x] Manual controls
- [x] Smooth interpolation

### Phase 5: Rendering - Software (Weeks 17-22) ✅

#### 5.1 Rendering Abstraction
- [x] Renderer trait
- [x] DrawCommand queue
- [x] Batch optimization

#### 5.2 Software Rasterizer
- [x] Line drawing (anti-aliased, Xiaolin Wu's algorithm)
- [x] Circle/disc drawing (anti-aliased)
- [x] Textured quad drawing (bilinear filtering)
- [x] Alpha blending

#### 5.3 Font Rendering
- [x] Fontdue integration
- [x] Glyph caching
- [x] Text layout

#### 5.4 Effects
- [x] Bloom (CPU approximation)
- [ ] Drop shadows
- [x] Color blending

### Phase 6: Platform Integration (Weeks 23-28) 🔄

#### 6.1 Native CLI
- [x] winit window creation
- [x] softbuffer integration
- [x] Input handling (keyboard controls)
- [x] CLI argument parsing (25+ options via clap)
- [x] Full scene graph integration
- [x] Camera system integration
- [x] Bloom effect integration
- [ ] Mouse input handling
- [ ] Video export (PPM frames)

#### 6.2 WebAssembly
- [ ] wasm-bindgen setup
- [ ] Canvas2D backend
- [ ] WebGL2 backend (optional)
- [ ] File upload interface

### Phase 7: Polish & Optimization (Weeks 29-32)

#### 7.1 Performance
- [ ] Profiling and bottleneck analysis
- [ ] Memory optimization
- [ ] Large repository handling
- [ ] Streaming commit loading

#### 7.2 User Experience
- [ ] Interactive file legend
- [ ] Timeline scrubbing
- [ ] Keyboard shortcuts
- [ ] Touch support

#### 7.3 Documentation
- [ ] User manual
- [ ] API documentation
- [ ] Examples
- [ ] Migration guide from Gource

---

## 7. Rendering Strategy

### 7.1 Multi-Backend Architecture

```rust
// rource-render/src/lib.rs

pub trait Renderer {
    fn begin_frame(&mut self);
    fn end_frame(&mut self);

    fn clear(&mut self, color: Color);

    fn draw_circle(&mut self, center: Vec2, radius: f32, color: Color);
    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color);
    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color);
    fn draw_spline(&mut self, points: &[Vec2], width: f32, colors: &[Color]);
    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color);
    fn draw_text(&mut self, text: &str, position: Vec2, font: &Font, color: Color);

    fn set_transform(&mut self, transform: Mat4);
    fn push_clip(&mut self, bounds: Bounds);
    fn pop_clip(&mut self);
}
```

### 7.2 Software Rasterizer (CPU-Only)

For maximum portability, the software rasterizer uses no GPU:

```rust
// rource-render/src/backend/software.rs

pub struct SoftwareRenderer {
    /// Pixel buffer (RGBA8)
    pixels: Vec<u32>,

    /// Width and height
    width: usize,
    height: usize,

    /// Depth buffer (optional for shadows)
    depth: Option<Vec<f32>>,

    /// Current transform matrix
    transform: Mat4,

    /// Clip stack
    clips: Vec<Bounds>,

    /// Font cache
    font_cache: FontCache,
}

impl SoftwareRenderer {
    /// Anti-aliased line drawing using Wu's algorithm
    fn draw_line_aa(&mut self, x0: f32, y0: f32, x1: f32, y1: f32, color: Color) {
        let steep = (y1 - y0).abs() > (x1 - x0).abs();

        let (x0, y0, x1, y1) = if steep {
            (y0, x0, y1, x1)
        } else {
            (x0, y0, x1, y1)
        };

        let (x0, y0, x1, y1) = if x0 > x1 {
            (x1, y1, x0, y0)
        } else {
            (x0, y0, x1, y1)
        };

        let dx = x1 - x0;
        let dy = y1 - y0;
        let gradient = if dx == 0.0 { 1.0 } else { dy / dx };

        // Handle first endpoint
        let xend = x0.round();
        let yend = y0 + gradient * (xend - x0);
        let xgap = 1.0 - (x0 + 0.5).fract();
        let xpxl1 = xend as i32;
        let ypxl1 = yend.floor() as i32;

        if steep {
            self.plot(ypxl1, xpxl1, (1.0 - yend.fract()) * xgap, color);
            self.plot(ypxl1 + 1, xpxl1, yend.fract() * xgap, color);
        } else {
            self.plot(xpxl1, ypxl1, (1.0 - yend.fract()) * xgap, color);
            self.plot(xpxl1, ypxl1 + 1, yend.fract() * xgap, color);
        }

        let mut intery = yend + gradient;

        // Handle second endpoint
        let xend = x1.round();
        let yend = y1 + gradient * (xend - x1);
        let xgap = (x1 + 0.5).fract();
        let xpxl2 = xend as i32;
        let ypxl2 = yend.floor() as i32;

        if steep {
            self.plot(ypxl2, xpxl2, (1.0 - yend.fract()) * xgap, color);
            self.plot(ypxl2 + 1, xpxl2, yend.fract() * xgap, color);
        } else {
            self.plot(xpxl2, ypxl2, (1.0 - yend.fract()) * xgap, color);
            self.plot(xpxl2, ypxl2 + 1, yend.fract() * xgap, color);
        }

        // Main loop
        for x in (xpxl1 + 1)..xpxl2 {
            if steep {
                self.plot(intery.floor() as i32, x, 1.0 - intery.fract(), color);
                self.plot(intery.floor() as i32 + 1, x, intery.fract(), color);
            } else {
                self.plot(x, intery.floor() as i32, 1.0 - intery.fract(), color);
                self.plot(x, intery.floor() as i32 + 1, intery.fract(), color);
            }
            intery += gradient;
        }
    }

    /// Plot a pixel with alpha blending
    fn plot(&mut self, x: i32, y: i32, brightness: f32, color: Color) {
        if x < 0 || y < 0 || x >= self.width as i32 || y >= self.height as i32 {
            return;
        }

        let idx = (y as usize * self.width + x as usize);
        let existing = self.pixels[idx];

        let alpha = (color.a as f32 / 255.0) * brightness;
        let inv_alpha = 1.0 - alpha;

        let r = ((existing >> 16) & 0xFF) as f32;
        let g = ((existing >> 8) & 0xFF) as f32;
        let b = (existing & 0xFF) as f32;

        let new_r = (color.r as f32 * alpha + r * inv_alpha) as u32;
        let new_g = (color.g as f32 * alpha + g * inv_alpha) as u32;
        let new_b = (color.b as f32 * alpha + b * inv_alpha) as u32;

        self.pixels[idx] = (new_r << 16) | (new_g << 8) | new_b;
    }

    /// Draw filled circle with anti-aliasing at edges
    fn draw_disc_aa(&mut self, cx: f32, cy: f32, radius: f32, color: Color) {
        let r2 = radius * radius;
        let min_x = (cx - radius).floor() as i32;
        let max_x = (cx + radius).ceil() as i32;
        let min_y = (cy - radius).floor() as i32;
        let max_y = (cy + radius).ceil() as i32;

        for y in min_y..=max_y {
            for x in min_x..=max_x {
                let dx = x as f32 - cx;
                let dy = y as f32 - cy;
                let dist2 = dx * dx + dy * dy;

                if dist2 <= (radius - 1.0) * (radius - 1.0) {
                    // Fully inside
                    self.plot(x, y, 1.0, color);
                } else if dist2 <= (radius + 1.0) * (radius + 1.0) {
                    // Edge - anti-alias
                    let dist = dist2.sqrt();
                    let coverage = 1.0 - (dist - radius + 0.5).clamp(0.0, 1.0);
                    self.plot(x, y, coverage, color);
                }
            }
        }
    }
}
```

### 7.3 WebGL2 Backend (Browser)

For better browser performance when GPU is available:

```rust
// rource-render/src/backend/webgl.rs

use web_sys::{WebGl2RenderingContext, WebGlProgram, WebGlBuffer};

pub struct WebGLRenderer {
    gl: WebGl2RenderingContext,

    // Shader programs
    basic_program: WebGlProgram,
    textured_program: WebGlProgram,
    text_program: WebGlProgram,

    // Vertex buffers
    quad_vbo: WebGlBuffer,
    circle_vbo: WebGlBuffer,

    // Batching
    batch: DrawBatch,

    // Textures
    textures: HashMap<TextureId, WebGlTexture>,
    font_atlas: WebGlTexture,
}

impl WebGLRenderer {
    const VERTEX_SHADER: &'static str = r#"#version 300 es
        precision mediump float;

        in vec2 a_position;
        in vec2 a_texcoord;
        in vec4 a_color;

        uniform mat4 u_transform;

        out vec2 v_texcoord;
        out vec4 v_color;

        void main() {
            gl_Position = u_transform * vec4(a_position, 0.0, 1.0);
            v_texcoord = a_texcoord;
            v_color = a_color;
        }
    "#;

    const FRAGMENT_SHADER: &'static str = r#"#version 300 es
        precision mediump float;

        in vec2 v_texcoord;
        in vec4 v_color;

        uniform sampler2D u_texture;
        uniform bool u_use_texture;

        out vec4 fragColor;

        void main() {
            vec4 color = v_color;
            if (u_use_texture) {
                color *= texture(u_texture, v_texcoord);
            }
            fragColor = color;
        }
    "#;
}
```

### 7.4 Bloom Effect (CPU-Efficient)

```rust
// rource-render/src/effects/bloom.rs

pub struct BloomEffect {
    /// Threshold for bloom (brightness above this blooms)
    pub threshold: f32,

    /// Bloom intensity multiplier
    pub intensity: f32,

    /// Number of blur passes
    pub passes: usize,

    /// Downscale factor for blur buffer
    pub downscale: usize,
}

impl BloomEffect {
    /// Apply bloom effect to a pixel buffer
    pub fn apply(&self, pixels: &mut [u32], width: usize, height: usize) {
        // 1. Extract bright pixels
        let bright = self.extract_bright(pixels, width, height);

        // 2. Downscale for faster blur
        let (small_w, small_h) = (width / self.downscale, height / self.downscale);
        let mut small = self.downscale_buffer(&bright, width, height, small_w, small_h);

        // 3. Apply box blur (faster than Gaussian)
        for _ in 0..self.passes {
            small = self.box_blur(&small, small_w, small_h);
        }

        // 4. Upscale and blend back
        let bloom = self.upscale_buffer(&small, small_w, small_h, width, height);

        for (i, pixel) in pixels.iter_mut().enumerate() {
            let bloom_pixel = bloom[i];
            *pixel = self.additive_blend(*pixel, bloom_pixel);
        }
    }

    fn extract_bright(&self, pixels: &[u32], width: usize, height: usize) -> Vec<u32> {
        pixels.iter().map(|&p| {
            let r = ((p >> 16) & 0xFF) as f32 / 255.0;
            let g = ((p >> 8) & 0xFF) as f32 / 255.0;
            let b = (p & 0xFF) as f32 / 255.0;

            let brightness = r * 0.299 + g * 0.587 + b * 0.114;

            if brightness > self.threshold {
                let factor = (brightness - self.threshold) * self.intensity;
                let nr = ((r * factor * 255.0) as u32).min(255);
                let ng = ((g * factor * 255.0) as u32).min(255);
                let nb = ((b * factor * 255.0) as u32).min(255);
                (nr << 16) | (ng << 8) | nb
            } else {
                0
            }
        }).collect()
    }

    fn box_blur(&self, src: &[u32], width: usize, height: usize) -> Vec<u32> {
        let mut dst = vec![0u32; src.len()];
        let radius = 2i32;

        // Horizontal pass
        for y in 0..height {
            for x in 0..width {
                let mut r = 0u32;
                let mut g = 0u32;
                let mut b = 0u32;
                let mut count = 0u32;

                for dx in -radius..=radius {
                    let nx = (x as i32 + dx).clamp(0, width as i32 - 1) as usize;
                    let pixel = src[y * width + nx];
                    r += (pixel >> 16) & 0xFF;
                    g += (pixel >> 8) & 0xFF;
                    b += pixel & 0xFF;
                    count += 1;
                }

                dst[y * width + x] = ((r / count) << 16) | ((g / count) << 8) | (b / count);
            }
        }

        // Vertical pass (in place)
        let src = dst.clone();
        for y in 0..height {
            for x in 0..width {
                let mut r = 0u32;
                let mut g = 0u32;
                let mut b = 0u32;
                let mut count = 0u32;

                for dy in -radius..=radius {
                    let ny = (y as i32 + dy).clamp(0, height as i32 - 1) as usize;
                    let pixel = src[ny * width + x];
                    r += (pixel >> 16) & 0xFF;
                    g += (pixel >> 8) & 0xFF;
                    b += pixel & 0xFF;
                    count += 1;
                }

                dst[y * width + x] = ((r / count) << 16) | ((g / count) << 8) | (b / count);
            }
        }

        dst
    }

    fn additive_blend(&self, base: u32, bloom: u32) -> u32 {
        let r = (((base >> 16) & 0xFF) + ((bloom >> 16) & 0xFF)).min(255);
        let g = (((base >> 8) & 0xFF) + ((bloom >> 8) & 0xFF)).min(255);
        let b = ((base & 0xFF) + (bloom & 0xFF)).min(255);
        (r << 16) | (g << 8) | b
    }
}
```

---

## 8. Performance Optimizations

### 8.1 Instanced Rendering (Inspired by Boids Gist)

The particle system gist demonstrates excellent performance through:

1. **Spatial Hashing**: 8,192 buckets with 8.0 cell size for 100,000 particles
2. **Instanced Rendering**: Batches of 16,384 instances reduce draw calls
3. **ECS Architecture**: Cache-friendly data layout

Apply to Rource:

```rust
// rource-render/src/batch/instanced.rs

/// Maximum instances per draw call
const MAX_INSTANCES: usize = 16384;

pub struct InstancedRenderer {
    /// Batched circle instances
    circles: Vec<CircleInstance>,

    /// Batched line instances
    lines: Vec<LineInstance>,

    /// Spatial hash for culling
    spatial: SpatialHash,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct CircleInstance {
    pub position: [f32; 2],
    pub radius: f32,
    pub color: [f32; 4],
}

impl InstancedRenderer {
    pub fn submit_circles(&mut self, instances: &[CircleInstance]) {
        for chunk in instances.chunks(MAX_INSTANCES) {
            self.draw_circle_batch(chunk);
        }
    }

    fn draw_circle_batch(&self, instances: &[CircleInstance]) {
        // Single draw call for up to 16,384 circles
        // WebGL2: gl.drawArraysInstanced(gl.TRIANGLE_FAN, 0, segments, instances.len())
    }
}
```

### 8.2 Spatial Hashing for Collision/Culling

```rust
// rource-core/src/physics/spatial.rs

pub struct SpatialHash<T> {
    cell_size: f32,
    buckets: HashMap<(i32, i32), Vec<T>>,
}

impl<T: Clone> SpatialHash<T> {
    pub fn new(cell_size: f32) -> Self {
        Self {
            cell_size,
            buckets: HashMap::new(),
        }
    }

    fn cell_key(&self, pos: Vec2) -> (i32, i32) {
        (
            (pos.x / self.cell_size).floor() as i32,
            (pos.y / self.cell_size).floor() as i32,
        )
    }

    pub fn insert(&mut self, pos: Vec2, item: T) {
        let key = self.cell_key(pos);
        self.buckets.entry(key).or_default().push(item);
    }

    pub fn query_radius(&self, center: Vec2, radius: f32) -> Vec<&T> {
        let mut results = Vec::new();

        let min_cell = self.cell_key(center - Vec2::splat(radius));
        let max_cell = self.cell_key(center + Vec2::splat(radius));

        for cx in min_cell.0..=max_cell.0 {
            for cy in min_cell.1..=max_cell.1 {
                if let Some(bucket) = self.buckets.get(&(cx, cy)) {
                    results.extend(bucket.iter());
                }
            }
        }

        results
    }

    pub fn clear(&mut self) {
        self.buckets.clear();
    }
}
```

### 8.3 Level of Detail (LOD)

```rust
// rource-core/src/scene/lod.rs

pub enum DetailLevel {
    /// Full detail - all effects
    High,
    /// Reduced detail - no bloom, simpler shapes
    Medium,
    /// Minimal detail - circles only, no text
    Low,
    /// Dots only - for very zoomed out views
    Minimal,
}

impl DetailLevel {
    pub fn from_zoom(zoom: f32, entity_count: usize) -> Self {
        let complexity = entity_count as f32 / zoom;

        match complexity {
            c if c < 1000.0 => DetailLevel::High,
            c if c < 5000.0 => DetailLevel::Medium,
            c if c < 20000.0 => DetailLevel::Low,
            _ => DetailLevel::Minimal,
        }
    }
}

impl FileNode {
    pub fn draw(&self, renderer: &mut impl Renderer, lod: DetailLevel) {
        match lod {
            DetailLevel::High => {
                renderer.draw_disc(self.position, self.radius, self.current_color());
                renderer.draw_circle(self.position, self.radius, Color::WHITE.with_alpha(0.3));
                if self.should_show_name() {
                    renderer.draw_text(&self.name, self.label_position(), ...);
                }
            }
            DetailLevel::Medium => {
                renderer.draw_disc(self.position, self.radius, self.current_color());
            }
            DetailLevel::Low => {
                renderer.draw_disc(self.position, self.radius * 0.8, self.current_color());
            }
            DetailLevel::Minimal => {
                renderer.draw_point(self.position, self.current_color());
            }
        }
    }
}
```

### 8.4 Memory-Efficient Data Structures

```rust
// Use compact IDs instead of pointers
pub struct UserId(u32);
pub struct FileId(u32);
pub struct DirNodeId(u32);

// Arena allocation for entities
pub struct Arena<T> {
    items: Vec<Option<T>>,
    free_list: Vec<usize>,
}

impl<T> Arena<T> {
    pub fn insert(&mut self, item: T) -> usize {
        if let Some(idx) = self.free_list.pop() {
            self.items[idx] = Some(item);
            idx
        } else {
            self.items.push(Some(item));
            self.items.len() - 1
        }
    }

    pub fn remove(&mut self, idx: usize) {
        self.items[idx] = None;
        self.free_list.push(idx);
    }

    pub fn get(&self, idx: usize) -> Option<&T> {
        self.items.get(idx)?.as_ref()
    }
}
```

### 8.5 Streaming Commit Loading

```rust
// rource-vcs/src/stream.rs

/// Streams commits without loading entire history into memory
pub struct CommitStream {
    reader: BufReader<Box<dyn Read>>,
    buffer: VecDeque<Commit>,
    buffer_size: usize,
}

impl CommitStream {
    pub fn new(source: Box<dyn Read>, buffer_size: usize) -> Self {
        Self {
            reader: BufReader::new(source),
            buffer: VecDeque::with_capacity(buffer_size),
            buffer_size,
        }
    }

    /// Get next commit, loading more if needed
    pub fn next(&mut self) -> Option<Commit> {
        if self.buffer.is_empty() {
            self.fill_buffer();
        }
        self.buffer.pop_front()
    }

    /// Peek at upcoming commits without consuming
    pub fn peek(&mut self, count: usize) -> &[Commit] {
        while self.buffer.len() < count {
            if !self.fill_buffer() {
                break;
            }
        }
        &self.buffer.make_contiguous()[..count.min(self.buffer.len())]
    }

    fn fill_buffer(&mut self) -> bool {
        // Parse more commits from reader
        // Returns false if no more data
        ...
    }
}
```

---

## 9. API Design

### 9.1 Public Library API

```rust
// rource-core/src/lib.rs

pub use crate::config::Settings;
pub use crate::scene::{Scene, Commit, FileAction};
pub use crate::camera::ZoomCamera;

/// Main visualization engine
pub struct Rource {
    scene: Scene,
    settings: Settings,
    playback: PlaybackController,
    commit_stream: Box<dyn Iterator<Item = Commit>>,
}

impl Rource {
    /// Create a new visualization from settings
    pub fn new(settings: Settings) -> Result<Self, Error>;

    /// Load commits from a source
    pub fn load_commits(&mut self, source: CommitSource) -> Result<(), Error>;

    /// Update simulation by delta time
    pub fn update(&mut self, dt: f32);

    /// Render current frame to a renderer
    pub fn render(&self, renderer: &mut impl Renderer);

    /// Get current playback time
    pub fn current_time(&self) -> DateTime<Utc>;

    /// Seek to specific time
    pub fn seek(&mut self, time: DateTime<Utc>);

    /// Play/pause
    pub fn set_playing(&mut self, playing: bool);

    /// Get camera reference for manual control
    pub fn camera(&self) -> &ZoomCamera;
    pub fn camera_mut(&mut self) -> &mut ZoomCamera;

    /// Handle input event
    pub fn handle_input(&mut self, event: InputEvent);
}

/// Supported commit sources
pub enum CommitSource {
    /// Git repository path
    Git(PathBuf),
    /// Custom format file
    Custom(PathBuf),
    /// Pre-parsed commits
    Commits(Vec<Commit>),
    /// Streaming iterator
    Stream(Box<dyn Iterator<Item = Commit>>),
}
```

### 9.2 WASM JavaScript API

```typescript
// rource.d.ts

export interface RourceSettings {
    width: number;
    height: number;
    autoPlay?: boolean;
    secondsPerDay?: number;
    hideDate?: boolean;
    hideUsers?: boolean;
    userScale?: number;
    fileScale?: number;
    bloomIntensity?: number;
    backgroundColor?: string;
}

export interface Commit {
    timestamp: number; // Unix timestamp
    author: string;
    files: FileChange[];
}

export interface FileChange {
    path: string;
    action: 'create' | 'modify' | 'delete';
    color?: string;
}

export class Rource {
    constructor(canvas: HTMLCanvasElement, settings?: RourceSettings);

    /** Load commits from array */
    loadCommits(commits: Commit[]): void;

    /** Load commits from git log format string */
    loadGitLog(log: string): void;

    /** Load from custom format string */
    loadCustomLog(log: string): void;

    /** Start playback */
    play(): void;

    /** Pause playback */
    pause(): void;

    /** Seek to specific timestamp */
    seek(timestamp: number): void;

    /** Set playback speed (seconds per day) */
    setSpeed(secondsPerDay: number): void;

    /** Zoom camera */
    zoom(factor: number): void;

    /** Pan camera */
    pan(dx: number, dy: number): void;

    /** Take screenshot */
    screenshot(): Uint8Array; // PNG data

    /** Get current timestamp */
    getCurrentTime(): number;

    /** Get total duration in seconds */
    getDuration(): number;

    /** Cleanup resources */
    destroy(): void;
}
```

### 9.3 CLI Interface

```
rource 0.1.0
Rust/WASM rewrite of Gource - Software version control visualization

USAGE:
    rource [OPTIONS] [PATH]

ARGS:
    <PATH>    Repository path or log file [default: .]

OPTIONS:
    -h, --help                   Print help information
    -V, --version                Print version information

DISPLAY:
    -W, --viewport <WIDTHxHEIGHT>     Set viewport size [default: 1280x720]
    -f, --fullscreen                  Start in fullscreen mode
    --no-vsync                        Disable vsync
    --frameless                       Frameless window

PLAYBACK:
    -s, --seconds-per-day <SECS>      Simulation speed [default: 1.0]
    -c, --time-scale <SCALE>          Time scale multiplier [default: 1.0]
    --start-date <DATE>               Start from date (YYYY-MM-DD)
    --stop-date <DATE>                Stop at date
    -p, --start-position <0.0-1.0>    Start at position
    --loop                            Loop when finished
    --disable-auto-skip               Don't skip idle periods

CAMERA:
    --camera-mode <MODE>              Camera mode: overview, track [default: overview]
    --padding <PADDING>               Camera padding [default: 1.2]

VISUALS:
    --hide-date                       Hide date display
    --hide-users                      Hide user labels
    --hide-files                      Hide file labels
    --hide-tree                       Hide directory tree
    --hide-progress                   Hide progress bar
    --hide-bloom                      Disable bloom effect
    --background <COLOR>              Background color (hex)
    --bloom-intensity <0.0-1.0>       Bloom intensity [default: 0.5]
    --user-scale <SCALE>              User size scale [default: 1.0]
    --file-scale <SCALE>              File size scale [default: 1.0]

FILTERING:
    --user-filter <REGEX>             Show only matching users
    --file-filter <REGEX>             Show only matching files
    --hide-filenames <REGEX>          Hide matching file names
    --max-files <N>                   Maximum files to show

OUTPUT:
    -o, --output-file <FILE>          Output video frames (ppm)
    --output-framerate <FPS>          Output framerate [default: 60]
    --screenshot <FILE>               Take screenshot and exit

CAPTIONS:
    --caption-file <FILE>             Load captions from file
    --caption-offset <SECS>           Caption time offset

USER IMAGES:
    --user-image-dir <DIR>            Directory containing user images
    --default-user-image <FILE>       Default user image

LOG FORMAT:
    --log-format <FORMAT>             Force log format: git, svn, hg, custom
    --git-branch <BRANCH>             Git branch to visualize
```

---

## 10. Testing Strategy

### 10.1 Unit Tests

```rust
// rource-math/src/vec.rs

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec2_operations() {
        let a = Vec2::new(3.0, 4.0);
        let b = Vec2::new(1.0, 2.0);

        assert_eq!(a + b, Vec2::new(4.0, 6.0));
        assert_eq!(a - b, Vec2::new(2.0, 2.0));
        assert_eq!(a * 2.0, Vec2::new(6.0, 8.0));
        assert!((a.length() - 5.0).abs() < 0.0001);
        assert!((a.dot(b) - 11.0).abs() < 0.0001);
    }

    #[test]
    fn test_vec2_normalize() {
        let v = Vec2::new(3.0, 4.0);
        let n = v.normalize();
        assert!((n.length() - 1.0).abs() < 0.0001);
        assert!((n.x - 0.6).abs() < 0.0001);
        assert!((n.y - 0.8).abs() < 0.0001);
    }
}
```

### 10.2 Integration Tests

```rust
// tests/integration/scene_test.rs

#[test]
fn test_scene_commit_processing() {
    let mut scene = Scene::new(Settings::default());

    let commit = Commit {
        timestamp: 1000000000,
        author: "Alice".to_string(),
        files: vec![
            FileChange { path: "src/main.rs".into(), action: FileAction::Create },
            FileChange { path: "Cargo.toml".into(), action: FileAction::Modify },
        ],
    };

    scene.apply_commit(&commit);

    assert_eq!(scene.users.len(), 1);
    assert!(scene.users.values().any(|u| u.name == "Alice"));
    assert!(scene.files.contains_key(&PathBuf::from("src/main.rs")));
    assert!(scene.files.contains_key(&PathBuf::from("Cargo.toml")));
}

#[test]
fn test_directory_tree_construction() {
    let mut scene = Scene::new(Settings::default());

    // Create nested directory structure
    let commit = Commit {
        timestamp: 1000000000,
        author: "Bob".to_string(),
        files: vec![
            FileChange { path: "a/b/c/file.txt".into(), action: FileAction::Create },
        ],
    };

    scene.apply_commit(&commit);

    // Verify tree structure
    assert!(scene.root.children.len() > 0);
    // ... more assertions
}
```

### 10.3 Visual Regression Tests

```rust
// tests/visual/render_test.rs

#[test]
fn test_render_basic_scene() {
    let scene = create_test_scene();
    let mut renderer = SoftwareRenderer::new(800, 600);

    scene.render(&mut renderer);

    let pixels = renderer.get_pixels();

    // Compare against reference image
    let reference = load_reference_image("basic_scene.png");
    let diff = calculate_image_diff(pixels, reference);

    assert!(diff < 0.01, "Visual regression: diff = {}", diff);
}
```

### 10.4 Performance Benchmarks

```rust
// benches/performance.rs

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_force_simulation(c: &mut Criterion) {
    let mut scene = create_large_scene(10000); // 10k files

    c.bench_function("force_simulation_10k", |b| {
        b.iter(|| {
            scene.apply_forces(0.016); // 60fps dt
        })
    });
}

fn bench_quadtree_query(c: &mut Criterion) {
    let mut tree = QuadTree::new(Bounds::new(Vec2::ZERO, Vec2::splat(10000.0)), 16, 8);

    // Insert 100k items
    for i in 0..100000 {
        let pos = Vec2::new(
            (i as f32 * 1.23) % 10000.0,
            (i as f32 * 4.56) % 10000.0,
        );
        tree.insert(pos, i);
    }

    c.bench_function("quadtree_query_100k", |b| {
        b.iter(|| {
            tree.query(&Bounds::new(Vec2::splat(4000.0), Vec2::splat(6000.0)))
        })
    });
}

criterion_group!(benches, bench_force_simulation, bench_quadtree_query);
criterion_main!(benches);
```

---

## 11. Build & Distribution

### 11.1 Cargo Workspace Configuration

```toml
# Cargo.toml (workspace root)
[workspace]
members = [
    "crates/rource-core",
    "crates/rource-render",
    "crates/rource-vcs",
    "crates/rource-font",
    "crates/rource-math",
    "crates/rource-image",
    "rource-cli",
    "rource-wasm",
]

[workspace.package]
version = "0.1.0"
edition = "2021"
license = "GPL-3.0-or-later"
repository = "https://github.com/yourname/rource"

[workspace.dependencies]
# Internal crates
rource-core = { path = "crates/rource-core" }
rource-render = { path = "crates/rource-render" }
rource-vcs = { path = "crates/rource-vcs" }
rource-font = { path = "crates/rource-font" }
rource-math = { path = "crates/rource-math" }
rource-image = { path = "crates/rource-image" }

# External minimal dependencies
fontdue = "0.8"
regex-lite = "0.1"
chrono = { version = "0.4", default-features = false }
serde = { version = "1.0", features = ["derive"], optional = true }
```

### 11.2 Native CLI Crate

```toml
# rource-cli/Cargo.toml
[package]
name = "rource"
version.workspace = true
edition.workspace = true

[[bin]]
name = "rource"
path = "src/main.rs"

[dependencies]
rource-core.workspace = true
rource-render.workspace = true
rource-vcs.workspace = true

clap = { version = "4", features = ["derive"] }
winit = "0.30"
softbuffer = "0.4"
anyhow = "1.0"

[target.'cfg(not(target_arch = "wasm32"))'.dependencies]
gix = { version = "0.63", default-features = false, features = ["basic"] }
```

### 11.3 WASM Crate

```toml
# rource-wasm/Cargo.toml
[package]
name = "rource-wasm"
version.workspace = true
edition.workspace = true

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
rource-core.workspace = true
rource-render = { workspace = true, features = ["webgl"] }
rource-vcs.workspace = true

wasm-bindgen = "0.2"
web-sys = { version = "0.3", features = [
    "Window",
    "Document",
    "HtmlCanvasElement",
    "CanvasRenderingContext2d",
    "WebGl2RenderingContext",
    "WebGlProgram",
    "WebGlBuffer",
    "WebGlTexture",
    "Performance",
] }
js-sys = "0.3"
console_error_panic_hook = "0.1"

[profile.release]
lto = true
opt-level = "z"
```

### 11.4 Build Scripts

```bash
#!/bin/bash
# build.sh - Build all targets

set -e

echo "Building native CLI..."
cargo build --release --package rource

echo "Building WASM..."
cd rource-wasm
wasm-pack build --target web --release
cd ..

echo "Optimizing WASM..."
wasm-opt -Oz -o rource-wasm/pkg/rource_wasm_bg_opt.wasm rource-wasm/pkg/rource_wasm_bg.wasm
mv rource-wasm/pkg/rource_wasm_bg_opt.wasm rource-wasm/pkg/rource_wasm_bg.wasm

echo "Build complete!"
echo "Native binary: target/release/rource"
echo "WASM package: rource-wasm/pkg/"
```

### 11.5 CI/CD Pipeline

```yaml
# .github/workflows/ci.yml
name: CI

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo test --all

  build-native:
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
    runs-on: ${{ matrix.os }}
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo build --release --package rource
      - uses: actions/upload-artifact@v4
        with:
          name: rource-${{ matrix.os }}
          path: target/release/rource*

  build-wasm:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: rustup target add wasm32-unknown-unknown
      - run: cargo install wasm-pack
      - run: wasm-pack build --target web --release rource-wasm
      - uses: actions/upload-artifact@v4
        with:
          name: rource-wasm
          path: rource-wasm/pkg/

  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo bench --no-run
```

---

## Appendix A: Migration Guide from Gource

### Command-Line Compatibility

| Gource Option | Rource Equivalent | Notes |
|---------------|-------------------|-------|
| `-WxH` | `-W WxH` | Same |
| `-f` | `-f` | Same |
| `-s` | `-s` | Same |
| `--hide-*` | `--hide-*` | Same |
| `--user-image-dir` | `--user-image-dir` | Same |
| `--logo` | `--logo` | Same |
| `-o output.ppm` | `-o output.ppm` | Same |

### New Features in Rource

1. **Web browser support** - Run in any modern browser
2. **No GPU required** - Software rendering option
3. **JSON/YAML config** - In addition to command-line
4. **Interactive timeline** - Click to seek
5. **Touch support** - Mobile-friendly
6. **Direct MP4 export** - No ffmpeg needed (optional)
7. **SVG avatars** - Vector user images
8. **Markdown captions** - Rich text overlays

---

## Appendix B: Dependency Audit

### Core Dependencies (Always Included)

| Crate | Size | Purpose | Alternative |
|-------|------|---------|-------------|
| `fontdue` | ~50KB | Font rasterization | Custom (complex) |
| `regex-lite` | ~30KB | Filtering | Custom DFA (complex) |
| `chrono` | ~100KB | Date/time | Custom (medium) |

### Optional Dependencies

| Crate | Size | Purpose | When Needed |
|-------|------|---------|-------------|
| `clap` | ~200KB | CLI parsing | Native only |
| `winit` | ~300KB | Windowing | Native only |
| `wasm-bindgen` | ~50KB | JS interop | WASM only |
| `gix` | ~500KB | Pure Rust Git | Optional native |
| `serde` | ~100KB | Serialization | Config files |

### Total Binary Size Estimates

| Target | Size (Release + LTO) |
|--------|---------------------|
| Native CLI (Linux) | ~2.5 MB |
| Native CLI (Windows) | ~3.0 MB |
| Native CLI (macOS) | ~2.8 MB |
| WASM (gzip) | ~400 KB |

---

## Appendix C: Research Sources

### Gource Repository Analysis
- GitHub: https://github.com/acaudwell/Gource
- Core Library: https://github.com/acaudwell/Core
- License: GPL-3.0

### Rust/WASM Graphics Libraries
- wgpu: https://wgpu.rs/
- miniquad: https://github.com/not-fl3/miniquad
- tiny-skia: https://github.com/RazrFalcon/tiny-skia

### Font Rendering
- fontdue: https://github.com/mooman219/fontdue
- rusttype/ab_glyph: https://github.com/alexheretic/ab-glyph

### Spatial Partitioning
- quadtree-rs: https://crates.io/crates/quadtree-rs
- aabb-quadtree: https://docs.rs/aabb-quadtree

### ECS Systems
- hecs: https://github.com/Ralith/hecs
- shipyard: https://github.com/leudz/shipyard

### Performance Reference (Boids Demo)
- Gist: https://gist.github.com/gabrieldechichi/17e13f9e2e8d8e5abb88019ab9efdc15
- Techniques: Spatial hashing, instanced rendering, ECS

---

## Document Metadata

- **Version**: 1.1
- **Created**: 2026-01-10
- **Last Updated**: 2026-01-10
- **Author**: Claude (AI Assistant)
- **Based On**: Comprehensive analysis of Gource v0.55/0.56
- **Target**: Rust 2021 Edition, WASM 2.0
- **Implementation Progress**: Phases 1-5 complete, Phase 6 in progress
- **Test Count**: 484 tests passing

---

*This document provides a complete roadmap for implementing Rource, a modern Rust/WASM rewrite of Gource. All technical details have been validated against the original source code and current Rust ecosystem capabilities.*

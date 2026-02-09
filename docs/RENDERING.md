# Rource Rendering Architecture

This document explains Rource's multi-backend rendering strategy and the design decisions behind it.

## Overview

Rource supports three rendering backends:

| Backend      | Target                     | Performance | Compatibility              |
|--------------|----------------------------|-------------|----------------------------|
| **wgpu**     | Native + WASM              | Best        | WebGPU/Vulkan/Metal/DX12   |
| **Software** | Native + WASM fallback     | Good        | Universal                  |
| **WebGL2**   | WASM primary               | Great       | WebGL2 required            |

The WASM build automatically tries wgpu (WebGPU) first, then WebGL2, and falls back to Software if neither is available. The wgpu backend provides cross-platform GPU rendering via the `wgpu` crate, targeting WebGPU, Vulkan, Metal, and DX12.

## Renderer Trait

All backends implement a common `Renderer` trait:

```rust
pub trait Renderer {
    // Frame lifecycle
    fn begin_frame(&mut self);
    fn end_frame(&mut self);

    // Canvas operations
    fn clear(&mut self, color: Color);
    fn width(&self) -> u32;
    fn height(&self) -> u32;
    fn resize(&mut self, width: u32, height: u32);

    // Primitives
    fn draw_circle(&mut self, center: Vec2, radius: f32, width: f32, color: Color);
    fn draw_disc(&mut self, center: Vec2, radius: f32, color: Color);
    fn draw_line(&mut self, start: Vec2, end: Vec2, width: f32, color: Color);
    fn draw_spline(&mut self, points: &[Vec2], width: f32, color: Color);
    fn draw_quad(&mut self, bounds: Bounds, texture: Option<TextureId>, color: Color);
    fn draw_text(&mut self, text: &str, position: Vec2, font: FontId, size: f32, color: Color);

    // Transform
    fn set_transform(&mut self, transform: Mat4);
    fn transform(&self) -> Mat4;

    // Clipping
    fn push_clip(&mut self, bounds: Bounds);
    fn pop_clip(&mut self);

    // Textures
    fn load_texture(&mut self, width: u32, height: u32, data: &[u8]) -> TextureId;
    fn unload_texture(&mut self, texture: TextureId);

    // Fonts
    fn load_font(&mut self, data: &[u8]) -> Option<FontId>;

    // File icons (opt-in, with default fallback implementations)
    fn init_file_icons(&mut self) -> bool { false }
    fn has_file_icons(&self) -> bool { false }
    fn draw_file_icon(&mut self, center: Vec2, size: f32, extension: &str, color: Color);
}
```

## Software Renderer

The `SoftwareRenderer` is a pure CPU rasterizer that works everywhere.

### Architecture

```
┌───────────────────────────────────────────────────────┐
│                   SoftwareRenderer                    │
├───────────────────────────────────────────────────────┤
│  Pixel Buffer: Vec<u32>  (ARGB format)                │
│  Width × Height pixels                                │
├───────────────────────────────────────────────────────┤
│  Clip Stack: Vec<Rect>                                │
│  Font Cache: HashMap<FontId, fontdue::Font>           │
│  Glyph Cache: HashMap<(char, size), RasterizedGlyph>  │
└───────────────────────────────────────────────────────┘
```

### Anti-Aliasing Algorithms

**Lines**: Xiaolin Wu's algorithm for smooth anti-aliased lines

```
For each pixel along the line:
  1. Calculate perpendicular distance to ideal line
  2. Apply intensity falloff based on distance
  3. Blend with existing pixel using alpha
```

**Circles**: Distance-field based anti-aliasing

```
For each pixel in bounding box:
  1. Calculate distance from center
  2. If |distance - radius| < 1.5:
     Apply smooth falloff based on sub-pixel distance
```

### Bloom Effect (Post-Processing)

The software renderer includes CPU-based bloom:

```
1. Threshold Pass:
   - Extract bright pixels (luminance > threshold)

2. Horizontal Blur:
   - 9-tap Gaussian blur horizontally

3. Vertical Blur:
   - 9-tap Gaussian blur vertically

4. Composite:
   - Additive blend bloom with original image
```

### Performance Characteristics

| Operation | Complexity          | Notes                 |
|-----------|---------------------|-----------------------|
| Clear     | O(w×h)              | Memset entire buffer  |
| Circle    | O(r²)               | Scan bounding box     |
| Line      | O(length)           | Bresenham + Wu AA     |
| Text      | O(chars×glyph_size) | Cached glyphs         |
| Bloom     | O(w×h×9)            | 3-pass blur           |

## WebGL2 Renderer

The `WebGl2Renderer` uses GPU-accelerated instanced rendering for best performance.

### Architecture

```
┌───────────────────────────────────────────────────────┐
│                    WebGl2Renderer                     │
├───────────────────────────────────────────────────────┤
│  WebGL2 Context (from canvas)                         │
├───────────────────────────────────────────────────────┤
│  Shader Programs:                                     │
│   • circle_program  (instanced circles/rings)         │
│   • line_program    (instanced line segments)         │
│   • quad_program    (instanced quads)                 │
│   • text_program    (textured quads for glyphs)       │
├───────────────────────────────────────────────────────┤
│  Buffers (per primitive type):                        │
│   • Vertex Buffer (unit geometry)                     │
│   • Instance Buffer (per-instance data)               │
├───────────────────────────────────────────────────────┤
│  Font Atlas:                                          │
│   • GL_R8 texture (single-channel alpha)              │
│   • Row-based packing (512→2048 max)                  │
│   • UV cache for glyphs                               │
└───────────────────────────────────────────────────────┘
```

### Instanced Rendering

Instead of individual draw calls per primitive, we batch by type:

```
// Collect all circles this frame
circles: Vec<CircleInstance> = [
    { center: (100, 200), radius: 10, color: RED },
    { center: (300, 400), radius: 15, color: BLUE },
    // ... potentially thousands
];

// Single draw call
gl.bindVertexArray(circle_vao);
gl.bufferData(ARRAY_BUFFER, circles, DYNAMIC_DRAW);
gl.drawArraysInstanced(TRIANGLE_FAN, 0, vertex_count, circles.len());
```

**Result**: 6 draw calls per frame regardless of entity count (one per primitive type).

### Shader Anti-Aliasing

GLSL ES 3.0 shaders with smooth edges:

**Circle Fragment Shader**:
```glsl
float dist = length(v_local_pos);
float edge = fwidth(dist);
float alpha = 1.0 - smoothstep(1.0 - edge, 1.0 + edge, dist);
gl_FragColor = vec4(v_color.rgb, v_color.a * alpha);
```

**Line Fragment Shader**:
```glsl
float dist = abs(v_perpendicular_dist);
float edge = fwidth(dist);
float alpha = 1.0 - smoothstep(half_width - edge, half_width + edge, dist);
gl_FragColor = vec4(v_color.rgb, v_color.a * alpha);
```

### Font Atlas Management

```
┌──────────────────────────────────────────┐
│ Font Atlas Texture (GL_R8)               │
├──────────────────────────────────────────┤
│ Row 0: A B C D E F G H I J K L M N ...   │
│ Row 1: a b c d e f g h i j k l m n ...   │
│ Row 2: 0 1 2 3 4 5 6 7 8 9 ! @ # $ ...   │
│ ...                                      │
└──────────────────────────────────────────┘

Glyph Cache: HashMap<(char, size_bucket), GlyphInfo>
GlyphInfo: { uv_min, uv_max, advance, offset }
```

### Context Loss Handling

WebGL contexts can be lost (GPU reset, tab backgrounded, etc.):

```rust
// Detection
pub fn is_context_lost(&self) -> bool {
    self.gl.is_context_lost()
}

// Recovery
pub fn recover_context(&mut self) -> Result<(), String> {
    // Recreate shaders
    self.create_shaders()?;

    // Recreate buffers
    self.create_buffers()?;

    // Rebuild font atlas
    self.rebuild_font_atlas()?;

    Ok(())
}
```

## wgpu Renderer

The `WgpuRenderer` provides cross-platform GPU-accelerated rendering via the [`wgpu`](https://wgpu.rs/) crate, abstracting over platform-native graphics APIs.

### Architecture

```
┌───────────────────────────────────────────────────────┐
│                     WgpuRenderer                      │
├───────────────────────────────────────────────────────┤
│  wgpu::Device + wgpu::Queue                           │
├───────────────────────────────────────────────────────┤
│  Render Pipelines:                                    │
│   • Circle pipeline (instanced circles/rings)         │
│   • Line pipeline   (instanced line segments)         │
│   • Quad pipeline   (instanced quads)                 │
│   • Text pipeline   (textured quads for glyphs)       │
├───────────────────────────────────────────────────────┤
│  Platform Backends (auto-selected by wgpu):           │
│   • Vulkan   (Linux, Windows, Android)                │
│   • Metal    (macOS, iOS)                             │
│   • DX12     (Windows)                                │
│   • WebGPU   (Browsers with WebGPU support)           │
└───────────────────────────────────────────────────────┘
```

### Key Features

- **Cross-platform GPU**: Single codebase targets Vulkan, Metal, DX12, and WebGPU
- **Native + WASM**: Works for both native desktop builds and browser WASM builds
- **Modern API**: Leverages the WebGPU specification for a clean, safe GPU abstraction
- **Instanced rendering**: Batches draw calls similar to the WebGL2 backend

### Source Location

The wgpu backend implementation is at `crates/rource-render/src/backend/wgpu/`.

## Backend Selection (WASM)

The `RendererBackend` enum provides automatic fallback:

```rust
pub enum RendererBackend {
    Wgpu(WgpuRenderer),
    WebGl2(WebGl2Renderer),
    Software {
        renderer: SoftwareRenderer,
        context: CanvasRenderingContext2d,
    },
}

impl RendererBackend {
    pub async fn new_async(canvas: &HtmlCanvasElement) -> Result<(Self, RendererType), JsValue> {
        // Try wgpu (WebGPU) first - best performance
        if let Ok(wgpu) = WgpuRenderer::new_async(canvas).await {
            return Ok((Self::Wgpu(wgpu), RendererType::Wgpu));
        }

        // Try WebGL2 next
        if let Ok(webgl2) = WebGl2Renderer::new(canvas) {
            return Ok((Self::WebGl2(webgl2), RendererType::WebGl2));
        }

        // Fall back to software + Canvas2D
        let context = canvas.get_context("2d")?.into();
        let renderer = SoftwareRenderer::new(width, height);
        Ok((Self::Software { renderer, context }, RendererType::Software))
    }
}
```

### JavaScript API

```javascript
const rource = await Rource.create(canvas);

// Check which renderer is active
const type = rource.getRendererType(); // "wgpu", "webgl2", or "software"
const isGPU = rource.isGPUAccelerated(); // true/false

// Handle context loss (WebGL2 only)
if (rource.isContextLost()) {
    const recovered = rource.recoverContext();
    if (!recovered) {
        console.error("Failed to recover WebGL context");
    }
}
```

## Rendering Pipeline Details

### Per-Frame Flow

```
┌───────────────────────────────────────────────────────┐
│ frame(timestamp) {                                    │
│   // 1. Calculate delta time                          │
│   dt = (timestamp - last_time) / 1000.0;              │
│                                                       │
│   // 2. Update simulation (if playing)                │
│   if (playing) {                                      │
│     apply_pending_commits();                          │
│   }                                                   │
│   scene.update(dt);  // Physics + animations          │
│   camera.update(dt); // Smooth following              │
│                                                       │
│   // 3. Render                                        │
│   render();                                           │
│ }                                                     │
└───────────────────────────────────────────────────────┘
```

### Render Layer Order

Entities are rendered back-to-front for correct alpha blending:

1. **Background** - Clear with background color
2. **Directory branches** - Tree connection lines (lowest z)
3. **Directory labels** - Text labels for directories
4. **Files** - Colored dots representing source files
5. **Action beams** - Lines from users to files being modified
6. **Users** - Avatar circles/images
7. **User labels** - Usernames above avatars
8. **File labels** - Filenames (when zoomed in)

### Frustum Culling

Only visible entities are rendered:

```rust
// Calculate visible bounds from camera
let visible_bounds = camera.visible_bounds();

// Query spatial index
let (visible_dirs, visible_files, visible_users) =
    scene.visible_entities(&visible_bounds);

// Render only visible entities
for dir_id in visible_dirs {
    render_directory(dir_id);
}
// ...
```

## Performance Comparison

Tested on MacBook Pro M1, 1920x1080, 10k files:

| Metric     | Software  | WebGL2    | Improvement  |
|------------|-----------|-----------|--------------|
| Draw calls | ~30,000   | 6         | 5000x fewer  |
| Frame time | 16ms      | 2ms       | 8x faster    |
| Max FPS    | ~60       | ~500      | Uncapped     |
| Memory     | 8MB buffer| 2MB + GPU | GPU offload  |

## CLI/WASM Rendering Synchronization

**Important**: The CLI and WASM have separate rendering code that must be kept in sync.

| Component  | Location                                                      |
|------------|---------------------------------------------------------------|
| Native CLI | `rource-cli/src/rendering.rs`                                 |
| WASM       | `rource-wasm/src/render_phases/`, `rource-wasm/src/rendering.rs` |

When modifying visual elements (avatar styles, beam effects, curves):
1. Update CLI rendering code
2. Update WASM rendering code
3. Test both to verify visual parity

**Future**: Extract shared rendering utilities to `rource-render/src/primitives.rs`.

## Debugging

### Software Renderer
```rust
// Get pixel buffer for inspection
let pixels = software_renderer.pixels();
let non_black = pixels.iter().filter(|&&p| p != 0xFF000000).count();
println!("Frame has {} non-black pixels", non_black);
```

### WebGL2 Renderer
```javascript
// Browser DevTools
const gl = canvas.getContext("webgl2");
console.log("WebGL2 supported:", !!gl);
console.log("Max texture size:", gl.getParameter(gl.MAX_TEXTURE_SIZE));

// Check WASM
console.log("Renderer type:", rource.getRendererType());
console.log("Draw calls:", rource.getDrawCalls());
```

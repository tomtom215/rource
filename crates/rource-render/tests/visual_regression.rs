// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

// Test module clippy configuration:
// - cast_possible_wrap: Pixel channel extraction (u8 shifted from u32) always fits in i32
// - cast_lossless: Using `as` for clarity in test assertions over verbose From::from
// - unreadable_literal: Hex color literals are more readable without separators (0xFF0000FF)
#![allow(
    clippy::cast_possible_wrap,
    clippy::cast_lossless,
    clippy::unreadable_literal
)]

//! Visual Regression Testing Suite for rource-render
//!
//! This module provides pixel-perfect visual regression testing for the rendering
//! pipeline. Tests render deterministic scenes and compare against golden images.
//!
//! # Running Tests
//!
//! ```bash
//! # Run all visual regression tests
//! cargo test -p rource-render --test visual_regression
//!
//! # Update golden images (when intentional changes are made)
//! UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression
//! ```
//!
//! # Architecture
//!
//! - **Deterministic Rendering**: Uses fixed-point arithmetic and seeded inputs
//! - **Golden Images**: Stored in `tests/visual/golden/` as PNG files
//! - **Pixel Comparison**: Mean Squared Error (MSE) with configurable threshold
//! - **Diff Generation**: Creates diff images highlighting changes
//!
//! # Adding New Tests
//!
//! 1. Create a test function that builds a deterministic scene
//! 2. Call `assert_visual_match("test_name", &renderer)`
//! 3. Run with `UPDATE_GOLDEN=1` to create initial golden image
//! 4. Commit the golden image to the repository

use rource_math::{Bounds, Color, Vec2};
use rource_render::{Renderer, SoftwareRenderer};
use std::env;
use std::fs::{self, File};
use std::io::{self, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

// ============================================================================
// Configuration Constants
// ============================================================================

/// Default test viewport width
const TEST_WIDTH: u32 = 320;

/// Default test viewport height
const TEST_HEIGHT: u32 = 240;

/// Maximum allowed Mean Squared Error before test fails.
/// 0.0 = pixel-perfect match required
/// 0.001 = allows ~1 LSB difference per channel on average
const MSE_THRESHOLD: f64 = 0.0;

/// Directory for golden reference images (relative to crate root)
const GOLDEN_DIR: &str = "tests/visual/golden";

/// Directory for test output/diff images (relative to crate root)
const OUTPUT_DIR: &str = "tests/visual/output";

// ============================================================================
// Pixel Comparison Utilities
// ============================================================================

/// Result of comparing two images pixel-by-pixel.
#[derive(Debug, Clone)]
pub struct ImageDiff {
    /// Mean Squared Error (0.0 = identical, 1.0 = maximum difference)
    pub mse: f64,
    /// Peak Signal-to-Noise Ratio in decibels (higher = more similar)
    pub psnr: f64,
    /// Number of pixels that differ
    pub different_pixels: u64,
    /// Total number of pixels compared
    pub total_pixels: u64,
    /// Maximum per-channel difference found
    pub max_diff: u8,
}

impl ImageDiff {
    /// Returns true if images are considered identical within threshold.
    pub fn is_match(&self, threshold: f64) -> bool {
        self.mse <= threshold
    }
}

/// Compares two ARGB8 pixel buffers and computes difference metrics.
///
/// # Arguments
/// * `expected` - Reference/golden pixel buffer (ARGB8 format)
/// * `actual` - Rendered pixel buffer to compare (ARGB8 format)
/// * `width` - Image width in pixels
/// * `height` - Image height in pixels
///
/// # Returns
/// Detailed comparison metrics including MSE and PSNR.
///
/// # Panics
/// Panics if buffer sizes don't match dimensions.
pub fn compare_pixels(expected: &[u32], actual: &[u32], width: u32, height: u32) -> ImageDiff {
    let total_pixels = (width * height) as u64;
    assert_eq!(
        expected.len(),
        total_pixels as usize,
        "Expected buffer size mismatch"
    );
    assert_eq!(
        actual.len(),
        total_pixels as usize,
        "Actual buffer size mismatch"
    );

    let mut sum_squared_error: f64 = 0.0;
    let mut different_pixels: u64 = 0;
    let mut max_diff: u8 = 0;

    for (exp_pixel, act_pixel) in expected.iter().zip(actual.iter()) {
        // Extract RGB channels (ignore alpha in comparison)
        let exp_r = ((*exp_pixel >> 16) & 0xFF) as i32;
        let exp_g = ((*exp_pixel >> 8) & 0xFF) as i32;
        let exp_b = (*exp_pixel & 0xFF) as i32;

        let act_r = ((*act_pixel >> 16) & 0xFF) as i32;
        let act_g = ((*act_pixel >> 8) & 0xFF) as i32;
        let act_b = (*act_pixel & 0xFF) as i32;

        let dr = exp_r - act_r;
        let dg = exp_g - act_g;
        let db = exp_b - act_b;

        // Track maximum per-channel difference
        max_diff = max_diff.max(dr.unsigned_abs() as u8);
        max_diff = max_diff.max(dg.unsigned_abs() as u8);
        max_diff = max_diff.max(db.unsigned_abs() as u8);

        if dr != 0 || dg != 0 || db != 0 {
            different_pixels += 1;
        }

        // Accumulate squared error (normalized to 0-1 range per channel)
        let err_r = (dr as f64) / 255.0;
        let err_g = (dg as f64) / 255.0;
        let err_b = (db as f64) / 255.0;
        sum_squared_error += err_r * err_r + err_g * err_g + err_b * err_b;
    }

    // MSE per channel, averaged over all pixels and 3 channels
    let mse = sum_squared_error / (total_pixels as f64 * 3.0);

    // PSNR (Peak Signal-to-Noise Ratio)
    let psnr = if mse > 0.0 {
        10.0 * (1.0 / mse).log10()
    } else {
        f64::INFINITY // Perfect match
    };

    ImageDiff {
        mse,
        psnr,
        different_pixels,
        total_pixels,
        max_diff,
    }
}

/// Generates a diff image highlighting pixel differences.
///
/// Differences are shown in red intensity proportional to the magnitude.
/// Returns ARGB8 pixel buffer.
pub fn generate_diff_image(
    expected: &[u32],
    actual: &[u32],
    _width: u32,
    _height: u32,
) -> Vec<u32> {
    let mut diff = Vec::with_capacity(expected.len());

    for (exp_pixel, act_pixel) in expected.iter().zip(actual.iter()) {
        let exp_r = ((*exp_pixel >> 16) & 0xFF) as i32;
        let exp_g = ((*exp_pixel >> 8) & 0xFF) as i32;
        let exp_b = (*exp_pixel & 0xFF) as i32;

        let act_r = ((*act_pixel >> 16) & 0xFF) as i32;
        let act_g = ((*act_pixel >> 8) & 0xFF) as i32;
        let act_b = (*act_pixel & 0xFF) as i32;

        // Compute maximum per-channel difference
        let max_channel_diff = (exp_r - act_r)
            .abs()
            .max((exp_g - act_g).abs())
            .max((exp_b - act_b).abs());

        if max_channel_diff == 0 {
            // No difference: show grayscale version of actual
            let gray = ((act_r + act_g + act_b) / 3) as u32;
            diff.push(0xFF00_0000 | (gray << 16) | (gray << 8) | gray);
        } else {
            // Difference found: show red intensity (amplified for visibility)
            let intensity = ((max_channel_diff as u32) * 4).min(255);
            diff.push(0xFF00_0000 | (intensity << 16)); // Red channel only
        }
    }

    diff
}

// ============================================================================
// PNG I/O Utilities
// ============================================================================

/// Writes ARGB8 pixel buffer to PNG file.
pub fn write_png_to_file<P: AsRef<Path>>(
    pixels: &[u32],
    width: u32,
    height: u32,
    path: P,
) -> io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    write_png(pixels, width, height, &mut writer)
}

/// Writes ARGB8 pixel buffer to PNG format.
fn write_png<W: Write>(pixels: &[u32], width: u32, height: u32, writer: &mut W) -> io::Result<()> {
    // PNG signature
    writer.write_all(&[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A])?;

    // IHDR chunk
    let ihdr_data = {
        let mut data = Vec::with_capacity(13);
        data.extend_from_slice(&width.to_be_bytes());
        data.extend_from_slice(&height.to_be_bytes());
        data.push(8); // Bit depth
        data.push(2); // Color type: RGB
        data.push(0); // Compression method
        data.push(0); // Filter method
        data.push(0); // Interlace method
        data
    };
    write_png_chunk(writer, *b"IHDR", &ihdr_data)?;

    // Prepare raw image data with filter bytes
    let row_size = 1 + (width as usize) * 3;
    let mut raw_data = Vec::with_capacity(row_size * height as usize);

    for y in 0..height as usize {
        raw_data.push(0); // Filter type: None
        for x in 0..width as usize {
            let pixel = pixels[y * width as usize + x];
            let r = ((pixel >> 16) & 0xFF) as u8;
            let g = ((pixel >> 8) & 0xFF) as u8;
            let b = (pixel & 0xFF) as u8;
            raw_data.push(r);
            raw_data.push(g);
            raw_data.push(b);
        }
    }

    // Compress and write IDAT chunk
    let compressed = deflate_compress(&raw_data);
    write_png_chunk(writer, *b"IDAT", &compressed)?;

    // IEND chunk
    write_png_chunk(writer, *b"IEND", &[])?;

    writer.flush()
}

fn write_png_chunk<W: Write>(writer: &mut W, chunk_type: [u8; 4], data: &[u8]) -> io::Result<()> {
    writer.write_all(&(data.len() as u32).to_be_bytes())?;
    writer.write_all(&chunk_type)?;
    writer.write_all(data)?;
    writer.write_all(&crc32(&chunk_type, data).to_be_bytes())?;
    Ok(())
}

fn crc32(chunk_type: &[u8], data: &[u8]) -> u32 {
    const CRC_TABLE: [u32; 256] = {
        let mut table = [0u32; 256];
        let mut i = 0;
        while i < 256 {
            let mut crc = i as u32;
            let mut j = 0;
            while j < 8 {
                if crc & 1 != 0 {
                    crc = 0xEDB8_8320 ^ (crc >> 1);
                } else {
                    crc >>= 1;
                }
                j += 1;
            }
            table[i] = crc;
            i += 1;
        }
        table
    };

    let mut crc = 0xFFFF_FFFF_u32;
    for &byte in chunk_type.iter().chain(data.iter()) {
        let index = ((crc ^ u32::from(byte)) & 0xFF) as usize;
        crc = CRC_TABLE[index] ^ (crc >> 8);
    }
    !crc
}

const MAX_DEFLATE_BLOCK: usize = 65535;

fn deflate_compress(data: &[u8]) -> Vec<u8> {
    let mut output = Vec::new();
    output.push(0x78); // CMF
    output.push(0x01); // FLG

    let mut offset = 0;
    while offset < data.len() {
        let remaining = data.len() - offset;
        let block_len = remaining.min(MAX_DEFLATE_BLOCK);
        let is_final = offset + block_len >= data.len();

        output.push(u8::from(is_final));
        let len = block_len as u16;
        output.push((len & 0xFF) as u8);
        output.push((len >> 8) as u8);
        output.push((!len & 0xFF) as u8);
        output.push((!len >> 8) as u8);
        output.extend_from_slice(&data[offset..offset + block_len]);
        offset += block_len;
    }

    let adler = adler32(data);
    output.extend_from_slice(&adler.to_be_bytes());
    output
}

fn adler32(data: &[u8]) -> u32 {
    let mut a: u32 = 1;
    let mut b: u32 = 0;
    for &byte in data {
        a = (a + u32::from(byte)) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}

/// Reads a PNG file and returns the pixel data as ARGB8.
///
/// This is a minimal PNG decoder that handles the specific format we produce.
pub fn read_png_from_file<P: AsRef<Path>>(path: P) -> io::Result<(Vec<u32>, u32, u32)> {
    let mut file = File::open(path)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;

    // Verify PNG signature
    if data.len() < 8 || data[0..8] != [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid PNG signature",
        ));
    }

    let mut offset = 8;
    let mut width: u32 = 0;
    let mut height: u32 = 0;
    let mut compressed_data = Vec::new();

    // Parse chunks
    while offset + 12 <= data.len() {
        let length = u32::from_be_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]) as usize;
        let chunk_type = &data[offset + 4..offset + 8];
        let chunk_data = &data[offset + 8..offset + 8 + length];

        match chunk_type {
            b"IHDR" => {
                if length >= 8 {
                    width = u32::from_be_bytes([
                        chunk_data[0],
                        chunk_data[1],
                        chunk_data[2],
                        chunk_data[3],
                    ]);
                    height = u32::from_be_bytes([
                        chunk_data[4],
                        chunk_data[5],
                        chunk_data[6],
                        chunk_data[7],
                    ]);
                }
            }
            b"IDAT" => {
                compressed_data.extend_from_slice(chunk_data);
            }
            b"IEND" => break,
            _ => {}
        }

        offset += 12 + length;
    }

    if width == 0 || height == 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid PNG dimensions",
        ));
    }

    // Decompress zlib data
    let raw_data = inflate_decompress(&compressed_data)?;

    // Parse pixel data (RGB with filter byte per row)
    let row_stride = 1 + (width as usize) * 3;
    let mut pixels = Vec::with_capacity((width * height) as usize);

    for y in 0..height as usize {
        let row_start = y * row_stride + 1; // Skip filter byte
        for x in 0..width as usize {
            let idx = row_start + x * 3;
            if idx + 2 < raw_data.len() {
                let r = raw_data[idx] as u32;
                let g = raw_data[idx + 1] as u32;
                let b = raw_data[idx + 2] as u32;
                pixels.push(0xFF00_0000 | (r << 16) | (g << 8) | b);
            }
        }
    }

    Ok((pixels, width, height))
}

/// Minimal zlib/deflate decompression for uncompressed (stored) blocks.
fn inflate_decompress(data: &[u8]) -> io::Result<Vec<u8>> {
    if data.len() < 6 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Compressed data too short",
        ));
    }

    // Skip zlib header (2 bytes) and parse stored blocks
    let mut output = Vec::new();
    let mut offset = 2;

    while offset < data.len() - 4 {
        let bfinal = data[offset] & 1;
        let btype = (data[offset] >> 1) & 3;

        if btype != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Only uncompressed DEFLATE blocks supported",
            ));
        }

        offset += 1;

        if offset + 4 > data.len() {
            break;
        }

        let len = u16::from_le_bytes([data[offset], data[offset + 1]]) as usize;
        offset += 4; // Skip LEN and NLEN

        if offset + len > data.len() - 4 {
            // Account for Adler-32 checksum at end
            let available = data.len().saturating_sub(offset + 4);
            output.extend_from_slice(&data[offset..offset + available.min(len)]);
            break;
        }

        output.extend_from_slice(&data[offset..offset + len]);
        offset += len;

        if bfinal != 0 {
            break;
        }
    }

    Ok(output)
}

// ============================================================================
// Test Infrastructure
// ============================================================================

/// Returns the path to the golden image directory.
fn golden_dir() -> PathBuf {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(manifest_dir).join(GOLDEN_DIR)
}

/// Returns the path to the test output directory.
fn output_dir() -> PathBuf {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    PathBuf::from(manifest_dir).join(OUTPUT_DIR)
}

/// Ensures the output directory exists.
fn ensure_output_dir() -> io::Result<()> {
    fs::create_dir_all(output_dir())
}

/// Ensures the golden directory exists.
fn ensure_golden_dir() -> io::Result<()> {
    fs::create_dir_all(golden_dir())
}

/// Main assertion function for visual regression tests.
///
/// Compares rendered output against golden image. If `UPDATE_GOLDEN` environment
/// variable is set, updates the golden image instead of comparing.
///
/// # Arguments
/// * `test_name` - Unique identifier for this test (used for file names)
/// * `renderer` - Software renderer with rendered content
///
/// # Panics
/// Panics if the visual comparison fails (MSE exceeds threshold).
pub fn assert_visual_match(test_name: &str, renderer: &SoftwareRenderer) {
    let golden_path = golden_dir().join(format!("{test_name}.png"));
    let actual_path = output_dir().join(format!("{test_name}_actual.png"));
    let diff_path = output_dir().join(format!("{test_name}_diff.png"));

    let pixels = renderer.pixels();
    let width = renderer.width();
    let height = renderer.height();

    // Ensure directories exist
    ensure_output_dir().expect("Failed to create output directory");
    ensure_golden_dir().expect("Failed to create golden directory");

    // Save actual rendered image for debugging
    write_png_to_file(pixels, width, height, &actual_path).expect("Failed to write actual image");

    // Check if we should update golden images
    if env::var("UPDATE_GOLDEN").is_ok() {
        write_png_to_file(pixels, width, height, &golden_path)
            .expect("Failed to write golden image");
        println!("Updated golden image: {}", golden_path.display());
        return;
    }

    // Load golden image
    let (golden_pixels, golden_width, golden_height) = match read_png_from_file(&golden_path) {
        Ok(result) => result,
        Err(e) => {
            panic!(
                "Golden image not found: {}\n\
                 Run with UPDATE_GOLDEN=1 to create it:\n\
                 UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression {}\n\
                 Error: {}",
                golden_path.display(),
                test_name,
                e
            );
        }
    };

    // Verify dimensions match
    assert_eq!(
        (width, height),
        (golden_width, golden_height),
        "Image dimensions mismatch for test '{test_name}': expected {golden_width}x{golden_height}, got {width}x{height}",
    );

    // Compare pixels
    let diff = compare_pixels(&golden_pixels, pixels, width, height);

    // Generate and save diff image if there are differences
    if diff.different_pixels > 0 {
        let diff_pixels = generate_diff_image(&golden_pixels, pixels, width, height);
        write_png_to_file(&diff_pixels, width, height, &diff_path)
            .expect("Failed to write diff image");
    }

    // Check if within threshold
    let diff_percent = (diff.different_pixels as f64 / diff.total_pixels as f64) * 100.0;
    let golden_display = golden_path.display();
    let actual_display = actual_path.display();
    let diff_display = diff_path.display();
    assert!(
        diff.is_match(MSE_THRESHOLD),
        "Visual regression detected in test '{test_name}'!\n\
         \n\
         Metrics:\n\
         - MSE: {:.6} (threshold: {MSE_THRESHOLD:.6})\n\
         - PSNR: {:.2} dB\n\
         - Different pixels: {} / {} ({diff_percent:.2}%)\n\
         - Max channel diff: {}\n\
         \n\
         Files:\n\
         - Golden:  {golden_display}\n\
         - Actual:  {actual_display}\n\
         - Diff:    {diff_display}\n\
         \n\
         If this change is intentional, update golden images with:\n\
         UPDATE_GOLDEN=1 cargo test -p rource-render --test visual_regression {test_name}",
        diff.mse,
        diff.psnr,
        diff.different_pixels,
        diff.total_pixels,
        diff.max_diff,
    );

    println!(
        "Visual test '{}' passed (MSE: {:.6}, {} pixels identical)",
        test_name, diff.mse, diff.total_pixels
    );
}

// ============================================================================
// Visual Regression Tests
// ============================================================================

/// Test: Empty black frame renders correctly.
#[test]
fn visual_empty_black_frame() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::BLACK);
    renderer.end_frame();

    assert_visual_match("empty_black_frame", &renderer);
}

/// Test: Solid color fill.
#[test]
fn visual_solid_color_fill() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x1A1A2E)); // Dark blue background
    renderer.end_frame();

    assert_visual_match("solid_color_fill", &renderer);
}

/// Test: Circle/disc rendering with anti-aliasing.
#[test]
fn visual_disc_rendering() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x0D1117)); // GitHub dark theme

    // Render multiple discs at different positions and sizes
    let positions = [
        (80.0, 60.0, 20.0, Color::RED),
        (160.0, 60.0, 25.0, Color::GREEN),
        (240.0, 60.0, 30.0, Color::BLUE),
        (80.0, 140.0, 15.0, Color::YELLOW),
        (160.0, 140.0, 35.0, Color::CYAN),
        (240.0, 140.0, 18.0, Color::MAGENTA),
        (160.0, 200.0, 25.0, Color::WHITE),
    ];

    for (x, y, radius, color) in positions {
        renderer.draw_disc(Vec2::new(x, y), radius, color);
    }

    renderer.end_frame();
    assert_visual_match("disc_rendering", &renderer);
}

/// Test: Line rendering with anti-aliasing.
#[test]
fn visual_line_rendering() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x0D1117));

    // Horizontal lines
    renderer.draw_line(
        Vec2::new(20.0, 30.0),
        Vec2::new(300.0, 30.0),
        1.0,
        Color::RED,
    );
    renderer.draw_line(
        Vec2::new(20.0, 50.0),
        Vec2::new(300.0, 50.0),
        2.0,
        Color::GREEN,
    );

    // Vertical lines
    renderer.draw_line(
        Vec2::new(40.0, 70.0),
        Vec2::new(40.0, 220.0),
        1.0,
        Color::BLUE,
    );
    renderer.draw_line(
        Vec2::new(60.0, 70.0),
        Vec2::new(60.0, 220.0),
        3.0,
        Color::YELLOW,
    );

    // Diagonal lines (various angles)
    renderer.draw_line(
        Vec2::new(80.0, 70.0),
        Vec2::new(200.0, 150.0),
        1.0,
        Color::CYAN,
    );
    renderer.draw_line(
        Vec2::new(80.0, 150.0),
        Vec2::new(200.0, 70.0),
        2.0,
        Color::MAGENTA,
    );
    renderer.draw_line(
        Vec2::new(220.0, 70.0),
        Vec2::new(300.0, 220.0),
        1.5,
        Color::WHITE,
    );

    renderer.end_frame();
    assert_visual_match("line_rendering", &renderer);
}

/// Test: Filled rectangle rendering using `draw_quad`.
#[test]
fn visual_rect_rendering() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x0D1117));

    // Various rectangles using draw_quad (None texture = solid fill)
    renderer.draw_quad(
        Bounds::new(Vec2::new(20.0, 20.0), Vec2::new(100.0, 80.0)),
        None,
        Color::RED.with_alpha(0.8),
    );
    renderer.draw_quad(
        Bounds::new(Vec2::new(80.0, 60.0), Vec2::new(180.0, 140.0)),
        None,
        Color::GREEN.with_alpha(0.6),
    );
    renderer.draw_quad(
        Bounds::new(Vec2::new(150.0, 100.0), Vec2::new(280.0, 200.0)),
        None,
        Color::BLUE.with_alpha(0.7),
    );

    // Small rectangles
    renderer.draw_quad(
        Bounds::new(Vec2::new(240.0, 20.0), Vec2::new(260.0, 40.0)),
        None,
        Color::YELLOW,
    );
    renderer.draw_quad(
        Bounds::new(Vec2::new(270.0, 20.0), Vec2::new(300.0, 60.0)),
        None,
        Color::CYAN,
    );

    renderer.end_frame();
    assert_visual_match("rect_rendering", &renderer);
}

/// Test: Alpha blending with overlapping shapes.
#[test]
fn visual_alpha_blending() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x0D1117));

    // Draw overlapping semi-transparent discs
    renderer.draw_disc(Vec2::new(120.0, 100.0), 60.0, Color::RED.with_alpha(0.5));
    renderer.draw_disc(Vec2::new(160.0, 100.0), 60.0, Color::GREEN.with_alpha(0.5));
    renderer.draw_disc(Vec2::new(140.0, 140.0), 60.0, Color::BLUE.with_alpha(0.5));

    // Draw overlapping rectangles using draw_quad
    renderer.draw_quad(
        Bounds::new(Vec2::new(200.0, 60.0), Vec2::new(280.0, 120.0)),
        None,
        Color::YELLOW.with_alpha(0.4),
    );
    renderer.draw_quad(
        Bounds::new(Vec2::new(220.0, 80.0), Vec2::new(300.0, 160.0)),
        None,
        Color::MAGENTA.with_alpha(0.4),
    );
    renderer.draw_quad(
        Bounds::new(Vec2::new(240.0, 100.0), Vec2::new(310.0, 200.0)),
        None,
        Color::CYAN.with_alpha(0.4),
    );

    renderer.end_frame();
    assert_visual_match("alpha_blending", &renderer);
}

/// Test: Ring/circle outline rendering (using `draw_circle`).
#[test]
fn visual_ring_rendering() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x0D1117));

    // Various rings with different thicknesses (draw_circle = outlined circle)
    renderer.draw_circle(Vec2::new(60.0, 60.0), 30.0, 2.0, Color::RED);
    renderer.draw_circle(Vec2::new(140.0, 60.0), 35.0, 4.0, Color::GREEN);
    renderer.draw_circle(Vec2::new(240.0, 60.0), 40.0, 1.0, Color::BLUE);

    renderer.draw_circle(Vec2::new(80.0, 160.0), 50.0, 3.0, Color::YELLOW);
    renderer.draw_circle(Vec2::new(200.0, 160.0), 55.0, 6.0, Color::CYAN);

    // Concentric rings
    renderer.draw_circle(Vec2::new(280.0, 160.0), 20.0, 2.0, Color::WHITE);
    renderer.draw_circle(
        Vec2::new(280.0, 160.0),
        35.0,
        2.0,
        Color::WHITE.with_alpha(0.7),
    );
    renderer.draw_circle(
        Vec2::new(280.0, 160.0),
        50.0,
        2.0,
        Color::WHITE.with_alpha(0.4),
    );

    renderer.end_frame();
    assert_visual_match("ring_rendering", &renderer);
}

/// Test: Color spectrum using `draw_quad`.
#[test]
fn visual_color_spectrum() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::BLACK);

    // Draw color bars
    let bar_height = TEST_HEIGHT as f32 / 7.0;
    let colors = [
        Color::RED,
        Color::from_hex(0xFF8000), // Orange
        Color::YELLOW,
        Color::GREEN,
        Color::CYAN,
        Color::BLUE,
        Color::MAGENTA,
    ];

    for (i, color) in colors.iter().enumerate() {
        let y_start = i as f32 * bar_height;
        let y_end = (i + 1) as f32 * bar_height;
        renderer.draw_quad(
            Bounds::new(Vec2::new(0.0, y_start), Vec2::new(TEST_WIDTH as f32, y_end)),
            None,
            *color,
        );
    }

    renderer.end_frame();
    assert_visual_match("color_spectrum", &renderer);
}

/// Test: Complex scene with multiple element types.
#[test]
fn visual_complex_scene() {
    let mut renderer = SoftwareRenderer::new(TEST_WIDTH, TEST_HEIGHT);
    renderer.set_deterministic_mode(true);
    renderer.begin_frame();
    renderer.clear(Color::from_hex(0x0D1117));

    // Background grid pattern
    for x in (0..=320).step_by(20) {
        renderer.draw_line(
            Vec2::new(x as f32, 0.0),
            Vec2::new(x as f32, 240.0),
            0.5,
            Color::gray(0.15),
        );
    }
    for y in (0..=240).step_by(20) {
        renderer.draw_line(
            Vec2::new(0.0, y as f32),
            Vec2::new(320.0, y as f32),
            0.5,
            Color::gray(0.15),
        );
    }

    // File nodes (directory tree simulation)
    let file_positions = [
        (50.0, 50.0, 8.0, Color::from_hex(0x58A6FF)), // Blue (folder)
        (100.0, 80.0, 5.0, Color::from_hex(0x7EE787)), // Green (added)
        (150.0, 60.0, 5.0, Color::from_hex(0xF85149)), // Red (deleted)
        (200.0, 100.0, 5.0, Color::from_hex(0xD29922)), // Yellow (modified)
        (80.0, 130.0, 6.0, Color::from_hex(0x8B949E)), // Gray (unchanged)
        (140.0, 150.0, 5.0, Color::from_hex(0x7EE787)),
        (200.0, 170.0, 5.0, Color::from_hex(0xD29922)),
        (260.0, 140.0, 7.0, Color::from_hex(0x58A6FF)),
    ];

    for (x, y, r, color) in file_positions {
        renderer.draw_disc(Vec2::new(x, y), r, color);
    }

    // Connection lines (beams between nodes)
    renderer.draw_line(
        Vec2::new(50.0, 50.0),
        Vec2::new(100.0, 80.0),
        1.0,
        Color::from_hex(0x58A6FF).with_alpha(0.5),
    );
    renderer.draw_line(
        Vec2::new(50.0, 50.0),
        Vec2::new(150.0, 60.0),
        1.0,
        Color::from_hex(0x58A6FF).with_alpha(0.5),
    );
    renderer.draw_line(
        Vec2::new(100.0, 80.0),
        Vec2::new(80.0, 130.0),
        1.0,
        Color::from_hex(0x7EE787).with_alpha(0.3),
    );
    renderer.draw_line(
        Vec2::new(140.0, 150.0),
        Vec2::new(200.0, 170.0),
        1.0,
        Color::from_hex(0x7EE787).with_alpha(0.3),
    );

    // User avatar (circle outline + disc)
    renderer.draw_disc(Vec2::new(280.0, 200.0), 15.0, Color::from_hex(0xF78166));
    renderer.draw_circle(
        Vec2::new(280.0, 200.0),
        18.0,
        2.0,
        Color::WHITE.with_alpha(0.8),
    );

    renderer.end_frame();
    assert_visual_match("complex_scene", &renderer);
}

// ============================================================================
// Module Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compare_identical_images() {
        let pixels = vec![0xFF_FF_00_00; 100]; // Red pixels
        let diff = compare_pixels(&pixels, &pixels, 10, 10);
        assert_eq!(diff.mse, 0.0);
        assert_eq!(diff.different_pixels, 0);
        assert!(diff.psnr.is_infinite());
    }

    #[test]
    fn test_compare_different_images() {
        let pixels1 = vec![0xFF_FF_00_00; 100]; // Red
        let pixels2 = vec![0xFF_00_FF_00; 100]; // Green
        let diff = compare_pixels(&pixels1, &pixels2, 10, 10);
        assert!(diff.mse > 0.0);
        assert_eq!(diff.different_pixels, 100);
        assert_eq!(diff.max_diff, 255);
    }

    #[test]
    fn test_diff_image_generation() {
        let pixels1 = vec![0xFF_FF_00_00; 100]; // Red
        let pixels2 = vec![0xFF_00_FF_00; 100]; // Green
        let diff = generate_diff_image(&pixels1, &pixels2, 10, 10);
        assert_eq!(diff.len(), 100);
        // All pixels should show red (indicating difference)
        for pixel in diff {
            assert!((pixel >> 16) & 0xFF > 0); // Red channel should be set
        }
    }

    #[test]
    fn test_mse_threshold() {
        let pixels1 = vec![0xFF_80_80_80; 100]; // Gray
        let mut pixels2 = pixels1.clone();
        pixels2[0] = 0xFF_81_80_80; // Slightly different red

        let diff = compare_pixels(&pixels1, &pixels2, 10, 10);
        assert!(diff.mse > 0.0);
        assert!(diff.mse < 0.001); // Very small difference
        assert_eq!(diff.different_pixels, 1);
    }
}

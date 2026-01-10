//! Video export utilities for Rource.
//!
//! This module provides functionality for exporting frames as PPM images,
//! which can be piped to ffmpeg for video encoding.
//!
//! # Example Usage
//!
//! ```bash
//! # Export to video file using ffmpeg
//! rource --output - | ffmpeg -y -r 60 -f image2pipe -vcodec ppm -i - output.mp4
//!
//! # Export to high-quality video
//! rource --output - --framerate 60 | ffmpeg -y -r 60 -f image2pipe -vcodec ppm -i - -c:v libx264 -preset slow -crf 18 output.mp4
//! ```

use std::io::{self, Write};
use std::path::Path;

/// Writes a frame buffer to a PPM file.
///
/// The buffer is expected to be in ARGB8 format (0xAARRGGBB),
/// which is what the `SoftwareRenderer` uses.
///
/// # Arguments
///
/// * `pixels` - The pixel buffer in ARGB8 format
/// * `width` - Frame width in pixels
/// * `height` - Frame height in pixels
/// * `writer` - Any Write implementation (file, stdout, etc.)
///
/// # Returns
///
/// Returns `Ok(())` on success, or an IO error on failure.
pub fn write_ppm<W: Write>(
    pixels: &[u32],
    width: u32,
    height: u32,
    writer: &mut W,
) -> io::Result<()> {
    // Write PPM header (P6 = binary format)
    writeln!(writer, "P6")?;
    writeln!(writer, "{width} {height}")?;
    writeln!(writer, "255")?;

    // Write pixel data as RGB bytes
    // Our buffer is ARGB8 (0xAARRGGBB), we extract R, G, B
    let mut rgb_buffer = Vec::with_capacity((width * height * 3) as usize);

    for &pixel in pixels.iter().take((width * height) as usize) {
        let r = ((pixel >> 16) & 0xFF) as u8;
        let g = ((pixel >> 8) & 0xFF) as u8;
        let b = (pixel & 0xFF) as u8;
        rgb_buffer.push(r);
        rgb_buffer.push(g);
        rgb_buffer.push(b);
    }

    writer.write_all(&rgb_buffer)?;
    writer.flush()?;

    Ok(())
}

/// Writes a frame to stdout in PPM format.
///
/// This is useful for piping directly to ffmpeg.
pub fn write_ppm_to_stdout(pixels: &[u32], width: u32, height: u32) -> io::Result<()> {
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    write_ppm(pixels, width, height, &mut handle)
}

/// Writes a frame to a file in PPM format.
pub fn write_ppm_to_file<P: AsRef<Path>>(
    pixels: &[u32],
    width: u32,
    height: u32,
    path: P,
) -> io::Result<()> {
    let mut file = std::fs::File::create(path)?;
    write_ppm(pixels, width, height, &mut file)
}

/// Frame exporter for video output.
///
/// Manages the export of frames to PPM format, either to stdout
/// or to numbered files in a directory.
pub struct FrameExporter {
    /// Output mode.
    mode: ExportMode,
    /// Frame counter.
    frame_count: u64,
    /// Target framerate.
    framerate: u32,
    /// Time accumulator for frame timing.
    time_accumulator: f64,
    /// Seconds per frame.
    frame_interval: f64,
}

/// Export mode determines where frames are written.
#[derive(Debug, Clone)]
pub enum ExportMode {
    /// Write to stdout (for piping to ffmpeg).
    Stdout,
    /// Write numbered files to a directory.
    Directory(std::path::PathBuf),
}

impl FrameExporter {
    /// Creates a new frame exporter.
    ///
    /// # Arguments
    ///
    /// * `mode` - Where to write frames
    /// * `framerate` - Target frames per second
    pub fn new(mode: ExportMode, framerate: u32) -> Self {
        Self {
            mode,
            frame_count: 0,
            framerate,
            time_accumulator: 0.0,
            frame_interval: 1.0 / f64::from(framerate),
        }
    }

    /// Creates an exporter that writes to stdout.
    pub fn to_stdout(framerate: u32) -> Self {
        Self::new(ExportMode::Stdout, framerate)
    }

    /// Creates an exporter that writes numbered files to a directory.
    pub fn to_directory<P: AsRef<Path>>(path: P, framerate: u32) -> Self {
        Self::new(
            ExportMode::Directory(path.as_ref().to_path_buf()),
            framerate,
        )
    }

    /// Returns the number of frames exported.
    pub fn frame_count(&self) -> u64 {
        self.frame_count
    }

    /// Returns the target framerate.
    #[allow(dead_code)]
    pub fn framerate(&self) -> u32 {
        self.framerate
    }

    /// Exports a frame if enough time has elapsed.
    ///
    /// This method uses time accumulation to ensure consistent frame timing.
    ///
    /// # Arguments
    ///
    /// * `pixels` - The pixel buffer in ARGB8 format
    /// * `width` - Frame width
    /// * `height` - Frame height
    /// * `dt` - Delta time since last call
    ///
    /// # Returns
    ///
    /// Returns the number of frames written (0 or 1).
    pub fn export_frame(
        &mut self,
        pixels: &[u32],
        width: u32,
        height: u32,
        dt: f64,
    ) -> io::Result<u32> {
        self.time_accumulator += dt;

        let mut frames_written = 0;

        // Write frames to maintain target framerate
        #[allow(clippy::while_float)]
        while self.time_accumulator >= self.frame_interval {
            self.write_frame(pixels, width, height)?;
            self.time_accumulator -= self.frame_interval;
            self.frame_count += 1;
            frames_written += 1;
        }

        Ok(frames_written)
    }

    /// Forces a frame write regardless of timing.
    ///
    /// Useful for exporting the first frame or final frame.
    #[allow(dead_code)]
    pub fn force_write_frame(&mut self, pixels: &[u32], width: u32, height: u32) -> io::Result<()> {
        self.write_frame(pixels, width, height)?;
        self.frame_count += 1;
        Ok(())
    }

    /// Internal method to write a single frame.
    fn write_frame(&self, pixels: &[u32], width: u32, height: u32) -> io::Result<()> {
        match &self.mode {
            ExportMode::Stdout => {
                write_ppm_to_stdout(pixels, width, height)?;
            }
            ExportMode::Directory(dir) => {
                let filename = format!("frame_{:08}.ppm", self.frame_count);
                let path = dir.join(filename);
                write_ppm_to_file(pixels, width, height, path)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_ppm_basic() {
        // Create a simple 2x2 image
        let pixels = vec![
            0xFF_FF_00_00, // Red
            0xFF_00_FF_00, // Green
            0xFF_00_00_FF, // Blue
            0xFF_FF_FF_FF, // White
        ];

        let mut output = Vec::new();
        write_ppm(&pixels, 2, 2, &mut output).unwrap();

        // Check header
        let output_str = String::from_utf8_lossy(&output);
        assert!(output_str.starts_with("P6\n2 2\n255\n"));

        // Check that we have pixel data after header
        // Header is "P6\n2 2\n255\n" = 11 bytes
        // Pixel data is 2*2*3 = 12 bytes
        assert_eq!(output.len(), 11 + 12);

        // Verify pixel bytes (after header)
        let pixel_data = &output[11..];
        assert_eq!(pixel_data[0], 0xFF); // R of red
        assert_eq!(pixel_data[1], 0x00); // G of red
        assert_eq!(pixel_data[2], 0x00); // B of red
        assert_eq!(pixel_data[3], 0x00); // R of green
        assert_eq!(pixel_data[4], 0xFF); // G of green
        assert_eq!(pixel_data[5], 0x00); // B of green
    }

    #[test]
    fn test_write_ppm_empty() {
        let pixels: Vec<u32> = vec![];
        let mut output = Vec::new();

        write_ppm(&pixels, 0, 0, &mut output).unwrap();

        let output_str = String::from_utf8_lossy(&output);
        assert!(output_str.starts_with("P6\n0 0\n255\n"));
    }

    #[test]
    fn test_frame_exporter_new() {
        let exporter = FrameExporter::to_stdout(60);

        assert_eq!(exporter.framerate(), 60);
        assert_eq!(exporter.frame_count(), 0);
    }

    #[test]
    fn test_frame_exporter_timing() {
        let mut exporter = FrameExporter::to_stdout(60);

        // At 60 FPS, frame interval is ~16.67ms
        // We can't easily test stdout, so just verify the timing logic
        // by checking frame count

        // Simulate time passing without actual writing
        exporter.time_accumulator += 0.008; // 8ms
        assert!(exporter.time_accumulator < exporter.frame_interval);

        exporter.time_accumulator += 0.010; // Now 18ms total
        assert!(exporter.time_accumulator >= exporter.frame_interval);
    }

    #[test]
    fn test_export_mode_directory() {
        let exporter = FrameExporter::to_directory("/tmp/frames", 30);

        match &exporter.mode {
            ExportMode::Directory(path) => {
                assert_eq!(path.to_str().unwrap(), "/tmp/frames");
            }
            ExportMode::Stdout => panic!("Expected Directory mode"),
        }

        assert_eq!(exporter.framerate(), 30);
    }
}

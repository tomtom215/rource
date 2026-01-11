//! Image loading and manipulation for Rource.
//!
//! This module provides PNG image loading with RGBA8 output for use with renderers.
//! It supports loading from files or byte slices.
//!
//! # Example
//!
//! ```ignore
//! use rource_render::image::Image;
//!
//! // Load from file
//! let img = Image::load_file("logo.png")?;
//! let texture_id = renderer.load_texture(img.width(), img.height(), img.data());
//! ```

use std::io::{BufReader, Read};
use std::path::Path;

/// Error type for image loading operations.
#[derive(Debug, Clone)]
pub enum ImageError {
    /// Failed to read the file.
    Io(String),
    /// PNG decoding failed.
    Decode(String),
    /// Unsupported image format or color type.
    Unsupported(String),
}

impl std::fmt::Display for ImageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(msg) => write!(f, "Image I/O error: {msg}"),
            Self::Decode(msg) => write!(f, "Image decode error: {msg}"),
            Self::Unsupported(msg) => write!(f, "Unsupported image format: {msg}"),
        }
    }
}

impl std::error::Error for ImageError {}

impl From<std::io::Error> for ImageError {
    fn from(err: std::io::Error) -> Self {
        Self::Io(err.to_string())
    }
}

impl From<png::DecodingError> for ImageError {
    fn from(err: png::DecodingError) -> Self {
        Self::Decode(err.to_string())
    }
}

/// A loaded image in RGBA8 format.
///
/// Images are stored as raw RGBA8 pixel data, suitable for direct use
/// with renderer texture loading functions.
#[derive(Debug, Clone)]
pub struct Image {
    /// Image width in pixels.
    width: u32,
    /// Image height in pixels.
    height: u32,
    /// Pixel data in RGBA8 format (4 bytes per pixel).
    data: Vec<u8>,
}

impl Image {
    /// Creates a new image with the given dimensions and data.
    ///
    /// # Panics
    ///
    /// Panics if data length doesn't match width * height * 4.
    #[must_use]
    pub fn new(width: u32, height: u32, data: Vec<u8>) -> Self {
        assert_eq!(
            data.len(),
            (width * height * 4) as usize,
            "Image data size mismatch"
        );
        Self {
            width,
            height,
            data,
        }
    }

    /// Creates a solid color image with the given dimensions.
    #[must_use]
    pub fn solid(width: u32, height: u32, r: u8, g: u8, b: u8, a: u8) -> Self {
        let pixel_count = (width * height) as usize;
        let mut data = Vec::with_capacity(pixel_count * 4);
        for _ in 0..pixel_count {
            data.push(r);
            data.push(g);
            data.push(b);
            data.push(a);
        }
        Self {
            width,
            height,
            data,
        }
    }

    /// Loads a PNG image from a file path.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or the PNG is invalid.
    pub fn load_file(path: impl AsRef<Path>) -> Result<Self, ImageError> {
        let file = std::fs::File::open(path.as_ref())?;
        let reader = BufReader::new(file);
        Self::load_png(reader)
    }

    /// Loads a PNG image from a byte slice.
    ///
    /// # Errors
    ///
    /// Returns an error if the data is not a valid PNG.
    pub fn load_bytes(data: &[u8]) -> Result<Self, ImageError> {
        let cursor = std::io::Cursor::new(data);
        Self::load_png(cursor)
    }

    /// Loads a PNG image from any reader.
    fn load_png<R: Read>(reader: R) -> Result<Self, ImageError> {
        let decoder = png::Decoder::new(reader);
        let mut png_reader = decoder.read_info()?;

        let info = png_reader.info();
        let width = info.width;
        let height = info.height;
        let color_type = info.color_type;
        let bit_depth = info.bit_depth;

        // Allocate output buffer
        let output_size = (width * height * 4) as usize;
        let mut output = vec![0u8; output_size];

        // Read the frame
        let mut raw_buffer = vec![0u8; png_reader.output_buffer_size()];
        let frame_info = png_reader.next_frame(&mut raw_buffer)?;
        let raw_data = &raw_buffer[..frame_info.buffer_size()];

        // Convert to RGBA8 based on input format
        convert_to_rgba8(raw_data, &mut output, width, height, color_type, bit_depth)?;

        Ok(Self {
            width,
            height,
            data: output,
        })
    }

    /// Returns the image width in pixels.
    #[inline]
    #[must_use]
    pub const fn width(&self) -> u32 {
        self.width
    }

    /// Returns the image height in pixels.
    #[inline]
    #[must_use]
    pub const fn height(&self) -> u32 {
        self.height
    }

    /// Returns the raw pixel data in RGBA8 format.
    #[inline]
    #[must_use]
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Consumes the image and returns the raw pixel data.
    #[inline]
    #[must_use]
    pub fn into_data(self) -> Vec<u8> {
        self.data
    }

    /// Returns the pixel at the given coordinates.
    ///
    /// Returns `None` if coordinates are out of bounds.
    #[must_use]
    pub fn get_pixel(&self, x: u32, y: u32) -> Option<[u8; 4]> {
        if x >= self.width || y >= self.height {
            return None;
        }
        let idx = ((y * self.width + x) * 4) as usize;
        Some([
            self.data[idx],
            self.data[idx + 1],
            self.data[idx + 2],
            self.data[idx + 3],
        ])
    }

    /// Samples the image with bilinear filtering at normalized UV coordinates.
    ///
    /// UV coordinates are clamped to [0, 1].
    #[must_use]
    pub fn sample(&self, u: f32, v: f32) -> [u8; 4] {
        let u = u.clamp(0.0, 1.0);
        let v = v.clamp(0.0, 1.0);

        let x = u * (self.width - 1) as f32;
        let y = v * (self.height - 1) as f32;

        let x0 = x.floor() as u32;
        let y0 = y.floor() as u32;
        let x1 = (x0 + 1).min(self.width - 1);
        let y1 = (y0 + 1).min(self.height - 1);

        let fx = x.fract();
        let fy = y.fract();

        // Get four neighboring pixels
        let p00 = self.get_pixel(x0, y0).unwrap_or([0, 0, 0, 0]);
        let p10 = self.get_pixel(x1, y0).unwrap_or([0, 0, 0, 0]);
        let p01 = self.get_pixel(x0, y1).unwrap_or([0, 0, 0, 0]);
        let p11 = self.get_pixel(x1, y1).unwrap_or([0, 0, 0, 0]);

        // Bilinear interpolation
        let mut result = [0u8; 4];
        for (i, (((a, b), c), d)) in p00.iter().zip(&p10).zip(&p01).zip(&p11).enumerate() {
            let top = f32::from(*a) * (1.0 - fx) + f32::from(*b) * fx;
            let bottom = f32::from(*c) * (1.0 - fx) + f32::from(*d) * fx;
            result[i] = (top * (1.0 - fy) + bottom * fy) as u8;
        }
        result
    }

    /// Scales the image to the given dimensions using bilinear filtering.
    #[must_use]
    pub fn scale(&self, new_width: u32, new_height: u32) -> Self {
        if new_width == self.width && new_height == self.height {
            return self.clone();
        }

        let mut data = Vec::with_capacity((new_width * new_height * 4) as usize);

        for y in 0..new_height {
            let v = y as f32 / (new_height - 1).max(1) as f32;
            for x in 0..new_width {
                let u = x as f32 / (new_width - 1).max(1) as f32;
                let pixel = self.sample(u, v);
                data.extend_from_slice(&pixel);
            }
        }

        Self {
            width: new_width,
            height: new_height,
            data,
        }
    }

    /// Scales the image to fit within the given dimensions while preserving aspect ratio.
    #[must_use]
    pub fn scale_to_fit(&self, max_width: u32, max_height: u32) -> Self {
        let width_scale = max_width as f32 / self.width as f32;
        let height_scale = max_height as f32 / self.height as f32;
        let scale = width_scale.min(height_scale);

        if scale >= 1.0 {
            return self.clone();
        }

        let new_width = (self.width as f32 * scale).round() as u32;
        let new_height = (self.height as f32 * scale).round() as u32;

        self.scale(new_width, new_height)
    }
}

/// Converts pixel data from various PNG color types to RGBA8.
fn convert_to_rgba8(
    input: &[u8],
    output: &mut [u8],
    width: u32,
    height: u32,
    color_type: png::ColorType,
    bit_depth: png::BitDepth,
) -> Result<(), ImageError> {
    let pixel_count = (width * height) as usize;

    match (color_type, bit_depth) {
        (png::ColorType::Rgba, png::BitDepth::Eight) => {
            // Direct copy
            if input.len() >= output.len() {
                output.copy_from_slice(&input[..output.len()]);
            }
        }
        (png::ColorType::Rgb, png::BitDepth::Eight) => {
            // Add alpha channel
            for i in 0..pixel_count {
                let src_idx = i * 3;
                let dst_idx = i * 4;
                output[dst_idx] = input[src_idx];
                output[dst_idx + 1] = input[src_idx + 1];
                output[dst_idx + 2] = input[src_idx + 2];
                output[dst_idx + 3] = 255; // Opaque
            }
        }
        (png::ColorType::Grayscale, png::BitDepth::Eight) => {
            // Convert grayscale to RGBA
            for (i, &gray) in input.iter().take(pixel_count).enumerate() {
                let dst_idx = i * 4;
                output[dst_idx] = gray;
                output[dst_idx + 1] = gray;
                output[dst_idx + 2] = gray;
                output[dst_idx + 3] = 255;
            }
        }
        (png::ColorType::GrayscaleAlpha, png::BitDepth::Eight) => {
            // Convert grayscale+alpha to RGBA
            for i in 0..pixel_count {
                let src_idx = i * 2;
                let gray = input[src_idx];
                let alpha = input[src_idx + 1];
                let dst_idx = i * 4;
                output[dst_idx] = gray;
                output[dst_idx + 1] = gray;
                output[dst_idx + 2] = gray;
                output[dst_idx + 3] = alpha;
            }
        }
        (png::ColorType::Rgba, png::BitDepth::Sixteen) => {
            // Downsample 16-bit RGBA to 8-bit
            for i in 0..pixel_count {
                let src_idx = i * 8;
                let dst_idx = i * 4;
                output[dst_idx] = input[src_idx]; // High byte of R
                output[dst_idx + 1] = input[src_idx + 2]; // High byte of G
                output[dst_idx + 2] = input[src_idx + 4]; // High byte of B
                output[dst_idx + 3] = input[src_idx + 6]; // High byte of A
            }
        }
        (png::ColorType::Rgb, png::BitDepth::Sixteen) => {
            // Downsample 16-bit RGB to 8-bit RGBA
            for i in 0..pixel_count {
                let src_idx = i * 6;
                let dst_idx = i * 4;
                output[dst_idx] = input[src_idx];
                output[dst_idx + 1] = input[src_idx + 2];
                output[dst_idx + 2] = input[src_idx + 4];
                output[dst_idx + 3] = 255;
            }
        }
        (png::ColorType::Indexed, _) => {
            // Indexed/palette images need the palette to convert
            return Err(ImageError::Unsupported(
                "Indexed/palette PNG images require manual palette expansion".to_string(),
            ));
        }
        _ => {
            return Err(ImageError::Unsupported(format!(
                "Color type {color_type:?} with bit depth {bit_depth:?} not supported"
            )));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_image_solid() {
        let img = Image::solid(2, 2, 255, 0, 0, 128);
        assert_eq!(img.width(), 2);
        assert_eq!(img.height(), 2);
        assert_eq!(img.data().len(), 2 * 2 * 4);

        let pixel = img.get_pixel(0, 0).unwrap();
        assert_eq!(pixel, [255, 0, 0, 128]);
    }

    #[test]
    fn test_image_get_pixel() {
        let mut data = vec![0u8; 4 * 4 * 4]; // 4x4 image
                                             // Set pixel at (1, 1)
        let idx = (1 * 4 + 1) * 4;
        data[idx] = 100;
        data[idx + 1] = 150;
        data[idx + 2] = 200;
        data[idx + 3] = 250;

        let img = Image::new(4, 4, data);
        assert_eq!(img.get_pixel(1, 1), Some([100, 150, 200, 250]));
        assert_eq!(img.get_pixel(0, 0), Some([0, 0, 0, 0]));
        assert_eq!(img.get_pixel(10, 10), None);
    }

    #[test]
    fn test_image_sample() {
        let img = Image::solid(2, 2, 255, 255, 255, 255);
        let sample = img.sample(0.5, 0.5);
        assert_eq!(sample, [255, 255, 255, 255]);
    }

    #[test]
    fn test_image_scale() {
        let img = Image::solid(4, 4, 128, 128, 128, 255);
        let scaled = img.scale(2, 2);
        assert_eq!(scaled.width(), 2);
        assert_eq!(scaled.height(), 2);

        // All pixels should be the same color
        for y in 0..2 {
            for x in 0..2 {
                let pixel = scaled.get_pixel(x, y).unwrap();
                assert_eq!(pixel, [128, 128, 128, 255]);
            }
        }
    }

    #[test]
    fn test_image_scale_to_fit() {
        let img = Image::solid(100, 50, 255, 255, 255, 255);
        let scaled = img.scale_to_fit(50, 50);

        // Should scale to 50x25 (preserving 2:1 aspect ratio)
        assert_eq!(scaled.width(), 50);
        assert_eq!(scaled.height(), 25);
    }

    #[test]
    fn test_image_scale_to_fit_no_upscale() {
        let img = Image::solid(10, 10, 255, 255, 255, 255);
        let scaled = img.scale_to_fit(100, 100);

        // Should not upscale
        assert_eq!(scaled.width(), 10);
        assert_eq!(scaled.height(), 10);
    }

    #[test]
    fn test_convert_rgb_to_rgba() {
        let rgb = [255u8, 128, 64, 200, 100, 50];
        let mut rgba = [0u8; 8];
        convert_to_rgba8(
            &rgb,
            &mut rgba,
            2,
            1,
            png::ColorType::Rgb,
            png::BitDepth::Eight,
        )
        .unwrap();

        assert_eq!(rgba, [255, 128, 64, 255, 200, 100, 50, 255]);
    }

    #[test]
    fn test_convert_grayscale_to_rgba() {
        let gray = [128u8, 64];
        let mut rgba = [0u8; 8];
        convert_to_rgba8(
            &gray,
            &mut rgba,
            2,
            1,
            png::ColorType::Grayscale,
            png::BitDepth::Eight,
        )
        .unwrap();

        assert_eq!(rgba, [128, 128, 128, 255, 64, 64, 64, 255]);
    }

    #[test]
    fn test_image_error_display() {
        let err = ImageError::Io("test error".to_string());
        assert!(err.to_string().contains("test error"));

        let err = ImageError::Decode("decode error".to_string());
        assert!(err.to_string().contains("decode error"));

        let err = ImageError::Unsupported("format error".to_string());
        assert!(err.to_string().contains("format error"));
    }
}

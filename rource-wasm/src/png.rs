//! Minimal, dependency-free PNG encoding for screenshots.
//!
//! This module provides a simple PNG encoder that doesn't require external
//! image processing libraries. It uses uncompressed DEFLATE blocks for simplicity.

use std::io::{self, Write};

/// Maximum bytes per uncompressed DEFLATE block.
const MAX_DEFLATE_BLOCK: usize = 65535;

/// Writes a frame buffer to PNG format.
///
/// # Arguments
///
/// * `writer` - The output writer
/// * `pixels` - Pixel data in ARGB format (0xAARRGGBB)
/// * `width` - Image width in pixels
/// * `height` - Image height in pixels
pub fn write_png<W: Write>(
    writer: &mut W,
    pixels: &[u32],
    width: u32,
    height: u32,
) -> io::Result<()> {
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

    // Prepare raw image data (1 filter byte + 3 RGB bytes per pixel per row)
    let raw_size = (1 + (width as usize) * 3) * height as usize;
    let mut raw_data = Vec::with_capacity(raw_size);

    for y in 0..height as usize {
        raw_data.push(0); // Filter type: None
        for x in 0..width as usize {
            let pixel = pixels[y * width as usize + x];
            raw_data.push(((pixel >> 16) & 0xFF) as u8); // R
            raw_data.push(((pixel >> 8) & 0xFF) as u8); // G
            raw_data.push((pixel & 0xFF) as u8); // B
        }
    }

    // Compress and write IDAT
    let compressed = deflate_compress(&raw_data);
    write_png_chunk(writer, *b"IDAT", &compressed)?;

    // IEND chunk
    write_png_chunk(writer, *b"IEND", &[])?;

    writer.flush()
}

/// Writes a PNG chunk.
fn write_png_chunk<W: Write>(writer: &mut W, chunk_type: [u8; 4], data: &[u8]) -> io::Result<()> {
    writer.write_all(&(data.len() as u32).to_be_bytes())?;
    writer.write_all(&chunk_type)?;
    writer.write_all(data)?;
    let crc = crc32(&chunk_type, data);
    writer.write_all(&crc.to_be_bytes())?;
    Ok(())
}

/// Computes CRC-32 for PNG chunks.
pub fn crc32(chunk_type: &[u8], data: &[u8]) -> u32 {
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

/// Simple DEFLATE compression with zlib wrapper (uncompressed blocks).
///
/// This uses uncompressed DEFLATE blocks for simplicity. The output is valid
/// zlib/DEFLATE data but not optimally compressed.
pub fn deflate_compress(data: &[u8]) -> Vec<u8> {
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

    // Adler-32
    let mut a: u32 = 1;
    let mut b: u32 = 0;
    for &byte in data {
        a = (a + u32::from(byte)) % 65521;
        b = (b + a) % 65521;
    }
    let adler = (b << 16) | a;
    output.extend_from_slice(&adler.to_be_bytes());

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crc32_empty() {
        let result = crc32(b"IEND", &[]);
        // Known CRC32 for empty IEND chunk
        assert_eq!(result, 0xAE42_6082);
    }

    #[test]
    fn test_crc32_ihdr() {
        // Test with a known IHDR chunk (1x1 RGB image)
        let ihdr_data = [
            0, 0, 0, 1, // width = 1
            0, 0, 0, 1, // height = 1
            8, // bit depth
            2, // color type (RGB)
            0, // compression
            0, // filter
            0, // interlace
        ];
        let crc = crc32(b"IHDR", &ihdr_data);
        // Should be a valid non-zero CRC
        assert_ne!(crc, 0);
    }

    #[test]
    fn test_deflate_compress_empty() {
        let result = deflate_compress(&[]);
        // Compressed empty data should have zlib header + empty block + adler32
        assert!(!result.is_empty());
        // Check zlib header
        assert_eq!(result[0], 0x78);
        assert_eq!(result[1], 0x01);
    }

    #[test]
    fn test_deflate_compress_small() {
        let data = b"Hello, World!";
        let result = deflate_compress(data);
        // Compressed data should be larger than original for small data
        // (uncompressed storage adds overhead)
        assert!(!result.is_empty());
        // Should contain the original data
        assert!(result.windows(data.len()).any(|w| w == data));
    }

    #[test]
    fn test_write_png_small_image() {
        // Create a 2x2 red image
        let pixels: Vec<u32> = vec![
            0xFFFF_0000,
            0xFFFF_0000, // Red, Red
            0xFFFF_0000,
            0xFFFF_0000, // Red, Red
        ];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 2, 2).unwrap();

        // Check PNG signature
        assert_eq!(
            &output[0..8],
            &[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        );

        // Check IHDR chunk type
        assert_eq!(&output[12..16], b"IHDR");

        // Output should contain IEND
        assert!(output.windows(4).any(|w| w == b"IEND"));
    }

    #[test]
    fn test_write_png_1x1_pixel() {
        let pixels: Vec<u32> = vec![0xFF00_FF00]; // Green
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 1, 1).unwrap();

        // Should produce valid PNG with signature
        assert!(output.len() > 8);
        assert_eq!(
            &output[0..8],
            &[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        );
    }

    #[test]
    fn test_deflate_compress_repeated_data() {
        // Highly compressible data
        let data = vec![0xAA; 1000];
        let result = deflate_compress(&data);
        // Should still produce valid output
        assert!(!result.is_empty());
    }

    #[test]
    fn test_deflate_compress_random_like_data() {
        // Less compressible data
        let data: Vec<u8> = (0..=255).collect();
        let result = deflate_compress(&data);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_deflate_compress_single_byte() {
        let data = vec![0x42];
        let result = deflate_compress(&data);
        assert!(!result.is_empty());
        // Should contain the original byte
        assert!(result.windows(1).any(|w| w[0] == 0x42));
    }

    #[test]
    fn test_write_png_transparent_pixel() {
        let pixels: Vec<u32> = vec![0x0000_0000]; // Fully transparent
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 1, 1).unwrap();
        // Should still produce valid PNG
        assert!(output.len() > 8);
    }

    #[test]
    fn test_write_png_various_colors() {
        // 4 pixels: red, green, blue, white
        let pixels: Vec<u32> = vec![
            0xFFFF_0000, // Red
            0xFF00_FF00, // Green
            0xFF00_00FF, // Blue
            0xFFFF_FFFF, // White
        ];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 2, 2).unwrap();
        // Check valid PNG signature
        assert_eq!(
            &output[0..8],
            &[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
        );
    }

    #[test]
    fn test_write_png_wide_image() {
        // 10x1 image
        let pixels: Vec<u32> = vec![0xFFFF_FFFF; 10];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 10, 1).unwrap();
        assert!(output.windows(4).any(|w| w == b"IHDR"));
        assert!(output.windows(4).any(|w| w == b"IEND"));
    }

    #[test]
    fn test_write_png_tall_image() {
        // 1x10 image
        let pixels: Vec<u32> = vec![0xFF00_0000; 10];
        let mut output = Vec::new();
        write_png(&mut output, &pixels, 1, 10).unwrap();
        assert!(output.windows(4).any(|w| w == b"IHDR"));
        assert!(output.windows(4).any(|w| w == b"IEND"));
    }
}

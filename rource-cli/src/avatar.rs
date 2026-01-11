//! User avatar loading and management.
//!
//! This module handles loading user avatars from image files.
//! Avatar filenames should match usernames (e.g., "John Doe.png").
//!
//! # Supported Formats
//!
//! Currently only PNG files are supported.
//!
//! # Example
//!
//! ```ignore
//! let mut manager = AvatarManager::load_from_directory("./avatars");
//! let avatar_registry = manager.register_with_renderer(&mut renderer);
//! if let Some(texture_id) = avatar_registry.get_avatar_id("John Doe") {
//!     // Use texture_id for rendering
//! }
//! ```

// PNG/DEFLATE decoder uses explicit binary literals for protocol values
#![allow(clippy::unreadable_literal)]
// Some helper methods reserved for future use
#![allow(dead_code)]
// Variables initialized to default then conditionally assigned in chunk parsing
#![allow(unused_assignments)]
// PNG decoder is self-contained with many small functions; larger ones are acceptable for readability
#![allow(clippy::too_many_lines)]
// PNG format parsing uses explicit casts for clarity
#![allow(clippy::cast_lossless)]
// Comparison chains are clearer than match in binary protocol parsing
#![allow(clippy::comparison_chain)]
// PNG decoder uses standard Result pattern even when errors are unlikely
#![allow(clippy::unnecessary_wraps)]
// Items defined after statements for locality in decoder implementation
#![allow(clippy::items_after_statements)]

use rource_render::{SoftwareRenderer, Texture, TextureId};
use std::collections::HashMap;
use std::path::Path;

/// Manages user avatar images.
#[derive(Debug, Default)]
pub struct AvatarManager {
    /// Loaded avatar textures, keyed by username (lowercase).
    avatars: HashMap<String, Texture>,

    /// Default avatar texture (optional).
    default_avatar: Option<Texture>,
}

/// Registry of avatar `TextureIds` after registration with a renderer.
#[derive(Debug, Default)]
pub struct AvatarRegistry {
    /// Registered avatar texture IDs, keyed by username (lowercase).
    avatar_ids: HashMap<String, TextureId>,

    /// Default avatar texture ID (optional).
    default_avatar_id: Option<TextureId>,
}

impl AvatarRegistry {
    /// Gets the avatar texture ID for a username.
    ///
    /// Returns the user's avatar if found, or the default avatar if set.
    /// Returns `None` if no avatar is available.
    pub fn get_avatar_id(&self, username: &str) -> Option<TextureId> {
        let key = username.to_lowercase();
        self.avatar_ids
            .get(&key)
            .copied()
            .or(self.default_avatar_id)
    }

    /// Returns true if there are any registered avatars.
    #[must_use]
    pub fn has_avatars(&self) -> bool {
        !self.avatar_ids.is_empty() || self.default_avatar_id.is_some()
    }
}

impl AvatarManager {
    /// Creates a new empty avatar manager.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Loads avatars from a directory.
    ///
    /// Avatar filenames should match usernames (case-insensitive).
    /// For example, "John Doe.png" will be matched to user "john doe".
    ///
    /// Supported formats: PNG
    pub fn load_from_directory<P: AsRef<Path>>(path: P) -> Self {
        let mut manager = Self::new();
        let path = path.as_ref();

        if !path.is_dir() {
            eprintln!("Avatar directory not found: {}", path.display());
            return manager;
        }

        // Load all PNG files from the directory
        match std::fs::read_dir(path) {
            Ok(entries) => {
                for entry in entries.flatten() {
                    let file_path = entry.path();
                    if file_path.extension().is_some_and(|ext| ext == "png") {
                        if let Some(stem) = file_path.file_stem() {
                            let username = stem.to_string_lossy().to_lowercase();
                            if let Some(texture) = load_png(&file_path) {
                                manager.avatars.insert(username, texture);
                            }
                        }
                    }
                }
            }
            Err(e) => {
                eprintln!("Failed to read avatar directory: {e}");
            }
        }

        if !manager.avatars.is_empty() {
            eprintln!("Loaded {} avatar(s)", manager.avatars.len());
        }

        manager
    }

    /// Loads a default avatar from a file.
    pub fn set_default_avatar<P: AsRef<Path>>(&mut self, path: P) {
        if let Some(texture) = load_png(path.as_ref()) {
            self.default_avatar = Some(texture);
        }
    }

    /// Registers all loaded avatars with a renderer and returns a registry.
    ///
    /// This consumes the textures and registers them with the renderer,
    /// returning an `AvatarRegistry` that can be used to look up texture IDs.
    pub fn register_with_renderer(self, renderer: &mut SoftwareRenderer) -> AvatarRegistry {
        let mut registry = AvatarRegistry::default();

        // Register all user avatars
        for (username, texture) in self.avatars {
            let texture_id = renderer.register_texture(texture);
            registry.avatar_ids.insert(username, texture_id);
        }

        // Register default avatar if present
        if let Some(texture) = self.default_avatar {
            registry.default_avatar_id = Some(renderer.register_texture(texture));
        }

        registry
    }

    /// Gets the avatar texture for a username.
    ///
    /// Returns the user's avatar if found, or the default avatar if set.
    /// Returns `None` if no avatar is available.
    pub fn get_avatar(&self, username: &str) -> Option<&Texture> {
        let key = username.to_lowercase();
        self.avatars.get(&key).or(self.default_avatar.as_ref())
    }

    /// Gets the avatar texture for a username without falling back to default.
    pub fn get_avatar_exact(&self, username: &str) -> Option<&Texture> {
        let key = username.to_lowercase();
        self.avatars.get(&key)
    }

    /// Returns true if there are any loaded avatars.
    #[must_use]
    pub fn has_avatars(&self) -> bool {
        !self.avatars.is_empty() || self.default_avatar.is_some()
    }

    /// Returns the number of loaded avatars.
    #[must_use]
    pub fn avatar_count(&self) -> usize {
        self.avatars.len()
    }
}

/// Loads a PNG file and returns it as a Texture.
fn load_png(path: &Path) -> Option<Texture> {
    let data = match std::fs::read(path) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Failed to read {}: {e}", path.display());
            return None;
        }
    };

    match decode_png(&data) {
        Ok(texture) => Some(texture),
        Err(e) => {
            eprintln!("Failed to decode {}: {e}", path.display());
            None
        }
    }
}

/// Decodes PNG data into an RGBA texture.
fn decode_png(data: &[u8]) -> Result<Texture, &'static str> {
    // Check PNG signature
    if data.len() < 8 || data[0..8] != [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] {
        return Err("Invalid PNG signature");
    }

    let mut pos = 8;
    let mut width = 0u32;
    let mut height = 0u32;
    let mut bit_depth = 0u8;
    let mut color_type = 0u8;
    let mut compressed_data = Vec::new();

    // Parse chunks
    while pos + 12 <= data.len() {
        let length =
            u32::from_be_bytes([data[pos], data[pos + 1], data[pos + 2], data[pos + 3]]) as usize;
        let chunk_type = &data[pos + 4..pos + 8];
        let chunk_data = &data[pos + 8..pos + 8 + length];

        match chunk_type {
            b"IHDR" => {
                if chunk_data.len() < 13 {
                    return Err("Invalid IHDR chunk");
                }
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
                bit_depth = chunk_data[8];
                color_type = chunk_data[9];

                // We only support 8-bit RGB/RGBA
                if bit_depth != 8 {
                    return Err("Only 8-bit PNGs are supported");
                }
                if color_type != 2 && color_type != 6 {
                    return Err("Only RGB and RGBA PNGs are supported");
                }
            }
            b"IDAT" => {
                compressed_data.extend_from_slice(chunk_data);
            }
            b"IEND" => {
                break;
            }
            _ => {}
        }

        pos += 12 + length;
    }

    if width == 0 || height == 0 {
        return Err("Invalid or missing IHDR chunk");
    }

    // Decompress the image data
    let decompressed = inflate_decompress(&compressed_data)?;

    // Determine bytes per pixel
    let bytes_per_pixel = if color_type == 6 { 4 } else { 3 };
    let expected_raw_size = (1 + width as usize * bytes_per_pixel) * height as usize;

    if decompressed.len() < expected_raw_size {
        return Err("Decompressed data too small");
    }

    // Unfilter and convert to RGBA
    let mut rgba = Vec::with_capacity((width * height * 4) as usize);
    let row_len = 1 + width as usize * bytes_per_pixel;

    for y in 0..height as usize {
        let row_start = y * row_len;
        let filter_type = decompressed[row_start];
        let row_data = &decompressed[row_start + 1..row_start + row_len];

        // Apply reverse filter (we only support filter type 0 = None and 1 = Sub)
        let mut unfiltered = row_data.to_vec();

        match filter_type {
            0 => {} // None - no change needed
            1 => {
                // Sub filter
                for i in bytes_per_pixel..unfiltered.len() {
                    unfiltered[i] = unfiltered[i].wrapping_add(unfiltered[i - bytes_per_pixel]);
                }
            }
            2 => {
                // Up filter
                if y > 0 {
                    let prev_row_start = (y - 1) * row_len + 1;
                    for i in 0..unfiltered.len() {
                        unfiltered[i] =
                            unfiltered[i].wrapping_add(decompressed[prev_row_start + i]);
                    }
                }
            }
            3 => {
                // Average filter
                let prev_row_start = if y > 0 { (y - 1) * row_len + 1 } else { 0 };
                for i in 0..unfiltered.len() {
                    let a = if i >= bytes_per_pixel {
                        unfiltered[i - bytes_per_pixel]
                    } else {
                        0
                    };
                    let b = if y > 0 {
                        decompressed[prev_row_start + i]
                    } else {
                        0
                    };
                    unfiltered[i] =
                        unfiltered[i].wrapping_add(((u16::from(a) + u16::from(b)) / 2) as u8);
                }
            }
            4 => {
                // Paeth filter
                let prev_row_start = if y > 0 { (y - 1) * row_len + 1 } else { 0 };
                for i in 0..unfiltered.len() {
                    let a = if i >= bytes_per_pixel {
                        unfiltered[i - bytes_per_pixel]
                    } else {
                        0
                    };
                    let b = if y > 0 {
                        decompressed[prev_row_start + i]
                    } else {
                        0
                    };
                    let c = if y > 0 && i >= bytes_per_pixel {
                        decompressed[prev_row_start + i - bytes_per_pixel]
                    } else {
                        0
                    };
                    unfiltered[i] = unfiltered[i].wrapping_add(paeth_predictor(a, b, c));
                }
            }
            _ => return Err("Unsupported filter type"),
        }

        // Convert to RGBA
        for x in 0..width as usize {
            let offset = x * bytes_per_pixel;
            let r = unfiltered[offset];
            let g = unfiltered[offset + 1];
            let b = unfiltered[offset + 2];
            let a = if bytes_per_pixel == 4 {
                unfiltered[offset + 3]
            } else {
                255
            };
            rgba.extend_from_slice(&[r, g, b, a]);
        }
    }

    Ok(Texture::new(width, height, rgba))
}

/// Paeth predictor for PNG filtering.
fn paeth_predictor(a: u8, b: u8, c: u8) -> u8 {
    let a = i16::from(a);
    let b = i16::from(b);
    let c = i16::from(c);
    let p = a + b - c;
    let pa = (p - a).abs();
    let pb = (p - b).abs();
    let pc = (p - c).abs();
    if pa <= pb && pa <= pc {
        a as u8
    } else if pb <= pc {
        b as u8
    } else {
        c as u8
    }
}

/// Minimal DEFLATE decompression for PNG IDAT chunks.
///
/// This is a simple implementation that handles common cases.
/// For complex PNGs, a full zlib library would be needed.
fn inflate_decompress(data: &[u8]) -> Result<Vec<u8>, &'static str> {
    if data.len() < 2 {
        return Err("Compressed data too short");
    }

    // Check zlib header
    let cmf = data[0];
    let flg = data[1];

    // CMF = 8 (deflate) + window size (usually 7 = 32K)
    if cmf & 0x0F != 8 {
        return Err("Not deflate compression");
    }

    // Check header checksum
    if (u16::from(cmf) * 256 + u16::from(flg)) % 31 != 0 {
        return Err("Invalid zlib header checksum");
    }

    // Skip dictionary if present
    let has_dict = (flg & 0x20) != 0;
    let start = if has_dict { 6 } else { 2 };

    if start > data.len() {
        return Err("Compressed data too short");
    }

    // Decompress deflate stream
    inflate_raw(&data[start..data.len().saturating_sub(4)])
}

/// Raw DEFLATE decompression.
fn inflate_raw(data: &[u8]) -> Result<Vec<u8>, &'static str> {
    let mut output = Vec::new();
    let mut bit_reader = BitReader::new(data);

    loop {
        let bfinal = bit_reader.read_bits(1)?;
        let btype = bit_reader.read_bits(2)?;

        match btype {
            0 => {
                // Stored block
                bit_reader.align();
                let len = bit_reader.read_u16_le()?;
                let _nlen = bit_reader.read_u16_le()?;
                for _ in 0..len {
                    output.push(bit_reader.read_byte()?);
                }
            }
            1 => {
                // Fixed Huffman
                inflate_block_fixed(&mut bit_reader, &mut output)?;
            }
            2 => {
                // Dynamic Huffman
                inflate_block_dynamic(&mut bit_reader, &mut output)?;
            }
            _ => return Err("Invalid block type"),
        }

        if bfinal == 1 {
            break;
        }
    }

    Ok(output)
}

/// Fixed Huffman code decompression.
fn inflate_block_fixed(reader: &mut BitReader, output: &mut Vec<u8>) -> Result<(), &'static str> {
    loop {
        // Read literal/length code
        let code = read_fixed_literal(reader)?;

        if code < 256 {
            output.push(code as u8);
        } else if code == 256 {
            break;
        } else {
            let length = decode_length(code, reader)?;
            let distance = read_fixed_distance(reader)?;

            if distance > output.len() {
                return Err("Invalid distance");
            }

            let start = output.len() - distance;
            for i in 0..length {
                output.push(output[start + (i % distance)]);
            }
        }
    }
    Ok(())
}

/// Read a fixed Huffman literal/length code.
fn read_fixed_literal(reader: &mut BitReader) -> Result<u16, &'static str> {
    // Read 7 bits
    let mut code = reader.read_bits_rev(7)?;

    if code <= 0b0010111 {
        // 256-279: 7 bits (0000000-0010111)
        Ok(code + 256)
    } else {
        code = (code << 1) | reader.read_bits(1)?;
        if code <= 0b10111111 {
            // 0-143: 8 bits (00110000-10111111)
            Ok(code - 0b00110000)
        } else if code <= 0b11000111 {
            // 280-287: 8 bits (11000000-11000111)
            Ok(code - 0b11000000 + 280)
        } else {
            code = (code << 1) | reader.read_bits(1)?;
            // 144-255: 9 bits (110010000-111111111)
            Ok(code - 0b110010000 + 144)
        }
    }
}

/// Read a fixed Huffman distance code (5 bits, then extra bits).
fn read_fixed_distance(reader: &mut BitReader) -> Result<usize, &'static str> {
    let code = reader.read_bits_rev(5)?;
    decode_distance(code, reader)
}

/// Decode length from code.
fn decode_length(code: u16, reader: &mut BitReader) -> Result<usize, &'static str> {
    let (base, extra_bits) = match code {
        257..=264 => (code as usize - 254, 0),
        265..=268 => (11 + (code as usize - 265) * 2, 1),
        269..=272 => (19 + (code as usize - 269) * 4, 2),
        273..=276 => (35 + (code as usize - 273) * 8, 3),
        277..=280 => (67 + (code as usize - 277) * 16, 4),
        281..=284 => (131 + (code as usize - 281) * 32, 5),
        285 => (258, 0),
        _ => return Err("Invalid length code"),
    };

    let extra = if extra_bits > 0 {
        reader.read_bits(extra_bits)? as usize
    } else {
        0
    };

    Ok(base + extra)
}

/// Decode distance from code.
fn decode_distance(code: u16, reader: &mut BitReader) -> Result<usize, &'static str> {
    if code > 29 {
        return Err("Invalid distance code");
    }

    let extra_bits = if code >= 4 { (code as u8 - 2) / 2 } else { 0 };
    let base = if code < 4 {
        code as usize + 1
    } else {
        (1 << (extra_bits + 1)) + 1 + ((code as usize - extra_bits as usize * 2 - 2) << extra_bits)
    };

    let extra = if extra_bits > 0 {
        reader.read_bits(extra_bits)? as usize
    } else {
        0
    };

    Ok(base + extra)
}

/// Dynamic Huffman code decompression.
fn inflate_block_dynamic(reader: &mut BitReader, output: &mut Vec<u8>) -> Result<(), &'static str> {
    let hlit = reader.read_bits(5)? as usize + 257;
    let hdist = reader.read_bits(5)? as usize + 1;
    let hclen = reader.read_bits(4)? as usize + 4;

    // Read code length code lengths
    const CL_ORDER: [usize; 19] = [
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
    ];
    let mut cl_lengths = [0u8; 19];
    for i in 0..hclen {
        cl_lengths[CL_ORDER[i]] = reader.read_bits(3)? as u8;
    }

    let cl_tree = build_huffman_tree(&cl_lengths)?;

    // Read literal/length and distance code lengths
    let mut lengths = vec![0u8; hlit + hdist];
    let mut i = 0;
    while i < lengths.len() {
        let code = decode_huffman(reader, &cl_tree)?;
        match code {
            0..=15 => {
                lengths[i] = code as u8;
                i += 1;
            }
            16 => {
                let repeat = reader.read_bits(2)? as usize + 3;
                let value = if i > 0 { lengths[i - 1] } else { 0 };
                for _ in 0..repeat {
                    if i < lengths.len() {
                        lengths[i] = value;
                        i += 1;
                    }
                }
            }
            17 => {
                let repeat = reader.read_bits(3)? as usize + 3;
                for _ in 0..repeat {
                    if i < lengths.len() {
                        lengths[i] = 0;
                        i += 1;
                    }
                }
            }
            18 => {
                let repeat = reader.read_bits(7)? as usize + 11;
                for _ in 0..repeat {
                    if i < lengths.len() {
                        lengths[i] = 0;
                        i += 1;
                    }
                }
            }
            _ => return Err("Invalid code length code"),
        }
    }

    let lit_tree = build_huffman_tree(&lengths[..hlit])?;
    let dist_tree = build_huffman_tree(&lengths[hlit..])?;

    // Decode data
    loop {
        let code = decode_huffman(reader, &lit_tree)?;
        if code < 256 {
            output.push(code as u8);
        } else if code == 256 {
            break;
        } else {
            let length = decode_length(code, reader)?;
            let dist_code = decode_huffman(reader, &dist_tree)?;
            let distance = decode_distance(dist_code, reader)?;

            if distance > output.len() {
                return Err("Invalid distance");
            }

            let start = output.len() - distance;
            for i in 0..length {
                output.push(output[start + (i % distance)]);
            }
        }
    }

    Ok(())
}

/// Simple Huffman tree representation.
struct HuffmanTree {
    /// (symbol, `code_length`) pairs sorted by code
    codes: Vec<(u16, u8)>,
}

/// Build a Huffman tree from code lengths.
fn build_huffman_tree(lengths: &[u8]) -> Result<HuffmanTree, &'static str> {
    let mut codes = Vec::new();
    for (sym, &len) in lengths.iter().enumerate() {
        if len > 0 {
            codes.push((sym as u16, len));
        }
    }
    codes.sort_by_key(|&(sym, len)| (len, sym));
    Ok(HuffmanTree { codes })
}

/// Decode one symbol using a Huffman tree.
fn decode_huffman(reader: &mut BitReader, tree: &HuffmanTree) -> Result<u16, &'static str> {
    let mut code = 0u32;
    let mut code_len = 0u8;
    let mut idx = 0;

    loop {
        code = (code << 1) | (reader.read_bits(1)? as u32);
        code_len += 1;

        while idx < tree.codes.len() && tree.codes[idx].1 == code_len {
            if code == idx as u32 {
                return Ok(tree.codes[idx].0);
            }
            idx += 1;
        }

        if code_len > 15 {
            return Err("Invalid Huffman code");
        }
    }
}

/// Bit reader for DEFLATE decompression.
struct BitReader<'a> {
    data: &'a [u8],
    pos: usize,
    bit_pos: u8,
}

impl<'a> BitReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self {
            data,
            pos: 0,
            bit_pos: 0,
        }
    }

    fn read_bits(&mut self, n: u8) -> Result<u16, &'static str> {
        let mut result = 0u16;
        for i in 0..n {
            if self.pos >= self.data.len() {
                return Err("Unexpected end of data");
            }
            let bit = (self.data[self.pos] >> self.bit_pos) & 1;
            result |= (bit as u16) << i;
            self.bit_pos += 1;
            if self.bit_pos == 8 {
                self.bit_pos = 0;
                self.pos += 1;
            }
        }
        Ok(result)
    }

    fn read_bits_rev(&mut self, n: u8) -> Result<u16, &'static str> {
        let bits = self.read_bits(n)?;
        Ok(bits.reverse_bits() >> (16 - n))
    }

    fn read_byte(&mut self) -> Result<u8, &'static str> {
        if self.pos >= self.data.len() {
            return Err("Unexpected end of data");
        }
        let b = self.data[self.pos];
        self.pos += 1;
        Ok(b)
    }

    fn read_u16_le(&mut self) -> Result<u16, &'static str> {
        let lo = self.read_byte()? as u16;
        let hi = self.read_byte()? as u16;
        Ok(lo | (hi << 8))
    }

    fn align(&mut self) {
        if self.bit_pos != 0 {
            self.bit_pos = 0;
            self.pos += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    // Create a minimal valid PNG for testing
    fn create_test_png(width: u32, height: u32, color: (u8, u8, u8, u8)) -> Vec<u8> {
        use std::io::Cursor;

        let mut data = Vec::new();

        // PNG signature
        data.extend_from_slice(&[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]);

        // IHDR chunk
        let ihdr_data = {
            let mut d = Vec::with_capacity(13);
            d.extend_from_slice(&width.to_be_bytes());
            d.extend_from_slice(&height.to_be_bytes());
            d.push(8); // bit depth
            d.push(6); // RGBA color type
            d.push(0); // compression
            d.push(0); // filter
            d.push(0); // interlace
            d
        };
        write_chunk(&mut data, b"IHDR", &ihdr_data);

        // Create raw image data (filter byte 0 + RGBA)
        let mut raw = Vec::new();
        for _ in 0..height {
            raw.push(0); // filter type: None
            for _ in 0..width {
                raw.extend_from_slice(&[color.0, color.1, color.2, color.3]);
            }
        }

        // Compress with simple stored blocks
        let compressed = deflate_store(&raw);
        write_chunk(&mut data, b"IDAT", &compressed);

        // IEND chunk
        write_chunk(&mut data, b"IEND", &[]);

        data
    }

    fn write_chunk(data: &mut Vec<u8>, chunk_type: &[u8; 4], chunk_data: &[u8]) {
        data.extend_from_slice(&(chunk_data.len() as u32).to_be_bytes());
        data.extend_from_slice(chunk_type);
        data.extend_from_slice(chunk_data);
        let crc = crc32(&[chunk_type.as_slice(), chunk_data].concat());
        data.extend_from_slice(&crc.to_be_bytes());
    }

    fn crc32(data: &[u8]) -> u32 {
        let mut crc = 0xFFFF_FFFFu32;
        for &byte in data {
            crc ^= u32::from(byte);
            for _ in 0..8 {
                if crc & 1 != 0 {
                    crc = (crc >> 1) ^ 0xEDB8_8320;
                } else {
                    crc >>= 1;
                }
            }
        }
        !crc
    }

    fn deflate_store(data: &[u8]) -> Vec<u8> {
        let mut result = Vec::new();
        // zlib header (deflate, 32K window)
        result.push(0x78);
        result.push(0x9C);

        // Store blocks (max 65535 bytes each)
        let chunks: Vec<_> = data.chunks(65535).collect();
        for (i, chunk) in chunks.iter().enumerate() {
            let is_last = i == chunks.len() - 1;
            result.push(if is_last { 1 } else { 0 }); // BFINAL + BTYPE=0
            let len = chunk.len() as u16;
            result.extend_from_slice(&len.to_le_bytes());
            result.extend_from_slice(&(!len).to_le_bytes());
            result.extend_from_slice(chunk);
        }

        // Adler-32 checksum
        let adler = adler32(data);
        result.extend_from_slice(&adler.to_be_bytes());

        result
    }

    fn adler32(data: &[u8]) -> u32 {
        let mut a = 1u32;
        let mut b = 0u32;
        for &byte in data {
            a = (a + u32::from(byte)) % 65521;
            b = (b + a) % 65521;
        }
        (b << 16) | a
    }

    #[test]
    fn test_avatar_manager_new() {
        let manager = AvatarManager::new();
        assert!(!manager.has_avatars());
        assert_eq!(manager.avatar_count(), 0);
    }

    #[test]
    fn test_decode_simple_png() {
        // Create a 2x2 red PNG
        let png_data = create_test_png(2, 2, (255, 0, 0, 255));
        let texture = decode_png(&png_data).expect("Failed to decode PNG");

        assert_eq!(texture.width(), 2);
        assert_eq!(texture.height(), 2);

        // Check that pixels are red
        let pixel = texture.get_pixel(0, 0);
        assert_eq!(pixel, (255, 0, 0, 255));
    }

    #[test]
    fn test_decode_invalid_signature() {
        let data = vec![0u8; 100];
        assert!(decode_png(&data).is_err());
    }

    #[test]
    fn test_avatar_manager_get_nonexistent() {
        let manager = AvatarManager::new();
        assert!(manager.get_avatar("nonexistent").is_none());
    }
}

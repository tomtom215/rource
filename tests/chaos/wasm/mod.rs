//! WASM Chaos Testing Module
//!
//! Comprehensive chaos tests for WASM boundary stability, edge cases,
//! and resilience testing. These tests ensure the WASM API can handle
//! any input from the browser environment.

pub mod api_tests;
pub mod memory_tests;
pub mod panic_tests;
pub mod state_tests;

use std::time::Instant;

/// Chaos test result with timing and metrics
#[derive(Debug)]
pub struct ChaosTestResult {
    pub name: String,
    pub passed: bool,
    pub duration_ms: f64,
    pub error: Option<String>,
    pub metrics: ChaosMetrics,
}

/// Metrics collected during chaos tests
#[derive(Debug, Default)]
pub struct ChaosMetrics {
    pub iterations: usize,
    pub allocations_bytes: usize,
    pub peak_memory_bytes: usize,
    pub error_count: usize,
    pub recovery_count: usize,
}

/// Chaos test context for running tests
pub struct ChaosContext {
    start_time: Instant,
    metrics: ChaosMetrics,
}

impl ChaosContext {
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            metrics: ChaosMetrics::default(),
        }
    }

    pub fn elapsed_ms(&self) -> f64 {
        self.start_time.elapsed().as_secs_f64() * 1000.0
    }

    pub fn record_iteration(&mut self) {
        self.metrics.iterations += 1;
    }

    pub fn record_error(&mut self) {
        self.metrics.error_count += 1;
    }

    pub fn record_recovery(&mut self) {
        self.metrics.recovery_count += 1;
    }

    pub fn metrics(&self) -> &ChaosMetrics {
        &self.metrics
    }

    pub fn into_result(self, name: &str, passed: bool, error: Option<String>) -> ChaosTestResult {
        ChaosTestResult {
            name: name.to_string(),
            passed,
            duration_ms: self.elapsed_ms(),
            error,
            metrics: self.metrics,
        }
    }
}

impl Default for ChaosContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Generate random bytes for fuzzing
pub fn random_bytes(len: usize, seed: u64) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(len);
    let mut state = seed;
    for _ in 0..len {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        bytes.push((state >> 56) as u8);
    }
    bytes
}

/// Generate random string with potential unicode chaos
pub fn random_chaos_string(len: usize, seed: u64) -> String {
    let chaos_chars = [
        // Normal ASCII
        'a', 'b', 'c', '1', '2', '3', ' ', '\t', '\n',
        // Unicode edge cases
        '\u{0}', '\u{FEFF}', '\u{200B}', '\u{200C}', '\u{200D}',
        // Emoji
        '🦀', '💀', '🔥', '❌', '✅',
        // RTL characters
        '\u{202E}', '\u{202D}', '\u{202C}',
        // Combining characters
        '\u{0300}', '\u{0301}', '\u{0302}',
        // High surrogate area (invalid UTF-8 if mishandled)
        '\u{FFFD}',
    ];

    let mut result = String::with_capacity(len);
    let mut state = seed;
    for _ in 0..len {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let idx = (state >> 56) as usize % chaos_chars.len();
        result.push(chaos_chars[idx]);
    }
    result
}

/// Generate a malformed log line for fuzzing
pub fn malformed_log_line(variant: usize) -> String {
    match variant % 20 {
        0 => String::new(),                                      // Empty line
        1 => "|".to_string(),                                    // Only delimiter
        2 => "||||".to_string(),                                 // Multiple delimiters
        3 => "no_delimiters_at_all".to_string(),                 // No delimiters
        4 => "\0\0\0".to_string(),                               // Null bytes
        5 => "1234567890|".to_string(),                          // Incomplete
        6 => "|Author|A|".to_string(),                           // Missing timestamp
        7 => "abc|Author|A|path".to_string(),                    // Invalid timestamp
        8 => "-1|Author|A|path".to_string(),                     // Negative timestamp
        9 => "99999999999999|Author|A|path".to_string(),         // Huge timestamp
        10 => "1234567890||A|path".to_string(),                  // Empty author
        11 => "1234567890|Author||path".to_string(),             // Empty action
        12 => "1234567890|Author|X|path".to_string(),            // Invalid action
        13 => "1234567890|Author|A|".to_string(),                // Empty path
        14 => "1234567890|Author|A|/".to_string(),               // Root path only
        15 => format!("1234567890|Author|A|{}", "a".repeat(10000)), // Very long path
        16 => "1234567890|Author|🔥|path".to_string(),           // Emoji action
        17 => "1234567890|Author\x00Name|A|path".to_string(),    // Null in author
        18 => "1234567890|Author|A|path\nembedded".to_string(),  // Embedded newline
        19 => format!("1234567890|{}|A|path", "A".repeat(1000)), // Very long author
        _ => "1234567890|Normal|A|normal/path.rs".to_string(),   // Valid fallback
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chaos_context_creation() {
        let ctx = ChaosContext::new();
        assert_eq!(ctx.metrics().iterations, 0);
        assert_eq!(ctx.metrics().error_count, 0);
    }

    #[test]
    fn test_random_bytes() {
        let bytes = random_bytes(100, 42);
        assert_eq!(bytes.len(), 100);

        // Same seed should produce same result
        let bytes2 = random_bytes(100, 42);
        assert_eq!(bytes, bytes2);

        // Different seed should produce different result
        let bytes3 = random_bytes(100, 43);
        assert_ne!(bytes, bytes3);
    }

    #[test]
    fn test_random_chaos_string() {
        let s = random_chaos_string(50, 42);
        assert!(!s.is_empty());
        // Should be valid UTF-8
        assert!(s.is_char_boundary(0));
    }

    #[test]
    fn test_malformed_log_variants() {
        for i in 0..20 {
            let line = malformed_log_line(i);
            // Should not panic, just produce a string
            assert!(line.len() < 20000);
        }
    }
}

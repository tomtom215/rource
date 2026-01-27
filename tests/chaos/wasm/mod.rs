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

// ===================================================================
// Floyd's Tortoise and Hare Algorithm (Phase 74)
// ===================================================================

/// The LCG multiplier used in chaos tests.
/// This is from PCG: https://www.pcg-random.org/
const LCG_MULTIPLIER: u64 = 6364136223846793005;

/// The LCG increment used in chaos tests.
const LCG_INCREMENT: u64 = 1;

/// Result of cycle detection using Floyd's algorithm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CycleInfo {
    /// Index where cycle begins (μ)
    pub start: usize,
    /// Length of the cycle (λ)
    pub length: usize,
}

/// Detects cycles using Floyd's Tortoise and Hare algorithm.
///
/// This is an O(1) space algorithm for detecting cycles in iterated function sequences.
/// For a function f: S → S, it detects when the sequence x, f(x), f(f(x)), ... repeats.
///
/// # Arguments
/// * `x0` - Initial value
/// * `f` - Iteration function (must be a total function)
/// * `max_iterations` - Maximum iterations before declaring "no short cycle"
///
/// # Returns
/// * `Some(CycleInfo)` if a cycle is detected within max_iterations
/// * `None` if no cycle found within the iteration limit
///
/// # Complexity
/// * Time: O(μ + λ) where μ = tail length, λ = cycle length
/// * Space: O(1) - only two values stored
pub fn floyd_cycle_detect<T, F>(x0: T, mut f: F, max_iterations: u64) -> Option<CycleInfo>
where
    T: PartialEq + Clone,
    F: FnMut(&T) -> T,
{
    // Phase 1: Detect meeting point
    let mut tortoise = f(&x0);
    let mut hare = f(&f(&x0));
    let mut iterations = 0u64;

    while tortoise != hare {
        if iterations >= max_iterations {
            return None; // No short cycle detected
        }

        tortoise = f(&tortoise);
        hare = f(&f(&hare));
        iterations += 1;
    }

    // Phase 2: Find cycle start (μ)
    let mut mu = 0usize;
    tortoise = x0;

    while tortoise != hare {
        tortoise = f(&tortoise);
        hare = f(&hare);
        mu += 1;
    }

    // Phase 3: Find cycle length (λ)
    let mut lambda = 1usize;
    hare = f(&tortoise);

    while tortoise != hare {
        hare = f(&hare);
        lambda += 1;
    }

    Some(CycleInfo {
        start: mu,
        length: lambda,
    })
}

/// Verifies the LCG PRNG doesn't have short cycles using Floyd's algorithm.
///
/// A proper LCG with full period should have period 2^64 for 64-bit state.
/// This function verifies no short cycles exist by sampling.
///
/// # Arguments
/// * `seed` - Initial seed value
/// * `max_check` - Maximum iterations to check (cannot check full 2^64)
///
/// # Returns
/// * `true` if no short cycle detected (PRNG is good for this sample)
/// * `false` if a short cycle was detected (PRNG quality issue)
pub fn verify_lcg_no_short_cycle(seed: u64, max_check: u64) -> bool {
    let f = |x: &u64| x.wrapping_mul(LCG_MULTIPLIER).wrapping_add(LCG_INCREMENT);

    floyd_cycle_detect(seed, f, max_check).is_none()
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

    // ===================================================================
    // Floyd's Tortoise and Hare Algorithm Tests (Phase 74)
    // ===================================================================

    #[test]
    fn test_floyd_simple_cycle() {
        // f(x) = (x + 1) mod 5, starting from 0
        // Sequence: 0 → 1 → 2 → 3 → 4 → 0 → ...
        // μ = 0, λ = 5
        let info = floyd_cycle_detect(0u32, |&x| (x + 1) % 5, 1000)
            .expect("Cycle should be detected");

        assert_eq!(info.start, 0, "Cycle should start at index 0");
        assert_eq!(info.length, 5, "Cycle length should be 5");
    }

    #[test]
    fn test_floyd_tail_and_cycle() {
        // Sequence: 0 → 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 5 → 6 → ...
        // μ = 5 (tail length before cycle), λ = 5 (cycle length)
        let info = floyd_cycle_detect(
            0u32,
            |&x| {
                if x < 5 {
                    x + 1
                } else {
                    5 + (x - 4) % 5
                }
            },
            1000,
        )
        .expect("Cycle should be detected");

        assert_eq!(info.start, 5, "Cycle should start at index 5");
        assert_eq!(info.length, 5, "Cycle length should be 5");
    }

    #[test]
    fn test_floyd_small_lcg() {
        // Small LCG for testing: x_{n+1} = (5*x_n + 1) mod 16
        // This is a full-period LCG with period = 16
        let info = floyd_cycle_detect(0u32, |&x| (5 * x + 1) % 16, 1000)
            .expect("Cycle should be detected");

        assert_eq!(info.start, 0, "Full-period LCG should cycle from start");
        assert_eq!(info.length, 16, "Period should be 16");
    }

    #[test]
    fn test_floyd_no_short_cycle() {
        // Test that large iteration limit returns None when no cycle exists
        // Use a function that won't cycle within the limit
        let info = floyd_cycle_detect(0u64, |&x| x.wrapping_add(1), 100);

        assert!(info.is_none(), "Should not find cycle within 100 iterations");
    }

    #[test]
    fn test_lcg_prng_no_short_cycle() {
        // Verify our LCG doesn't have short cycles
        // Full period is 2^64, we can only sample a small portion
        const MAX_CHECK: u64 = 10_000_000; // 10 million iterations

        // Test with multiple seeds
        for seed in [0u64, 1, 42, 12345, 0xDEADBEEF, u64::MAX] {
            assert!(
                verify_lcg_no_short_cycle(seed, MAX_CHECK),
                "LCG should not have short cycle with seed {}",
                seed
            );
        }
    }

    #[test]
    fn test_lcg_prng_determinism() {
        // Verify LCG produces deterministic sequence
        let mut state1 = 42u64;
        let mut state2 = 42u64;

        for _ in 0..1000 {
            state1 = state1.wrapping_mul(LCG_MULTIPLIER).wrapping_add(LCG_INCREMENT);
            state2 = state2.wrapping_mul(LCG_MULTIPLIER).wrapping_add(LCG_INCREMENT);

            assert_eq!(state1, state2, "LCG should be deterministic");
        }
    }

    #[test]
    fn test_lcg_prng_different_seeds() {
        // Different seeds should produce different sequences
        let mut state1 = 42u64;
        let mut state2 = 43u64;

        state1 = state1.wrapping_mul(LCG_MULTIPLIER).wrapping_add(LCG_INCREMENT);
        state2 = state2.wrapping_mul(LCG_MULTIPLIER).wrapping_add(LCG_INCREMENT);

        assert_ne!(state1, state2, "Different seeds should diverge immediately");
    }

    #[test]
    fn test_cycle_info_equality() {
        let info1 = CycleInfo {
            start: 5,
            length: 10,
        };
        let info2 = CycleInfo {
            start: 5,
            length: 10,
        };
        let info3 = CycleInfo {
            start: 5,
            length: 11,
        };

        assert_eq!(info1, info2);
        assert_ne!(info1, info3);
    }
}

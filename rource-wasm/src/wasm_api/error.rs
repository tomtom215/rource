// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Error metrics and error rate tracking APIs.
//!
//! This module provides methods to query error statistics:
//! - Error counts by category (parse, render, webgl, config, asset, io)
//! - Error rates for monitoring and alerting
//! - Error budget compliance checking
//!
//! # Error Budget SLO
//!
//! The project targets <0.1% total error rate. Individual categories have
//! specific thresholds documented in `docs/operations/ERROR_BUDGET.md`.

use wasm_bindgen::prelude::*;

use crate::metrics::ErrorCategory;
use crate::Rource;

// ============================================================================
// Error Metrics API
// ============================================================================

#[wasm_bindgen]
impl Rource {
    /// Returns the total number of errors recorded across all categories.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const totalErrors = rource.getTotalErrors();
    /// console.log(`Total errors: ${totalErrors}`);
    /// ```
    #[wasm_bindgen(js_name = getTotalErrors)]
    pub fn get_total_errors(&self) -> u64 {
        self.error_metrics.total_errors()
    }

    /// Returns the total number of operations recorded across all categories.
    ///
    /// This is the denominator for error rate calculations.
    #[wasm_bindgen(js_name = getTotalOperations)]
    pub fn get_total_operations(&self) -> u64 {
        self.error_metrics.total_operations()
    }

    /// Returns the error count for parse operations.
    ///
    /// Parse errors occur when loading git logs or custom log formats
    /// with invalid or malformed content.
    #[wasm_bindgen(js_name = getParseErrorCount)]
    pub fn get_parse_error_count(&self) -> u64 {
        self.error_metrics.error_count(ErrorCategory::Parse)
    }

    /// Returns the error count for render operations.
    ///
    /// Render errors occur during frame rendering, such as buffer allocation
    /// failures or texture upload issues.
    #[wasm_bindgen(js_name = getRenderErrorCount)]
    pub fn get_render_error_count(&self) -> u64 {
        self.error_metrics.error_count(ErrorCategory::Render)
    }

    /// Returns the error count for WebGL/wgpu operations.
    ///
    /// WebGL errors include shader compilation failures, context lost events,
    /// and program linking issues.
    #[wasm_bindgen(js_name = getWebGlErrorCount)]
    pub fn get_webgl_error_count(&self) -> u64 {
        self.error_metrics.error_count(ErrorCategory::WebGl)
    }

    /// Returns the error count for configuration operations.
    ///
    /// Config errors occur when invalid settings are provided.
    #[wasm_bindgen(js_name = getConfigErrorCount)]
    pub fn get_config_error_count(&self) -> u64 {
        self.error_metrics.error_count(ErrorCategory::Config)
    }

    /// Returns the error count for asset loading operations.
    ///
    /// Asset errors occur when loading images, fonts, or other resources.
    #[wasm_bindgen(js_name = getAssetErrorCount)]
    pub fn get_asset_error_count(&self) -> u64 {
        self.error_metrics.error_count(ErrorCategory::Asset)
    }

    /// Returns the error count for I/O operations.
    ///
    /// I/O errors occur during file reads or network operations.
    #[wasm_bindgen(js_name = getIoErrorCount)]
    pub fn get_io_error_count(&self) -> u64 {
        self.error_metrics.error_count(ErrorCategory::Io)
    }

    /// Returns the total error rate as a percentage (0.0-100.0).
    ///
    /// Formula: `(total_errors / total_operations) * 100`
    ///
    /// Returns 0.0 if no operations have been recorded.
    ///
    /// # Example
    ///
    /// ```javascript
    /// const errorRate = rource.getErrorRate();
    /// if (errorRate > 0.1) {
    ///     console.warn(`Error rate ${errorRate.toFixed(3)}% exceeds 0.1% threshold`);
    /// }
    /// ```
    #[wasm_bindgen(js_name = getErrorRate)]
    pub fn get_error_rate(&self) -> f64 {
        self.error_metrics.total_error_rate() * 100.0
    }

    /// Returns the parse error rate as a percentage (0.0-100.0).
    ///
    /// Parse errors should be below 0.5% for healthy operation.
    #[wasm_bindgen(js_name = getParseErrorRate)]
    pub fn get_parse_error_rate(&self) -> f64 {
        self.error_metrics.error_rate(ErrorCategory::Parse) * 100.0
    }

    /// Checks if the total error rate exceeds the given threshold.
    ///
    /// # Arguments
    ///
    /// * `threshold_percent` - Maximum acceptable error rate (0.0-100.0)
    ///
    /// # Example
    ///
    /// ```javascript
    /// // Check if error rate exceeds 0.1%
    /// if (rource.errorRateExceedsThreshold(0.1)) {
    ///     showErrorAlert('Error rate too high');
    /// }
    /// ```
    #[wasm_bindgen(js_name = errorRateExceedsThreshold)]
    pub fn error_rate_exceeds_threshold(&self, threshold_percent: f64) -> bool {
        self.error_metrics
            .total_exceeds_threshold(threshold_percent / 100.0)
    }

    /// Resets all error metrics to zero.
    ///
    /// Call this when starting a new session or after recovering from errors.
    ///
    /// # Example
    ///
    /// ```javascript
    /// // Reset metrics for a clean start
    /// rource.resetErrorMetrics();
    /// ```
    #[wasm_bindgen(js_name = resetErrorMetrics)]
    pub fn reset_error_metrics(&mut self) {
        self.error_metrics.reset();
    }

    /// Returns all error metrics as a JSON string.
    ///
    /// This batches all error metrics into a single call to reduce WASM↔JS overhead.
    ///
    /// # Returns
    ///
    /// JSON string with the following structure:
    /// ```json
    /// {
    ///   "parse": 0,
    ///   "render": 0,
    ///   "webgl": 0,
    ///   "config": 0,
    ///   "asset": 0,
    ///   "io": 0,
    ///   "total": 0,
    ///   "rate": 0.0
    /// }
    /// ```
    ///
    /// Note: The `rate` field is in decimal form (0.001 = 0.1%).
    ///
    /// # Example
    ///
    /// ```javascript
    /// const metrics = JSON.parse(rource.getErrorMetrics());
    /// if (metrics.rate > 0.001) {
    ///     console.warn('Error rate exceeds 0.1%');
    /// }
    /// ```
    #[wasm_bindgen(js_name = getErrorMetrics)]
    pub fn get_error_metrics(&self) -> String {
        self.error_metrics.to_json()
    }

    /// Returns detailed error metrics with operation counts as JSON.
    ///
    /// This includes both error counts and operation counts for each category,
    /// enabling more detailed analysis.
    ///
    /// # Returns
    ///
    /// JSON string with the following structure:
    /// ```json
    /// {
    ///   "errors": {
    ///     "parse": 0,
    ///     "render": 0,
    ///     "webgl": 0,
    ///     "config": 0,
    ///     "asset": 0,
    ///     "io": 0
    ///   },
    ///   "operations": {
    ///     "parse": 100,
    ///     "render": 10000,
    ///     "webgl": 1,
    ///     "config": 5,
    ///     "asset": 10,
    ///     "io": 0
    ///   },
    ///   "totals": {
    ///     "errors": 0,
    ///     "operations": 10116,
    ///     "rate": 0.0
    ///   }
    /// }
    /// ```
    #[wasm_bindgen(js_name = getDetailedErrorMetrics)]
    pub fn get_detailed_error_metrics(&self) -> String {
        format!(
            r#"{{"errors":{{"parse":{},"render":{},"webgl":{},"config":{},"asset":{},"io":{}}},"operations":{{"parse":{},"render":{},"webgl":{},"config":{},"asset":{},"io":{}}},"totals":{{"errors":{},"operations":{},"rate":{:.6}}}}}"#,
            self.error_metrics.error_count(ErrorCategory::Parse),
            self.error_metrics.error_count(ErrorCategory::Render),
            self.error_metrics.error_count(ErrorCategory::WebGl),
            self.error_metrics.error_count(ErrorCategory::Config),
            self.error_metrics.error_count(ErrorCategory::Asset),
            self.error_metrics.error_count(ErrorCategory::Io),
            self.error_metrics.operation_count(ErrorCategory::Parse),
            self.error_metrics.operation_count(ErrorCategory::Render),
            self.error_metrics.operation_count(ErrorCategory::WebGl),
            self.error_metrics.operation_count(ErrorCategory::Config),
            self.error_metrics.operation_count(ErrorCategory::Asset),
            self.error_metrics.operation_count(ErrorCategory::Io),
            self.error_metrics.total_errors(),
            self.error_metrics.total_operations(),
            self.error_metrics.total_error_rate()
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metrics::ErrorMetrics;

    #[test]
    fn test_error_metrics_json_format() {
        let metrics = ErrorMetrics::new();
        let json = metrics.to_json();

        // Verify it's valid JSON structure
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));

        // Verify all keys are present
        assert!(json.contains(r#""parse":"#));
        assert!(json.contains(r#""render":"#));
        assert!(json.contains(r#""webgl":"#));
        assert!(json.contains(r#""config":"#));
        assert!(json.contains(r#""asset":"#));
        assert!(json.contains(r#""io":"#));
        assert!(json.contains(r#""total":"#));
        assert!(json.contains(r#""rate":"#));
    }

    #[test]
    fn test_error_metrics_json_with_errors() {
        let mut metrics = ErrorMetrics::new();
        metrics.record_error(ErrorCategory::Parse);
        metrics.record_error(ErrorCategory::Parse);
        metrics.record_error(ErrorCategory::WebGl);

        let json = metrics.to_json();

        assert!(json.contains(r#""parse":2"#));
        assert!(json.contains(r#""webgl":1"#));
        assert!(json.contains(r#""total":3"#));
    }
}

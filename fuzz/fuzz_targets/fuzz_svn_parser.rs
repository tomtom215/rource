// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Fuzz target for the SVN log parser.
//!
//! This fuzzer tests the SvnParser with arbitrary input to find
//! potential panics, hangs, or other unexpected behavior.
//!
//! # Running
//!
//! ```bash
//! cd fuzz
//! cargo +nightly fuzz run fuzz_svn_parser
//! ```

#![no_main]

use libfuzzer_sys::fuzz_target;
use rource_vcs::parser::{Parser, SvnParser};

fuzz_target!(|data: &str| {
    // The parser should never panic on arbitrary input
    let parser = SvnParser::new();
    let _ = parser.parse_str(data);
});

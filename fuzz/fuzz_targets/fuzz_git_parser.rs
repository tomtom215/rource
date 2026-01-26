// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Fuzz target for the Git log parser.
//!
//! This fuzzer tests the GitParser with arbitrary input to find
//! potential panics, hangs, or other unexpected behavior.
//!
//! # Running
//!
//! ```bash
//! cd fuzz
//! cargo +nightly fuzz run fuzz_git_parser
//! ```

#![no_main]

use libfuzzer_sys::fuzz_target;
use rource_vcs::parser::{GitParser, Parser};

fuzz_target!(|data: &str| {
    // The parser should never panic on arbitrary input
    let parser = GitParser::new();
    let _ = parser.parse_str(data);
});

#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

# Test suite for benchmark scripts
# Verifies all benchmark components work correctly

# Note: We use set -u but not -e because test failures should not stop the suite
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Source common.sh but allow it to set its own pipefail
(
    set +e  # Disable exit on error temporarily
    source "${SCRIPT_DIR}/common.sh" 2>/dev/null
) || true
source "${SCRIPT_DIR}/common.sh"

# Test counters
TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

# ==============================================================================
# Test Framework
# ==============================================================================

test_start() {
    local name="$1"
    echo -n "Testing: $name... "
    TESTS_RUN=$((TESTS_RUN + 1))
}

test_pass() {
    echo -e "${GREEN}PASS${NC}"
    TESTS_PASSED=$((TESTS_PASSED + 1))
}

test_fail() {
    local msg="${1:-}"
    echo -e "${RED}FAIL${NC}"
    if [[ -n "$msg" ]]; then
        echo "  Reason: $msg"
    fi
    TESTS_FAILED=$((TESTS_FAILED + 1))
}

# ==============================================================================
# Infrastructure Tests
# ==============================================================================

print_header "Infrastructure Tests"

# Test: Common functions loaded
test_start "common.sh functions"
if type log_info &>/dev/null && type calculate_average &>/dev/null; then
    test_pass
else
    test_fail "Functions not exported"
fi

# Test: Directory structure
test_start "Directory structure"
if [[ -d "$RESULTS_DIR" && -d "$LOGS_DIR" && -d "$TOOLS_DIR" ]]; then
    test_pass
else
    test_fail "Missing directories"
fi

# Test: Rource binary
test_start "Rource binary exists"
if [[ -x "$ROURCE_BIN" ]]; then
    test_pass
else
    test_fail "Binary not found at $ROURCE_BIN"
fi

# Test: Gource binary
test_start "Gource binary exists"
if command -v gource &>/dev/null; then
    test_pass
else
    test_fail "gource not in PATH"
fi

# Test: xvfb available
test_start "xvfb-run available"
if command -v xvfb-run &>/dev/null; then
    test_pass
else
    test_fail "xvfb-run not found"
fi

# ==============================================================================
# Utility Function Tests
# ==============================================================================

print_header "Utility Function Tests"

# Test: format_bytes
test_start "format_bytes function"
RESULT=$(format_bytes 1048576)
if [[ "$RESULT" == "1.00 MB" ]]; then
    test_pass
else
    test_fail "Expected '1.00 MB', got '$RESULT'"
fi

# Test: time_to_seconds
test_start "time_to_seconds (mm:ss)"
RESULT=$(time_to_seconds "1:30.5")
if [[ "$RESULT" == "90.5" ]]; then
    test_pass
else
    test_fail "Expected '90.5', got '$RESULT'"
fi

# Test: time_to_seconds (hh:mm:ss)
test_start "time_to_seconds (hh:mm:ss)"
RESULT=$(time_to_seconds "1:02:30.0")
if [[ "$RESULT" == "3750.0" ]]; then
    test_pass
else
    test_fail "Expected '3750.0', got '$RESULT'"
fi

# Test: calculate_average
test_start "calculate_average function"
echo -e "10\n20\n30" > /tmp/test_avg.txt
RESULT=$(calculate_average /tmp/test_avg.txt)
if [[ "$RESULT" == "20" ]]; then
    test_pass
else
    test_fail "Expected '20', got '$RESULT'"
fi
rm -f /tmp/test_avg.txt

# Test: get_timestamp
test_start "get_timestamp format"
RESULT=$(get_timestamp)
if [[ "$RESULT" =~ ^[0-9]{8}_[0-9]{6}$ ]]; then
    test_pass
else
    test_fail "Expected YYYYMMDD_HHMMSS, got '$RESULT'"
fi

# ==============================================================================
# Tool Functionality Tests
# ==============================================================================

print_header "Tool Functionality Tests"

# Test: Rource --help
test_start "Rource --help"
if "$ROURCE_BIN" --help &>/dev/null; then
    test_pass
else
    test_fail "Rource --help failed"
fi

# Test: Gource --help
test_start "Gource --help"
if gource --help &>/dev/null; then
    test_pass
else
    test_fail "Gource --help failed"
fi

# Test: Rource version
test_start "Rource --version"
if "$ROURCE_BIN" --version &>/dev/null; then
    test_pass
else
    test_fail "Rource --version failed"
fi

# ==============================================================================
# Test Repository Tests
# ==============================================================================

print_header "Test Repository Tests"

# Test: Repository exists
test_start "Test repository exists"
if [[ -d "$TEST_REPO/.git" ]]; then
    test_pass
else
    test_fail "Test repository not found"
fi

# Test: Repository has commits
test_start "Repository has commits"
if cd "$TEST_REPO" && [[ $(git rev-list --count HEAD 2>/dev/null) -gt 0 ]]; then
    test_pass
else
    test_fail "Repository has no commits"
fi

# Test: Can generate custom log
test_start "Custom log generation"
cd "$TEST_REPO"
TEST_LOG="/tmp/test_custom.log"
if git log --pretty=format:"%at|%an|%h" --reverse -10 --name-status 2>/dev/null | head -50 > "$TEST_LOG"; then
    if [[ -s "$TEST_LOG" ]]; then
        test_pass
    else
        test_fail "Generated empty log"
    fi
else
    test_fail "git log command failed"
fi
rm -f "$TEST_LOG"

# Test: Can generate Gource log
test_start "Gource log generation"
cd "$TEST_REPO"
TEST_LOG="/tmp/test_gource.log"
if timeout 30 gource --output-custom-log "$TEST_LOG" . 2>/dev/null; then
    if [[ -s "$TEST_LOG" ]]; then
        test_pass
    else
        test_fail "Generated empty Gource log"
    fi
else
    test_fail "Gource log generation failed"
fi
rm -f "$TEST_LOG"

# ==============================================================================
# Quick Functional Tests
# ==============================================================================

print_header "Quick Functional Tests"

# Create a minimal test log (pipe-delimited format: timestamp|author|action|path)
QUICK_LOG="/tmp/quick_test.log"
cat > "$QUICK_LOG" << 'EOF'
1609459200|Alice|A|file1.txt
1609459300|Bob|M|file1.txt
1609459400|Alice|A|dir/file2.txt
EOF

# Test: Rource can parse custom log
test_start "Rource parse custom log"
ROURCE_OUT="/tmp/rource_quick"
rm -rf "$ROURCE_OUT"
mkdir -p "$ROURCE_OUT"
# Use --stop-at-time to limit the run, and very fast playback (-s 0.001)
if timeout 30 "$ROURCE_BIN" --headless --output "$ROURCE_OUT" --stop-at-time 0.1 \
   -s 0.001 --custom-log "$QUICK_LOG" 2>/dev/null; then
    if ls "$ROURCE_OUT"/*.ppm &>/dev/null; then
        test_pass
    else
        test_fail "No output frames generated"
    fi
else
    test_fail "Rource execution failed"
fi
rm -rf "$ROURCE_OUT"

# Test: Rource headless output
test_start "Rource headless frame generation"
ROURCE_OUT="/tmp/rource_frames"
rm -rf "$ROURCE_OUT"
mkdir -p "$ROURCE_OUT"
# Run for 0.5 seconds at 60fps = ~30 frames
if timeout 30 "$ROURCE_BIN" --headless --output "$ROURCE_OUT" --stop-at-time 0.5 \
   -s 0.001 --width 320 --height 240 --custom-log "$QUICK_LOG" 2>/dev/null; then
    FRAME_COUNT=$(ls "$ROURCE_OUT"/*.ppm 2>/dev/null | wc -l)
    if [[ $FRAME_COUNT -ge 1 ]]; then
        test_pass
    else
        test_fail "Expected frames, got $FRAME_COUNT"
    fi
else
    test_fail "Rource execution failed"
fi
rm -rf "$ROURCE_OUT"

# Test: Gource with xvfb
test_start "Gource via xvfb-run"
cd "$TEST_REPO"
GOURCE_OUT="/tmp/gource_test.ppm"
rm -f "$GOURCE_OUT"
if timeout 30 xvfb-run -a gource --log-format custom "$QUICK_LOG" \
   --stop-at-end -s 1 --output-framerate 60 --viewport 320x240 \
   -o "$GOURCE_OUT" 2>/dev/null; then
    if [[ -s "$GOURCE_OUT" ]]; then
        test_pass
    else
        test_fail "No output generated"
    fi
else
    test_fail "Gource via xvfb failed"
fi
rm -f "$GOURCE_OUT"

# Cleanup
rm -f "$QUICK_LOG"

# ==============================================================================
# Results
# ==============================================================================

print_header "Test Results"

echo "Tests run:    $TESTS_RUN"
echo "Tests passed: $TESTS_PASSED"
echo "Tests failed: $TESTS_FAILED"
echo ""

if [[ $TESTS_FAILED -eq 0 ]]; then
    log_success "All tests passed!"
    exit 0
else
    log_error "$TESTS_FAILED test(s) failed"
    exit 1
fi

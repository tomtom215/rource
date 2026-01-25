#!/bin/bash
# Rource Chaos Testing Suite Runner
#
# Runs comprehensive chaos tests for WASM and UI/UX stability.
# Can be run locally or in CI environments.
#
# Usage:
#   ./scripts/run-chaos-tests.sh              # Run all tests
#   ./scripts/run-chaos-tests.sh --wasm       # Run only WASM tests
#   ./scripts/run-chaos-tests.sh --ui         # Run only UI tests
#   ./scripts/run-chaos-tests.sh --category fuzzing  # Filter by category
#   ./scripts/run-chaos-tests.sh --verbose    # Verbose output
#   ./scripts/run-chaos-tests.sh --report     # Generate HTML report

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default settings
RUN_WASM=true
RUN_UI=true
VERBOSE=false
GENERATE_REPORT=false
CATEGORY=""
TEST_FILTER=""
HEADLESS=false
SEED=$(date +%s)

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --wasm)
            RUN_UI=false
            shift
            ;;
        --ui)
            RUN_WASM=false
            shift
            ;;
        --category)
            CATEGORY="$2"
            shift 2
            ;;
        --test)
            TEST_FILTER="$2"
            shift 2
            ;;
        --verbose|-v)
            VERBOSE=true
            shift
            ;;
        --report)
            GENERATE_REPORT=true
            shift
            ;;
        --headless)
            HEADLESS=true
            shift
            ;;
        --seed)
            SEED="$2"
            shift 2
            ;;
        --help|-h)
            echo "Rource Chaos Testing Suite"
            echo ""
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --wasm         Run only WASM/Rust tests"
            echo "  --ui           Run only UI/JavaScript tests"
            echo "  --category     Filter by category (fuzzing, rapid, network, devices, edge-cases)"
            echo "  --test NAME    Filter by test name pattern"
            echo "  --verbose, -v  Verbose output"
            echo "  --report       Generate HTML report"
            echo "  --headless     Run in headless mode (for CI)"
            echo "  --seed NUM     Random seed for reproducibility"
            echo "  --help, -h     Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

echo -e "${BLUE}"
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║            ROURCE CHAOS TESTING SUITE                        ║"
echo "╠══════════════════════════════════════════════════════════════╣"
echo "║  Testing WASM stability and UI/UX resilience                 ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo -e "${NC}"

echo -e "${YELLOW}Configuration:${NC}"
echo "  Seed:          $SEED"
echo "  WASM tests:    $RUN_WASM"
echo "  UI tests:      $RUN_UI"
echo "  Category:      ${CATEGORY:-all}"
echo "  Test filter:   ${TEST_FILTER:-none}"
echo "  Verbose:       $VERBOSE"
echo "  Report:        $GENERATE_REPORT"
echo "  Headless:      $HEADLESS"
echo ""

# Track results
WASM_PASSED=0
WASM_FAILED=0
UI_PASSED=0
UI_FAILED=0
START_TIME=$(date +%s)

# Create reports directory
mkdir -p tests/chaos/reports

# ============================================================================
# WASM/Rust Chaos Tests
# ============================================================================

if [ "$RUN_WASM" = true ]; then
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}  WASM/Rust Chaos Tests${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    # Build test filter
    TEST_ARGS=""
    if [ -n "$TEST_FILTER" ]; then
        TEST_ARGS="$TEST_FILTER"
    elif [ -n "$CATEGORY" ]; then
        TEST_ARGS="chaos_$CATEGORY"
    else
        TEST_ARGS="chaos"
    fi

    # Run Rust tests from chaos module
    echo -e "${YELLOW}Running cargo test for chaos tests...${NC}"

    if [ "$VERBOSE" = true ]; then
        if cargo test "$TEST_ARGS" --no-fail-fast -- --nocapture 2>&1; then
            echo -e "${GREEN}✓ All WASM chaos tests passed${NC}"
        else
            echo -e "${RED}✗ Some WASM chaos tests failed${NC}"
            WASM_FAILED=1
        fi
    else
        if cargo test "$TEST_ARGS" --no-fail-fast 2>&1 | tee /tmp/chaos-wasm-output.txt; then
            WASM_PASSED=$(grep -c "test result: ok" /tmp/chaos-wasm-output.txt 2>/dev/null || echo "0")
            echo -e "${GREEN}✓ WASM chaos tests completed${NC}"
        else
            WASM_FAILED=1
            echo -e "${RED}✗ Some WASM chaos tests failed${NC}"
        fi
    fi

    echo ""
fi

# ============================================================================
# UI/JavaScript Chaos Tests
# ============================================================================

if [ "$RUN_UI" = true ]; then
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}  UI/JavaScript Chaos Tests${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    # Check if Node.js is available
    if ! command -v node &> /dev/null; then
        echo -e "${YELLOW}⚠ Node.js not found, skipping UI tests${NC}"
        echo "  Install Node.js to run UI chaos tests"
    else
        # Create a Node.js test runner wrapper
        cat > /tmp/run-ui-chaos.mjs << 'NODERUNNER'
import { createChaosTestSuite } from './tests/chaos/ui/core/test-runner.js';
import { fuzzingTests } from './tests/chaos/ui/scenarios/fuzzing.js';
import { rapidTests } from './tests/chaos/ui/scenarios/rapid.js';
import { networkTests } from './tests/chaos/ui/scenarios/network.js';
import { deviceTests } from './tests/chaos/ui/scenarios/devices.js';
import { edgeCaseTests } from './tests/chaos/ui/scenarios/edge-cases.js';

const args = process.argv.slice(2);
const options = {
    verbose: args.includes('--verbose'),
    categories: args.find(a => a.startsWith('--category='))?.split('=')[1] || null,
    testFilter: args.find(a => a.startsWith('--test='))?.split('=')[1] || null,
    seed: parseInt(args.find(a => a.startsWith('--seed='))?.split('=')[1] || Date.now()),
};

const suite = createChaosTestSuite('UI Chaos Tests', options);

// Register all tests
suite.tests(fuzzingTests);
suite.tests(rapidTests);
suite.tests(networkTests);
suite.tests(deviceTests);
suite.tests(edgeCaseTests);

// Run tests
const report = await suite.run();

// Output results
console.log('');
console.log('━'.repeat(60));
console.log(`  Total:   ${report.summary.total}`);
console.log(`  Passed:  ${report.summary.passed}`);
console.log(`  Failed:  ${report.summary.failed}`);
console.log(`  Rate:    ${report.summary.passRate.toFixed(1)}%`);
console.log('━'.repeat(60));

// Exit with appropriate code
process.exit(report.summary.failed > 0 ? 1 : 0);
NODERUNNER

        echo -e "${YELLOW}Running Node.js UI chaos tests...${NC}"

        NODE_ARGS=""
        [ "$VERBOSE" = true ] && NODE_ARGS="$NODE_ARGS --verbose"
        [ -n "$CATEGORY" ] && NODE_ARGS="$NODE_ARGS --category=$CATEGORY"
        [ -n "$TEST_FILTER" ] && NODE_ARGS="$NODE_ARGS --test=$TEST_FILTER"
        NODE_ARGS="$NODE_ARGS --seed=$SEED"

        if node --experimental-vm-modules /tmp/run-ui-chaos.mjs $NODE_ARGS 2>&1; then
            echo -e "${GREEN}✓ UI chaos tests completed${NC}"
        else
            UI_FAILED=1
            echo -e "${RED}✗ Some UI chaos tests failed${NC}"
        fi

        rm -f /tmp/run-ui-chaos.mjs
    fi

    echo ""
fi

# ============================================================================
# Summary
# ============================================================================

END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}  CHAOS TEST SUMMARY${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""
echo "  Duration:     ${DURATION}s"
echo "  Seed:         $SEED"
echo ""

TOTAL_FAILED=$((WASM_FAILED + UI_FAILED))

if [ $TOTAL_FAILED -eq 0 ]; then
    echo -e "${GREEN}╔══════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║                    ALL TESTS PASSED                          ║${NC}"
    echo -e "${GREEN}╚══════════════════════════════════════════════════════════════╝${NC}"
    exit 0
else
    echo -e "${RED}╔══════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${RED}║                    SOME TESTS FAILED                         ║${NC}"
    echo -e "${RED}╚══════════════════════════════════════════════════════════════╝${NC}"
    echo ""
    echo "To reproduce failures, run with the same seed:"
    echo "  ./scripts/run-chaos-tests.sh --seed $SEED"
    exit 1
fi

/**
 * Chaos Reporter - Generates test reports in various formats
 *
 * Produces JSON and HTML reports for chaos test results.
 */

export class ChaosReporter {
    constructor(options = {}) {
        this.options = {
            outputDir: options.outputDir || 'tests/chaos/reports',
            includePassedDetails: options.includePassedDetails || false,
            ...options,
        };
    }

    /**
     * Generate JSON report
     */
    toJSON(report) {
        return JSON.stringify(report, null, 2);
    }

    /**
     * Generate HTML report
     */
    toHTML(report) {
        const passRate = report.summary.passRate.toFixed(1);
        const statusClass = report.summary.failed === 0 ? 'success' : 'failure';
        const statusText = report.summary.failed === 0 ? 'ALL TESTS PASSED' : 'TESTS FAILED';

        return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Chaos Test Report - ${report.timestamp}</title>
    <style>
        :root {
            --bg: #1a1a2e;
            --surface: #16213e;
            --text: #eaeaea;
            --text-dim: #a0a0a0;
            --success: #00d26a;
            --failure: #ff6b6b;
            --warning: #feca57;
            --info: #54a0ff;
            --border: #2d3748;
        }

        * {
            box-sizing: border-box;
            margin: 0;
            padding: 0;
        }

        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif;
            background: var(--bg);
            color: var(--text);
            line-height: 1.6;
            padding: 2rem;
        }

        .container {
            max-width: 1200px;
            margin: 0 auto;
        }

        h1, h2, h3 {
            margin-bottom: 1rem;
        }

        h1 {
            font-size: 2rem;
            border-bottom: 2px solid var(--border);
            padding-bottom: 0.5rem;
        }

        h2 {
            font-size: 1.5rem;
            margin-top: 2rem;
        }

        .header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 2rem;
        }

        .status {
            padding: 0.5rem 1rem;
            border-radius: 4px;
            font-weight: bold;
            font-size: 1.2rem;
        }

        .status.success {
            background: var(--success);
            color: #000;
        }

        .status.failure {
            background: var(--failure);
            color: #000;
        }

        .summary-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 1rem;
            margin-bottom: 2rem;
        }

        .summary-card {
            background: var(--surface);
            padding: 1.5rem;
            border-radius: 8px;
            border: 1px solid var(--border);
        }

        .summary-card h3 {
            font-size: 0.9rem;
            color: var(--text-dim);
            text-transform: uppercase;
            margin-bottom: 0.5rem;
        }

        .summary-card .value {
            font-size: 2rem;
            font-weight: bold;
        }

        .summary-card .value.success { color: var(--success); }
        .summary-card .value.failure { color: var(--failure); }
        .summary-card .value.info { color: var(--info); }

        .category-section {
            background: var(--surface);
            border-radius: 8px;
            margin-bottom: 1rem;
            border: 1px solid var(--border);
            overflow: hidden;
        }

        .category-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 1rem 1.5rem;
            background: rgba(255,255,255,0.05);
            cursor: pointer;
        }

        .category-header:hover {
            background: rgba(255,255,255,0.08);
        }

        .category-stats {
            display: flex;
            gap: 1rem;
        }

        .stat {
            padding: 0.25rem 0.5rem;
            border-radius: 4px;
            font-size: 0.85rem;
        }

        .stat.passed { background: var(--success); color: #000; }
        .stat.failed { background: var(--failure); color: #000; }
        .stat.skipped { background: var(--text-dim); color: #000; }

        .test-list {
            border-top: 1px solid var(--border);
        }

        .test-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 0.75rem 1.5rem;
            border-bottom: 1px solid var(--border);
        }

        .test-item:last-child {
            border-bottom: none;
        }

        .test-item.passed { border-left: 3px solid var(--success); }
        .test-item.failed { border-left: 3px solid var(--failure); }

        .test-name {
            font-family: 'Monaco', 'Consolas', monospace;
            font-size: 0.9rem;
        }

        .test-duration {
            color: var(--text-dim);
            font-size: 0.85rem;
        }

        .failure-details {
            background: var(--surface);
            border-radius: 8px;
            padding: 1.5rem;
            margin-top: 2rem;
            border: 1px solid var(--failure);
        }

        .failure-item {
            margin-bottom: 1.5rem;
            padding-bottom: 1.5rem;
            border-bottom: 1px solid var(--border);
        }

        .failure-item:last-child {
            margin-bottom: 0;
            padding-bottom: 0;
            border-bottom: none;
        }

        .failure-name {
            font-weight: bold;
            color: var(--failure);
            margin-bottom: 0.5rem;
        }

        .failure-message {
            font-family: monospace;
            background: rgba(0,0,0,0.3);
            padding: 1rem;
            border-radius: 4px;
            white-space: pre-wrap;
            overflow-x: auto;
        }

        .metrics-table {
            width: 100%;
            border-collapse: collapse;
            margin-top: 1rem;
        }

        .metrics-table th,
        .metrics-table td {
            padding: 0.75rem;
            text-align: left;
            border-bottom: 1px solid var(--border);
        }

        .metrics-table th {
            background: rgba(255,255,255,0.05);
            font-weight: normal;
            color: var(--text-dim);
        }

        .footer {
            margin-top: 3rem;
            padding-top: 1rem;
            border-top: 1px solid var(--border);
            color: var(--text-dim);
            font-size: 0.85rem;
        }

        @media (max-width: 768px) {
            body {
                padding: 1rem;
            }

            .header {
                flex-direction: column;
                gap: 1rem;
            }

            .summary-grid {
                grid-template-columns: 1fr 1fr;
            }
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>Chaos Test Report</h1>
            <span class="status ${statusClass}">${statusText}</span>
        </div>

        <div class="summary-grid">
            <div class="summary-card">
                <h3>Total Tests</h3>
                <div class="value info">${report.summary.total}</div>
            </div>
            <div class="summary-card">
                <h3>Passed</h3>
                <div class="value success">${report.summary.passed}</div>
            </div>
            <div class="summary-card">
                <h3>Failed</h3>
                <div class="value failure">${report.summary.failed}</div>
            </div>
            <div class="summary-card">
                <h3>Pass Rate</h3>
                <div class="value ${report.summary.failed === 0 ? 'success' : 'failure'}">${passRate}%</div>
            </div>
            <div class="summary-card">
                <h3>Duration</h3>
                <div class="value info">${(report.duration / 1000).toFixed(2)}s</div>
            </div>
            <div class="summary-card">
                <h3>Seed</h3>
                <div class="value" style="font-size: 1rem; font-family: monospace;">${report.seed}</div>
            </div>
        </div>

        ${this.renderCategories(report)}

        ${this.renderFailures(report)}

        ${this.renderChaosMetrics(report)}

        <div class="footer">
            <p>Generated: ${report.timestamp}</p>
            <p>Rource Chaos Testing Suite</p>
        </div>
    </div>
</body>
</html>`;
    }

    /**
     * Render category sections
     */
    renderCategories(report) {
        const categories = Object.entries(report.categories || {});

        if (categories.length === 0) {
            return '';
        }

        return `
        <h2>Test Categories</h2>
        ${categories.map(([name, stats]) => `
            <div class="category-section">
                <div class="category-header">
                    <h3>${name}</h3>
                    <div class="category-stats">
                        <span class="stat passed">${stats.passed} passed</span>
                        ${stats.failed > 0 ? `<span class="stat failed">${stats.failed} failed</span>` : ''}
                        ${stats.skipped > 0 ? `<span class="stat skipped">${stats.skipped} skipped</span>` : ''}
                    </div>
                </div>
                <div class="test-list">
                    ${this.renderTestsForCategory(report, name)}
                </div>
            </div>
        `).join('')}`;
    }

    /**
     * Render tests for a category
     */
    renderTestsForCategory(report, category) {
        const tests = (report.results || []).filter(r => r.category === category);

        return tests.map(test => `
            <div class="test-item ${test.passed ? 'passed' : 'failed'}">
                <span class="test-name">${test.name}</span>
                <span class="test-duration">${test.duration.toFixed(0)}ms</span>
            </div>
        `).join('');
    }

    /**
     * Render failure details
     */
    renderFailures(report) {
        const failures = report.failures || [];

        if (failures.length === 0) {
            return '';
        }

        return `
        <h2>Failure Details</h2>
        <div class="failure-details">
            ${failures.map(f => `
                <div class="failure-item">
                    <div class="failure-name">${f.category}/${f.name}</div>
                    <div class="failure-message">${this.escapeHtml(f.error?.message || 'Unknown error')}</div>
                </div>
            `).join('')}
        </div>`;
    }

    /**
     * Render chaos metrics
     */
    renderChaosMetrics(report) {
        const metrics = report.chaosMetrics;

        if (!metrics) {
            return '';
        }

        return `
        <h2>Chaos Metrics</h2>
        <div class="category-section">
            <table class="metrics-table">
                <tr>
                    <th>Metric</th>
                    <th>Value</th>
                </tr>
                <tr>
                    <td>Chaos Events Injected</td>
                    <td>${metrics.chaosEventsInjected}</td>
                </tr>
                <tr>
                    <td>Errors Triggered</td>
                    <td>${metrics.errorsTriggered}</td>
                </tr>
                <tr>
                    <td>Successful Recoveries</td>
                    <td>${metrics.recoveriesSuccessful}</td>
                </tr>
            </table>
        </div>`;
    }

    /**
     * Escape HTML special characters
     */
    escapeHtml(str) {
        const escapes = {
            '&': '&amp;',
            '<': '&lt;',
            '>': '&gt;',
            '"': '&quot;',
            "'": '&#039;',
        };
        return String(str).replace(/[&<>"']/g, c => escapes[c]);
    }

    /**
     * Generate console report
     */
    toConsole(report) {
        const lines = [];

        lines.push('');
        lines.push('='.repeat(60));
        lines.push('  CHAOS TEST REPORT');
        lines.push('='.repeat(60));
        lines.push('');
        lines.push(`  Timestamp: ${report.timestamp}`);
        lines.push(`  Duration:  ${(report.duration / 1000).toFixed(2)}s`);
        lines.push(`  Seed:      ${report.seed}`);
        lines.push('');
        lines.push('-'.repeat(60));
        lines.push('  SUMMARY');
        lines.push('-'.repeat(60));
        lines.push('');
        lines.push(`  Total:     ${report.summary.total}`);
        lines.push(`  Passed:    ${report.summary.passed}`);
        lines.push(`  Failed:    ${report.summary.failed}`);
        lines.push(`  Skipped:   ${report.summary.skipped}`);
        lines.push(`  Pass Rate: ${report.summary.passRate.toFixed(1)}%`);
        lines.push('');

        // Categories
        lines.push('-'.repeat(60));
        lines.push('  BY CATEGORY');
        lines.push('-'.repeat(60));
        lines.push('');

        for (const [name, stats] of Object.entries(report.categories || {})) {
            const status = stats.failed > 0 ? 'FAIL' : 'PASS';
            lines.push(`  ${name.padEnd(20)} ${status} (${stats.passed}/${stats.total})`);
        }
        lines.push('');

        // Failures
        if ((report.failures || []).length > 0) {
            lines.push('-'.repeat(60));
            lines.push('  FAILURES');
            lines.push('-'.repeat(60));
            lines.push('');

            for (const f of report.failures) {
                lines.push(`  ${f.category}/${f.name}`);
                lines.push(`    ${f.error?.message || 'Unknown error'}`);
                lines.push('');
            }
        }

        lines.push('='.repeat(60));
        lines.push('');

        return lines.join('\n');
    }

    /**
     * Generate JUnit XML report (for CI integration)
     */
    toJUnit(report) {
        const escapeXml = (str) => {
            return String(str)
                .replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&apos;');
        };

        const testcases = (report.results || []).map(r => {
            if (r.passed) {
                return `    <testcase name="${escapeXml(r.name)}" classname="${escapeXml(r.category)}" time="${(r.duration / 1000).toFixed(3)}"/>`;
            } else {
                return `    <testcase name="${escapeXml(r.name)}" classname="${escapeXml(r.category)}" time="${(r.duration / 1000).toFixed(3)}">
      <failure message="${escapeXml(r.error?.message || 'Unknown error')}">${escapeXml(r.error?.stack || '')}</failure>
    </testcase>`;
            }
        }).join('\n');

        return `<?xml version="1.0" encoding="UTF-8"?>
<testsuite name="chaos-tests" tests="${report.summary.total}" failures="${report.summary.failed}" skipped="${report.summary.skipped}" time="${(report.duration / 1000).toFixed(3)}" timestamp="${report.timestamp}">
${testcases}
</testsuite>`;
    }
}

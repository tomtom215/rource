// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Insights Formatting & Utility Functions
 *
 * Shared formatting helpers used by both the insights tab renderers
 * and the table rendering functions.
 */

/**
 * Formats a number with the specified decimal places using locale formatting.
 * @param {number|null} n - Number to format
 * @param {number} decimals - Number of decimal places
 * @returns {string} Formatted number or 'N/A'
 */
export function formatNumber(n, decimals = 2) {
    if (n == null || isNaN(n) || !isFinite(n)) return 'N/A';
    return Number(n).toLocaleString(undefined, {
        minimumFractionDigits: decimals,
        maximumFractionDigits: decimals,
    });
}

/**
 * Formats a number with fixed decimal places (no locale grouping).
 * @param {number|null} n - Number to format
 * @param {number} decimals - Number of decimal places
 * @returns {string} Formatted number or 'N/A'
 */
export function formatFixed(n, decimals = 1) {
    if (n == null || !isFinite(n)) return 'N/A';
    return Number(n).toFixed(decimals);
}

/**
 * Formats an integer with locale grouping (e.g., 1,234).
 * @param {number|null} n - Number to format
 * @returns {string} Formatted integer or em-dash
 */
export function formatInt(n) {
    if (n == null || !isFinite(n)) return '\u2014';
    return Number(n).toLocaleString();
}

/**
 * Formats a decimal ratio as a percentage (e.g., 0.25 -> "25.0%").
 * @param {number|null} n - Ratio to format (0-1 scale)
 * @returns {string} Formatted percentage or 'N/A'
 */
export function formatPercentage(n) {
    if (n == null || !isFinite(n)) return 'N/A';
    return (Number(n) * 100).toFixed(1) + '%';
}

/**
 * Truncates a file path for display, preserving first and last segments.
 * @param {string} path - File path to truncate
 * @returns {string} Truncated path (max ~40 chars)
 */
export function truncatePath(path) {
    if (!path) return '';
    if (path.length <= 40) return path;
    const parts = path.split('/');
    if (parts.length <= 3) return path;
    const tail = parts.slice(-2).join('/');
    return parts[0] + '/\u2026/' + tail;
}

/**
 * Escapes special HTML characters to prevent XSS.
 * @param {string} str - String to escape
 * @returns {string} HTML-safe string
 */
export function escapeHtml(str) {
    if (!str) return '';
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/**
 * Capitalizes the first letter of a string.
 * @param {string} str - String to capitalize
 * @returns {string} Capitalized string
 */
export function capitalize(str) {
    if (!str) return '';
    return str.charAt(0).toUpperCase() + str.slice(1);
}

/**
 * Interprets a Gini coefficient as a human-readable inequality level.
 * @param {number|null} gini - Gini coefficient (0-1)
 * @returns {string} Human-readable interpretation
 */
export function giniInterpretation(gini) {
    if (gini == null || isNaN(gini)) return 'N/A';
    if (gini < 0.3) return 'Low inequality (healthy)';
    if (gini < 0.5) return 'Moderate inequality';
    if (gini < 0.7) return 'High inequality';
    return 'Very high inequality (risk)';
}

/**
 * Renders an empty state with contextual explanation.
 * @param {string} message - Primary message
 * @param {string} [hint] - Explanation of what data is needed
 * @returns {string} HTML string
 */
export function emptyState(message, hint) {
    let html = `<div class="insights-empty"><p>${escapeHtml(message)}</p>`;
    if (hint) {
        html += `<p class="insights-empty-hint">${escapeHtml(hint)}</p>`;
    }
    html += '</div>';
    return html;
}

// ============================================================================
// Tooltip Data Registry
//
// Plain-English explanations and algorithm details for every insight metric.
// Keys must match the exact title string passed to renderMetricSection().
// The `math` field may contain <code> HTML tags for formula formatting.
// ============================================================================

const TOOLTIP = {
    'Technology Distribution': {
        plain: 'Shows which programming languages are used in your project by counting file extensions. Gives you a quick overview of your tech stack.',
        math: '<code>pct(lang) = files_with_extension / total_files \u00d7 100</code>. Extensions mapped to languages via lookup table. Primary language = language with highest file count. Source: <code>insights/tech_distribution.rs</code>'
    },
    'File Hotspots': {
        plain: 'The files that change most frequently. Research shows that frequently-changed files are where most bugs are introduced.',
        math: '<code>score = \u03a3(w\u1d62)</code> where <code>w\u1d62 = e^(-\u03bb \u00d7 age_days)</code> \u2014 exponential decay weights recent changes higher. Sorted by weighted score descending. Source: <code>insights/hotspot.rs</code>'
    },
    'Change Entropy': {
        plain: 'Measures whether your changes are focused (touching few files) or scattered (touching many files at once). Scattered changes indicate growing complexity.',
        math: 'Shannon entropy: <code>H = -\u03a3(p\u1d62 \u00d7 log\u2082(p\u1d62))</code>, normalized to [0,1] by dividing by <code>log\u2082(n)</code>. <code>p\u1d62</code> = fraction of changes in file <code>i</code> per commit window. H=0: all changes in one file, H=1: perfectly spread. Source: <code>insights/change_entropy.rs</code>'
    },
    'Change Bursts': {
        plain: 'Files that get edited many times in rapid succession \u2014 often a sign of emergency fixes or unstable code that keeps breaking.',
        math: 'A burst = \u22653 changes to the same file within a sliding time window. <code>burst_length = consecutive_rapid_changes</code>. Multi-author bursts count coordination events. Source: <code>insights/change_bursts.rs</code>'
    },
    'Bus Factor': {
        plain: 'How many people would need to leave before an area of code becomes unmaintainable. A bus factor of 1 is a critical risk.',
        math: 'For each directory, find the minimum set of contributors whose combined commit ownership exceeds 50%. <code>bus_factor = |min_set|</code>. Ownership = commits by contributor / total commits in directory. Source: <code>insights/index.rs</code>'
    },
    'Knowledge Silos': {
        plain: 'Files where only one person has ever made changes. If that person is unavailable, nobody else knows the code.',
        math: 'Knowledge entropy: <code>H = -\u03a3(p\u1d62 \u00d7 ln(p\u1d62))</code> where <code>p\u1d62</code> = contributor <code>i</code>\'s commit share. A silo is a file with <code>contributor_count = 1</code> (entropy = 0). Source: <code>insights/knowledge.rs</code>'
    },
    'Ownership Fragmentation': {
        plain: 'Measures how unevenly commits are distributed among contributors for each file. High fragmentation means one person dominates a file.',
        math: 'Gini coefficient: <code>G = \u03a3\u1d62 \u03a3\u2c7c |x\u1d62 - x\u2c7c| / (2n\u00b2\u03bc)</code> where <code>x</code> = commit counts per contributor. G=0: perfectly equal, G=1: one person owns all. Bird et al. threshold: &lt;5% share = minor contributor. Source: <code>insights/ownership_fragmentation.rs</code>'
    },
    'Knowledge Distribution': {
        plain: 'How widely knowledge is spread across your team for each directory. Low distribution means one person holds all the knowledge.',
        math: 'Shannon entropy: <code>H = -\u03a3(p\u1d62 \u00d7 log\u2082(p\u1d62))</code>, normalized by <code>log\u2082(n)</code>. 0 = one person knows everything, 1 = perfectly distributed across all contributors. Source: <code>insights/knowledge_distribution.rs</code>'
    },
    'Truck Factor (DOA Model)': {
        plain: 'An enhanced bus factor using the Degree of Authorship model. Measures how many developers must leave before more than half of files lose all experts.',
        math: '<code>DOA(d,f) = 3.293 + 1.098\u00d7FA + 0.164\u00d7DL - 0.321\u00d7AC</code>. FA = first author (binary), DL = fraction of deliveries by developer d, AC = accepted changes count. Expert threshold: <code>DOA &gt; 0.75</code>. Truck factor = min developers whose removal orphans &gt;50% of files. Source: <code>insights/truck_factor.rs</code>'
    },
    'Turnover Impact': {
        plain: 'Shows developers who stopped contributing and the files they left without anyone else who knows the code well enough to maintain it.',
        math: 'Departed = no commits in last 90 days. Orphaned file = departed developer held &gt;50% commit share with no remaining active contributor above 25%. <code>orphan_rate = orphaned_files / total_files</code>. Source: <code>insights/turnover_impact.rs</code>'
    },
    'Circadian Risk': {
        plain: 'Commits made late at night (midnight\u20134 AM) are statistically more likely to introduce bugs. Tired developers make more mistakes.',
        math: 'High-risk window: 00:00\u201304:00 UTC (Eyolfson et al. 2011). <code>high_risk_pct = commits_in_window / total_commits \u00d7 100</code>. Hourly risk score computed from commit timestamp distribution. Source: <code>insights/circadian.rs</code>'
    },
    'Developer Profiles': {
        plain: 'Classifies each contributor by their involvement level: core maintainers who drive the project, peripheral contributors, or drive-by one-time committers.',
        math: 'Core: &gt;5% of total commits AND active in &gt;50% of project months. Peripheral: &gt;1 commit but below core thresholds. Drive-by: 1\u20132 commits total (Mockus et al. 2002 classification). Source: <code>insights/profiles.rs</code>'
    },
    'Commit Cadence': {
        plain: 'How regularly each developer commits. Steady patterns suggest sustained engagement; bursty patterns may indicate deadline-driven work.',
        math: 'Coefficient of variation: <code>CV = \u03c3 / \u03bc</code> where <code>\u03bc</code> = mean commit interval (days), <code>\u03c3</code> = standard deviation. Low CV = regular cadence, high CV = bursty. Source: <code>insights/cadence.rs</code>'
    },
    'Collaboration Network': {
        plain: 'Maps which developers work on the same files. A well-connected network means the team shares knowledge more easily.',
        math: 'Graph density: <code>D = 2E / (N \u00d7 (N-1))</code> where E = file co-edit edges, N = developers. Connected components via BFS. <code>avg_degree = 2E / N</code>. Source: <code>insights/network.rs</code>'
    },
    'Contribution Inequality': {
        plain: 'Are commits spread evenly across the team or dominated by a few people? Like income inequality, but for code contributions.',
        math: 'Gini coefficient: <code>G = \u03a3\u1d62 \u03a3\u2c7c |c\u1d62 - c\u2c7c| / (2n\u00b2\u03bc)</code> where <code>c</code> = commits per developer. <code>top_20_share = commits_by_top_20% / total_commits</code>. Source: <code>insights/inequality.rs</code>'
    },
    'Developer Focus': {
        plain: 'How specialized each developer is \u2014 do they work deeply in one area, or spread thinly across the whole codebase?',
        math: '<code>focus = 1 - H_norm</code> where <code>H_norm = H / log\u2082(k)</code>, <code>H = -\u03a3(p\u1d62 \u00d7 log\u2082(p\u1d62))</code>, <code>p\u1d62</code> = fraction of commits in directory <code>i</code>, <code>k</code> = directories touched. Focus=1: single area, Focus\u22480: everywhere. Source: <code>insights/focus.rs</code>'
    },
    'Developer Experience': {
        plain: 'A composite score of how experienced each developer is with this specific project, based on their tenure, commit volume, and file breadth.',
        math: '<code>score = tenure_months \u00d7 ln(1 + commits) \u00d7 file_familiarity</code> where <code>file_familiarity = unique_files_touched / total_files</code>. Normalized to [0, 100]. Source: <code>insights/developer_experience.rs</code>'
    },
    'Technology Expertise': {
        plain: 'What technologies each developer works with, determined by the file types they modify. Reveals skill sets and specializations.',
        math: 'Per developer: commits grouped by file extension \u2192 mapped to language. <code>primary_tech = argmax(commits_per_lang)</code>. <code>breadth = |distinct_languages|</code>. Source: <code>insights/tech_expertise.rs</code>'
    },
    'Activity Patterns': {
        plain: 'When your team does the most work \u2014 peak hours and days of the week. Helps identify if work happens in focused bursts or steady streams.',
        math: 'Hourly histogram of commit timestamps (UTC). <code>peak_hour = argmax(count[h])</code>. Burst detection: commits in sliding window exceeding <code>\u03bc + 2\u03c3</code> threshold. Source: <code>insights/temporal.rs</code>'
    },
    'Commit Heatmap': {
        plain: 'A visual grid showing when commits happen, broken down by day of week and hour of day. Highlights peak development windows and off-hours activity.',
        math: '7\u00d724 matrix: <code>M[day][hour] = commit_count</code>. Color levels: L0=0, L1=1\u201325th percentile, L2=25\u201350th, L3=50\u201375th, L4=75\u2013100th. Source: <code>insights/activity_heatmap.rs</code>'
    },
    'Codebase Growth': {
        plain: 'Whether your project is growing, stable, or shrinking over time. Tracks the net change in file count across the project lifetime.',
        math: '<code>net_growth = \u03a3(creates) - \u03a3(deletes)</code>. <code>monthly_rate = \u0394files / \u0394months</code>. Trend classification via linear regression slope of monthly file counts (Lehman\'s Laws of Software Evolution). Source: <code>insights/growth.rs</code>'
    },
    'File Lifecycles': {
        plain: 'Categorizes each file by its stage: actively changing, mature and stable, short-lived (ephemeral), or abandoned (dead).',
        math: 'Active: changed within 90 days. Stable: exists &gt;90 days, no recent changes. Ephemeral: created and deleted within 30 days. Dead: no changes in &gt;180 days. <code>churn = (creates + deletes) / total_files</code>. Source: <code>insights/lifecycle.rs</code>'
    },
    'File Survival': {
        plain: 'How long files last before being deleted, using the same survival analysis method that medical researchers use for patient outcomes.',
        math: 'Kaplan-Meier estimator: <code>S(t) = \u220f(1 - d\u1d62/n\u1d62)</code> for <code>t\u1d62 \u2264 t</code>, where <code>d\u1d62</code> = deletions at time <code>t\u1d62</code>, <code>n\u1d62</code> = files at risk. Median survival = <code>t</code> where <code>S(t) = 0.5</code>. Source: <code>insights/survival.rs</code>'
    },
    'Release Rhythm': {
        plain: 'Detects whether your project follows a regular release cycle or ships ad-hoc. Regular cadence is a sign of mature engineering.',
        math: 'Velocity = commits per 7-day window. Peaks detected via z-score &gt; 1.5\u03c3. <code>regularity = 1 - CV(peak_intervals)</code>. Phase: PostRelease (velocity drop), Building (rising), Quiet (below mean). Source: <code>insights/release_rhythm.rs</code>'
    },
    'Work Type Mix': {
        plain: 'The balance between building new features, maintaining existing code, and cleaning up. Too much of any one type can signal problems.',
        math: 'Classification by dominant action type per commit: Feature = predominantly creates. Maintenance = predominantly modifies. Cleanup = predominantly deletes. <code>pct = type_commits / total \u00d7 100</code>. Source: <code>insights/work_type.rs</code>'
    },
    'Modularity': {
        plain: 'When you change a file, do you also have to change files in other directories? High modularity means changes stay contained within their module.',
        math: '<code>M = 1 - (cross_module_changes / total_changes)</code>. A change is cross-module when a commit touches files in \u22652 directories. M=1: perfectly modular, M=0: every change ripples everywhere. Source: <code>insights/modularity.rs</code>'
    },
    'Sociotechnical Congruence': {
        plain: 'Checks whether developers who work on related code actually communicate and coordinate. Gaps in coordination lead to integration bugs.',
        math: '<code>congruence = actual / required</code>. Required = developer pairs editing coupled files. Actual = developer pairs who co-edited files. <code>gaps = required - actual</code>. Source: <code>insights/congruence.rs</code>'
    },
    'Churn Volatility': {
        plain: 'Files with erratic change patterns \u2014 alternating between bursts of activity and calm periods. More predictive of bugs than total churn alone.',
        math: 'Per-file coefficient of variation: <code>CV = \u03c3(window_changes) / \u03bc(window_changes)</code>. Volatile: CV &gt; 1.5. Stable: CV \u2264 1.5. Nagappan et al. showed CV predicts defects better than raw churn count. Source: <code>insights/churn_volatility.rs</code>'
    },
    'Commit Complexity': {
        plain: 'Large commits that touch many files across many directories are harder to review and more error-prone. Smaller, focused commits are safer.',
        math: '<code>complexity = files_changed \u00d7 dirs_changed \u00d7 action_types</code>. Tangled = complexity above 95th percentile. Action types: {create, modify, delete}. Source: <code>insights/commit_complexity.rs</code>'
    },
    'Defect-Introducing Patterns': {
        plain: 'Files that get burst-edited right after a large commit \u2014 a strong signal that the big commit introduced bugs that need immediate fixing.',
        math: 'Large commit: <code>files_changed &gt; \u03bc + 2\u03c3</code>. Burst-after-large: \u22653 edits to same file within 3 days. <code>risk_score = burst_count \u00d7 recency_weight</code>. Based on SZZ algorithm (Sliwerski et al. 2005). Source: <code>insights/defect_patterns.rs</code>'
    },
    'Change Coupling': {
        plain: 'Files that always change together in the same commit, even without direct code dependencies. These hidden dependencies make the codebase harder to maintain.',
        math: '<code>support = co_change_count</code>. <code>confidence = support / changes_A</code>. <code>lift = support \u00d7 N / (changes_A \u00d7 changes_B)</code>. Lift &gt; 1 = positive association (Agrawal et al. 1993 association rules). Source: <code>insights/coupling.rs</code>'
    },
};

/**
 * Renders a metric section with title, description, content, and optional "Why it matters".
 * Automatically includes an info tooltip button when tooltip data exists for the metric.
 * @param {string} title - Section heading
 * @param {string} description - Metric description (may contain HTML entities)
 * @param {string|Array<{text: string, url: string}>} citation - Academic citation:
 *   string for plain text, or array of {text, url} for clickable DOI links
 * @param {string} content - Inner HTML content (table, key-value list, etc.)
 * @param {string} [whyItMatters] - Optional contextual explanation
 * @returns {string} HTML string
 */
export function renderMetricSection(title, description, citation, content, whyItMatters) {
    const tooltip = TOOLTIP[title];
    const infoBtn = tooltip
        ? ` <button class="insights-info-btn" aria-label="Details about ${escapeHtml(title)}" aria-expanded="false" type="button"></button>`
        : '';
    const detailPanel = tooltip
        ? `<div class="insights-info-panel" hidden>
            <div class="insights-info-section">
                <strong class="insights-info-label">In plain English</strong>
                <p>${escapeHtml(tooltip.plain)}</p>
            </div>
            <div class="insights-info-section">
                <strong class="insights-info-label">The algorithm</strong>
                <p>${tooltip.math}</p>
            </div>
        </div>`
        : '';

    const metricId = slugify(title);

    let html = `<div class="insights-metric" id="${metricId}">
        <div class="insights-metric-header">
            <h4 class="insights-metric-title">${escapeHtml(title)}</h4>${infoBtn}
        </div>${detailPanel}
        <p class="insights-metric-desc">${description}</p>
        ${content}`;
    if (whyItMatters) {
        html += `<p class="insights-metric-why"><strong>Why it matters:</strong> ${whyItMatters}</p>`;
    }
    html += `<cite class="insights-citation">${renderCitation(citation)}</cite>
    </div>`;
    return html;
}

/**
 * Renders a citation as clickable links or plain text.
 * @param {string|Array<{text: string, url: string}>} citation
 * @returns {string} HTML string with links or plain text
 */
function renderCitation(citation) {
    if (typeof citation === 'string') return citation;
    if (!Array.isArray(citation)) return '';
    return citation.map(c =>
        c.url
            ? `<a href="${escapeHtml(c.url)}" target="_blank" rel="noopener noreferrer" class="insights-citation-link">${escapeHtml(c.text)}</a>`
            : escapeHtml(c.text)
    ).join('; ');
}

/**
 * Renders a tab introduction with title and description.
 * Provides context before the metrics, explaining what the tab shows
 * and why it matters in plain language.
 * @param {string} title - Intro heading
 * @param {string} description - Plain-language explanation
 * @returns {string} HTML string
 */
export function renderTabIntro(title, description) {
    return `<div class="insights-tab-intro">
        <div>
            <strong>${escapeHtml(title)}</strong>
            <p>${escapeHtml(description)}</p>
        </div>
    </div>`;
}

/**
 * Renders a list of key-value pairs.
 * @param {Array<[string, string]>} pairs - Key-value pairs
 * @returns {string} HTML string
 */
export function renderKeyValueList(pairs) {
    const rows = pairs.map(([key, value]) =>
        `<div class="insights-kv-row">
            <span class="insights-kv-key">${escapeHtml(key)}</span>
            <span class="insights-kv-value">${escapeHtml(String(value))}</span>
        </div>`
    ).join('');
    return `<div class="insights-kv-list">${rows}</div>`;
}

/**
 * Converts a metric title to a URL-safe ID for anchor navigation.
 * @param {string} str - Title string
 * @returns {string} Slugified ID with "metric-" prefix
 */
function slugify(str) {
    return 'metric-' + str.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
}

/**
 * Renders a quick-navigation bar of pill buttons for the metrics in a tab.
 * Clicking a pill smooth-scrolls to the corresponding metric section.
 * @param {string[]} titles - Metric titles in display order
 * @returns {string} HTML string
 */
export function renderMetricNav(titles) {
    const pills = titles.map(t =>
        `<button class="insights-metric-pill" data-target="${slugify(t)}" type="button">${escapeHtml(t)}</button>`
    ).join('');
    return `<nav class="insights-metric-nav" aria-label="Jump to metric">${pills}</nav>`;
}

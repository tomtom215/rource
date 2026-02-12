// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Insights Tab Renderer Functions
 *
 * Each function renders the content for one analytics tab (Hotspots, Risk,
 * Team, Temporal, Quality). Data sources are documented with verified
 * field names from rource-wasm/src/wasm_api/insights.rs.
 */

import {
    formatNumber, formatFixed, formatInt, formatPercentage,
    escapeHtml, capitalize, giniInterpretation, emptyState,
    renderMetricSection, renderTabIntro, renderKeyValueList
} from './insights-utils.js';

import {
    renderHotspotsTable, renderBusFactorTable, renderBurstsTable,
    renderKnowledgeTable, renderCouplingTable, renderProfilesTable,
    renderCadenceTable, renderFocusTable, renderExperienceTable,
    renderOwnershipTable, renderKnowledgeDistributionTable,
    renderChurnVolatilityTable, renderTruckFactorTable,
    renderTurnoverImpactTable, renderCommitComplexityTable,
    renderDefectPatternsTable, renderTechDistributionTable,
    renderActivityHeatmapTable, renderTechExpertiseTable
} from './insights-tables.js';

/**
 * Hotspots tab: file hotspots, change entropy, change bursts.
 *
 * Data sources (all verified against insights.rs):
 * - cachedData.hotspots: flat array from getHotspots()
 *   Fields: path, totalChanges, weightedChanges, score, creates, modifies, deletes
 *   (insights.rs:786-796)
 * - cachedData.entropy: unwrapped from getChangeEntropy().changeEntropy
 *   Fields: windows[], avgNormalizedEntropy, maxEntropyWindowIdx, trend
 *   (insights.rs:486-509)
 * - cachedData.bursts: unwrapped from getChangeBursts().changeBursts
 *   Fields: files[], totalBursts, avgBurstLength, filesWithBursts, multiAuthorBurstCount
 *   (insights.rs:562-582)
 */
export function renderHotspotsTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Change Hotspots',
        'Files that change most often are where bugs hide. This tab identifies the riskiest files in your codebase.'
    ));

    // Technology distribution — fields verified: insights.rs write_tech_distribution_json
    const td = cachedData.techDistribution;
    if (td) {
        const langs = td.languages || [];
        parts.push(renderMetricSection(
            'Technology Distribution',
            'The languages and technologies in the repository, classified by file extension from the active file set.',
            'Mockus et al. 2002, TOSEM; Kalliamvakou et al. 2016, EMSE',
            langs.length > 0
                ? renderTechDistributionTable(langs)
                : emptyState('No files detected', 'Technology distribution requires files with recognized extensions.'),
            td.primaryLanguage
                ? `Primary language: ${escapeHtml(td.primaryLanguage)} (${formatNumber(td.primaryLanguagePct, 1)}% of ${formatInt(td.totalFiles)} files). ${formatInt(td.languageCount)} languages detected.`
                : null
        ));
    }

    // Hotspots table — fields verified: insights.rs:786-796
    const hotspots = cachedData.hotspots;
    parts.push(renderMetricSection(
        'File Hotspots',
        'The most frequently changed files, weighted by recency so recent changes count more.',
        'Nagappan et al. 2005, ICSE',
        hotspots && hotspots.length > 0
            ? renderHotspotsTable(hotspots)
            : emptyState('No hotspot files detected', 'Hotspots require files with multiple modifications over time.'),
        'Files that change often are statistically more likely to contain bugs. Focus code reviews and testing on these files first.'
    ));

    // Change entropy — fields verified: insights.rs:486-509
    const e = cachedData.entropy;
    if (e) {
        const entropyHealth = e.avgNormalizedEntropy > 0.8 ? 'high' : e.avgNormalizedEntropy > 0.5 ? 'moderate' : 'low';
        parts.push(renderMetricSection(
            'Change Entropy',
            'How spread out are changes across files? High entropy means changes touch many files at once; low entropy means changes are focused.',
            'Hassan 2009, ICSE',
            renderKeyValueList([
                ['Average Entropy', formatNumber(e.avgNormalizedEntropy, 3) + ` (${entropyHealth})`],
                ['Trend', escapeHtml(e.trend || 'stable')],
                ['Windows Analyzed', formatInt(e.windows ? e.windows.length : 0)],
            ]),
            'Rising entropy often signals growing complexity \u2014 changes that used to be simple start requiring edits in many files.'
        ));
    }

    // Change bursts — fields verified: insights.rs:562-582
    const b = cachedData.bursts;
    if (b) {
        const files = b.files || [];
        parts.push(renderMetricSection(
            'Change Bursts',
            'Files that get edited many times in quick succession \u2014 often a sign of urgent fixes or unstable code.',
            'Nagappan et al. 2010, ICSE',
            files.length > 0
                ? renderBurstsTable(files)
                : emptyState('No change bursts detected', 'Bursts require rapid consecutive changes to the same file.'),
            'Burst patterns often indicate "fix-then-fix-again" cycles. These files may need refactoring.'
        ));
    }

    return parts.join('');
}

/**
 * Risk tab: bus factor, knowledge silos, ownership fragmentation, knowledge distribution, truck factor, turnover impact, circadian risk.
 *
 * Data sources:
 * - cachedData.busFactors: flat array from getBusFactors()
 *   Fields: directory, busFactor, fileCount, contributorCount, criticalContributors
 *   (insights.rs:858-876)
 * - cachedData.knowledge: unwrapped from getKnowledgeMap().knowledge
 *   Fields: files[], directories[], totalSilos, siloPct, avgEntropy
 *   File fields: path, entropy, isSilo, primaryOwner, contributorCount
 *   (insights.rs:336-372)
 * - cachedData.ownershipFrag: unwrapped from getOwnershipFragmentation().ownershipFragmentation
 *   Fields: avgGini, fragmentedCount, concentratedCount, files[]
 *   (insights.rs:1698-1705)
 * - cachedData.knowledgeDist: unwrapped from getKnowledgeDistribution().knowledgeDistribution
 *   Fields: avgNormalizedEntropy, concentratedCount, distributedCount, directories[]
 *   (insights.rs:1737-1747)
 * - cachedData.circadian: unwrapped from getCircadianRisk().circadian
 *   Fields: files[], authors[], hourlyRisk[], highRiskPct, totalCommitsAnalyzed
 *   (insights.rs:513-556)
 */
export function renderRiskTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Risk Assessment',
        'Spots where your team is vulnerable — single points of failure, knowledge concentration, and risky commit patterns.'
    ));

    // Bus factors — fields verified: insights.rs:858-876
    const bus = cachedData.busFactors;
    const criticalCount = bus ? bus.filter(b => b.busFactor <= 1).length : 0;
    parts.push(renderMetricSection(
        'Bus Factor',
        'If a key contributor leaves, can someone else maintain this code? A bus factor of 1 means a single person controls it.',
        'Bird et al. 2011, FSE',
        bus && bus.length > 0
            ? renderBusFactorTable(bus)
            : emptyState('No bus factor data', 'Requires 2+ contributors to compute bus factor.'),
        criticalCount > 0
            ? `${criticalCount} director${criticalCount === 1 ? 'y has' : 'ies have'} a bus factor of 1 \u2014 consider cross-training or pair reviews.`
            : 'All directories have distributed ownership \u2014 good team resilience.'
    ));

    // Knowledge silos — fields verified: insights.rs:336-372
    const k = cachedData.knowledge;
    if (k) {
        const silos = (k.files || []).filter(f => f.isSilo);
        parts.push(renderMetricSection(
            'Knowledge Silos',
            'Files where only one person has ever made changes. If that person is unavailable, nobody else knows the code.',
            'Rigby &amp; Bird 2013',
            silos.length > 0
                ? renderKnowledgeTable(silos)
                : emptyState('No knowledge silos detected', 'All files have distributed ownership.'),
            silos.length > 0
                ? 'Consider code reviews with a second person on these files to spread knowledge.'
                : null
        ));
    }

    // Ownership fragmentation — fields verified: insights.rs:1698-1705
    const of = cachedData.ownershipFrag;
    if (of) {
        const files = of.files || [];
        const fragHealth = of.avgGini > 0.5 ? 'high fragmentation' : of.avgGini > 0.3 ? 'moderate fragmentation' : 'healthy ownership';
        parts.push(renderMetricSection(
            'Ownership Fragmentation',
            'Per-file Gini coefficient measuring how unevenly commit ownership is distributed. High Gini means one person dominates; low Gini means shared ownership.',
            'Bird et al. 2011, FSE; Greiler et al. 2015',
            files.length > 0
                ? renderOwnershipTable(files)
                : emptyState('No ownership data', 'Requires files with 2+ contributors to measure fragmentation.'),
            `Average Gini: ${formatNumber(of.avgGini, 3)} (${fragHealth}). ${of.fragmentedCount || 0} fragmented files, ${of.concentratedCount || 0} concentrated files.`
        ));
    }

    // Knowledge distribution — fields verified: insights.rs:1737-1747
    const kd = cachedData.knowledgeDist;
    if (kd) {
        const dirs = kd.directories || [];
        const distHealth = kd.avgNormalizedEntropy > 0.7 ? 'well-distributed' : kd.avgNormalizedEntropy > 0.3 ? 'moderately distributed' : 'concentrated';
        parts.push(renderMetricSection(
            'Knowledge Distribution',
            'Shannon entropy of contributor distribution per directory. Low entropy means knowledge is concentrated in few people; high entropy means it\u2019s well-spread.',
            'Constantinou &amp; Mens 2017; Fritz et al. 2010',
            dirs.length > 0
                ? renderKnowledgeDistributionTable(dirs)
                : emptyState('No directory distribution data', 'Requires directories with 2+ contributors.'),
            `Average entropy: ${formatNumber(kd.avgNormalizedEntropy, 3)} (${distHealth}). ${kd.concentratedCount || 0} concentrated directories need attention.`
        ));
    }

    // Enhanced truck factor — fields verified: insights.rs write_truck_factor_json
    const tf = cachedData.truckFactor;
    if (tf) {
        const devs = tf.rankedDevelopers || [];
        parts.push(renderMetricSection(
            'Truck Factor (DOA Model)',
            'Enhanced truck factor using the Degree of Authorship model. How many developers must leave before >50% of files lose all experts?',
            'Avelino et al. 2016, ICPC',
            devs.length > 0
                ? renderTruckFactorTable(devs)
                : emptyState('No truck factor data', 'Requires files with commit history.'),
            `Truck factor: ${tf.truckFactor || 0}. ${formatNumber(tf.singleExpertPct, 1)}% of files have only one expert.`
        ));
    }

    // Developer turnover impact — fields verified: insights.rs write_turnover_impact_json
    const ti = cachedData.turnoverImpact;
    if (ti) {
        const departed = ti.departedDevelopers || [];
        parts.push(renderMetricSection(
            'Turnover Impact',
            'Developers who stopped contributing and the files they left without a knowledgeable successor.',
            'Mockus 2009, ICSE; Rigby et al. 2016',
            departed.length > 0
                ? renderTurnoverImpactTable(departed)
                : emptyState('No departed developers detected', 'All contributors are still active (committed within last 90 days).'),
            ti.departedCount > 0
                ? `${ti.departedCount} departed developer${ti.departedCount === 1 ? '' : 's'}, ${ti.totalOrphanedFiles || 0} orphaned files (${formatNumber(ti.orphanRate, 1)}% orphan rate).`
                : 'No developer turnover detected \u2014 team is stable.'
        ));
    }

    // Circadian risk — fields verified: insights.rs:513-556
    const c = cachedData.circadian;
    if (c) {
        let peakRiskHour = 0;
        if (c.hourlyRisk && c.hourlyRisk.length > 0) {
            let maxRisk = -1;
            c.hourlyRisk.forEach((r, i) => {
                if (r > maxRisk) { maxRisk = r; peakRiskHour = i; }
            });
        }
        parts.push(renderMetricSection(
            'Circadian Risk',
            'Commits made in the early hours (midnight\u20134 AM) are statistically buggier \u2014 tired developers make more mistakes.',
            'Eyolfson et al. 2011, MSR',
            renderKeyValueList([
                ['High-Risk Commits', formatFixed(c.highRiskPct, 1) + '%'],
                ['Peak Risk Hour', `${peakRiskHour}:00 UTC`],
                ['Total Analyzed', formatInt(c.totalCommitsAnalyzed || 0)],
            ]),
            c.highRiskPct > 20
                ? 'Over 20% of commits are in high-risk hours \u2014 consider encouraging more regular working hours.'
                : 'Most commits happen during normal hours \u2014 low circadian risk.'
        ));
    }

    return parts.join('');
}

/**
 * Team tab: developer profiles, cadence, network, inequality, focus, experience.
 *
 * Data sources:
 * - cachedData.profiles: unwrapped from getDeveloperProfiles().profiles
 *   (insights.rs:376-403)
 * - cachedData.cadence: unwrapped from getCommitCadence().cadence
 *   (insights.rs:304-332)
 * - cachedData.network: unwrapped from getDeveloperNetwork().network
 *   (insights.rs:698-723)
 * - cachedData.inequality: unwrapped from getContributionInequality().inequality
 *   (insights.rs:446-475)
 * - cachedData.focus: unwrapped from getDeveloperFocus().focus
 *   (insights.rs:586-620)
 * - cachedData.experience: unwrapped from getDeveloperExperience().developerExperience
 *   (insights.rs:1671-1679)
 */
export function renderTeamTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Team Dynamics',
        'How your team works together — who contributes what, how often, and how well they collaborate.'
    ));

    // Developer profiles — fields verified: insights.rs:376-403
    const p = cachedData.profiles;
    if (p) {
        const devs = p.developers || [];
        parts.push(renderMetricSection(
            'Developer Profiles',
            'Each contributor classified by their involvement: core (regular, broad contributions), peripheral (occasional), or drive-by (1\u20132 commits total).',
            'Mockus et al. 2002',
            devs.length > 0
                ? renderProfilesTable(devs)
                : emptyState('No developer profile data', 'Requires commit history with author information.'),
            'A healthy project has a mix of core maintainers and active peripheral contributors. Too many drive-by commits can signal onboarding issues.'
        ));
    }

    // Commit cadence — fields verified: insights.rs:304-332
    const ca = cachedData.cadence;
    if (ca) {
        const devs = ca.authors || [];
        parts.push(renderMetricSection(
            'Commit Cadence',
            'How regularly each developer commits. Regular cadence suggests sustained engagement; bursty patterns may indicate deadline-driven work.',
            'Eyolfson et al. 2014',
            devs.length > 0
                ? renderCadenceTable(devs)
                : emptyState('No cadence data', 'Requires 2+ commits per author to analyze intervals.')
        ));
    }

    // Collaboration network — fields verified: insights.rs:698-723
    const n = cachedData.network;
    if (n) {
        const densityHealth = n.networkDensity > 0.5 ? 'well-connected' : n.networkDensity > 0.2 ? 'moderately connected' : 'loosely connected';
        parts.push(renderMetricSection(
            'Collaboration Network',
            'How much developers work on the same files. Higher density means more shared context and easier code reviews.',
            'Begel et al. 2023',
            renderKeyValueList([
                ['Network Density', formatNumber(n.networkDensity, 3) + ` (${densityHealth})`],
                ['Team Clusters', formatInt(n.connectedComponents || 0)],
                ['Avg Collaborations', formatNumber(n.avgDegree, 2) + ' per person'],
                ['Total Connections', formatInt(n.totalEdges || 0)],
            ]),
            n.connectedComponents > 1
                ? `Your team has ${n.connectedComponents} separate clusters \u2014 consider cross-team reviews to improve knowledge sharing.`
                : 'Your team forms a single connected group \u2014 good knowledge sharing.'
        ));
    }

    // Contribution inequality — fields verified: insights.rs:446-475
    const g = cachedData.inequality;
    if (g) {
        parts.push(renderMetricSection(
            'Contribution Inequality',
            'Are commits spread evenly across the team, or concentrated in a few people? The Gini coefficient measures this (0 = perfectly equal, 1 = one person does everything).',
            'Chelkowski et al. 2016',
            renderKeyValueList([
                ['Gini Coefficient', formatNumber(g.giniCoefficient, 3)],
                ['Top 20% Share', formatPercentage(g.top20PctShare)],
                ['Health', giniInterpretation(g.giniCoefficient)],
            ]),
            'High inequality is normal in open source, but in a company team it can signal bottlenecks or disengaged members.'
        ));
    }

    // Developer focus — fields verified: insights.rs:586-620
    const f = cachedData.focus;
    if (f) {
        const devs = f.developers || [];
        parts.push(renderMetricSection(
            'Developer Focus',
            'How many different areas of the codebase each developer touches. More focused developers tend to write higher-quality code.',
            'Posnett et al. 2013, ICSE',
            devs.length > 0
                ? renderFocusTable(devs)
                : emptyState('No focus data', 'Requires commits touching files in directories.'),
            'A focus score near 1.0 means a developer works in one area. Lower scores indicate spread across many directories.'
        ));
    }

    // Developer experience — fields verified: insights.rs:1671-1679
    const exp = cachedData.experience;
    if (exp) {
        const devs = exp.developers || [];
        parts.push(renderMetricSection(
            'Developer Experience',
            'Composite experience score combining tenure, commit volume, and file familiarity. Higher scores indicate deeper project knowledge.',
            'Mockus &amp; Votta 2000; Eyolfson et al. 2014',
            devs.length > 0
                ? renderExperienceTable(devs)
                : emptyState('No experience data', 'Requires commit history with author information.'),
            `Average experience score: ${formatNumber(exp.avgExperienceScore, 1)}. Experience is computed as tenure \u00D7 ln(1+commits) \u00D7 file familiarity.`
        ));
    }

    // Developer technology expertise — fields verified: insights.rs write_tech_expertise_json
    const te = cachedData.techExpertise;
    if (te) {
        const devs = te.developers || [];
        parts.push(renderMetricSection(
            'Technology Expertise',
            'Each developer\u2019s technology profile derived from the file types they modify. Reveals skill sets and specializations.',
            'Mockus &amp; Herbsleb 2002, ICSE; Fritz et al. 2010, ICSE',
            devs.length > 0
                ? renderTechExpertiseTable(devs)
                : emptyState('No technology expertise data', 'Requires commits touching files with recognized extensions.'),
            te.dominantTech
                ? `Dominant technology across the team: ${escapeHtml(te.dominantTech)}. ${formatInt(te.developerCount)} developer${te.developerCount === 1 ? '' : 's'} analyzed.`
                : null
        ));
    }

    return parts.join('');
}

/**
 * Temporal tab: activity patterns, codebase growth, file lifecycles, file survival, release rhythm.
 *
 * Data sources:
 * - cachedData.temporal: flat object from getTemporalPatterns()
 *   (insights.rs:898-922)
 * - cachedData.growth: unwrapped from getCodebaseGrowth().growth
 *   (insights.rs:266-285)
 * - cachedData.lifecycle: unwrapped from getFileLifecycles().lifecycle
 *   (insights.rs:407-442)
 * - cachedData.survival: unwrapped from getFileSurvival().survival
 *   (insights.rs:674-694)
 * - cachedData.releaseRhythm: unwrapped from getReleaseRhythm().releaseRhythm
 *   (insights.rs:1713-1722)
 */
export function renderTemporalTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Temporal Patterns',
        'When work happens and how the codebase evolves over time — activity rhythms, growth trends, and file lifespans.'
    ));

    // Temporal patterns — fields verified: insights.rs:898-922
    const t = cachedData.temporal;
    if (t) {
        const days = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
        parts.push(renderMetricSection(
            'Activity Patterns',
            'When does your team do the most work? Shows peak hours and days, plus whether work comes in focused bursts or steady streams.',
            'Eyolfson et al. 2011, MSR',
            renderKeyValueList([
                ['Peak Hour', `${t.peakHour != null ? t.peakHour : 0}:00 UTC`],
                ['Peak Day', days[t.peakDay != null ? t.peakDay : 0] || 'N/A'],
                ['Activity Bursts', formatInt(t.burstCount || 0)],
                ['Avg Files per Burst', formatNumber(t.avgFilesInBursts, 1)],
                ['Avg Files (Non-Burst)', formatNumber(t.avgFilesOutsideBursts, 1)],
            ])
        ));
    }

    // Activity heatmap — fields verified: insights.rs write_activity_heatmap_json
    const hm = cachedData.activityHeatmap;
    if (hm && hm.totalCommits > 0) {
        parts.push(renderMetricSection(
            'Commit Heatmap',
            'A day-of-week by hour-of-day grid showing when commits happen. Identifies peak development windows and off-hours activity.',
            'Eyolfson et al. 2011, MSR; Claes et al. 2018, ICSE',
            renderActivityHeatmapTable(hm),
            hm.workHoursPct > 80
                ? 'Most commits are during business hours \u2014 a healthy work pattern.'
                : hm.weekendPct > 30
                    ? 'Over 30% of commits happen on weekends \u2014 this may indicate unsustainable work patterns.'
                    : 'Mixed work pattern with activity outside standard business hours.'
        ));
    }

    // Codebase growth — fields verified: insights.rs:266-285
    const g = cachedData.growth;
    if (g) {
        const trendLabel = {
            accelerating: 'Growing faster over time',
            stable: 'Steady growth',
            decelerating: 'Growth is slowing down',
            shrinking: 'Codebase is shrinking',
        };
        parts.push(renderMetricSection(
            'Codebase Growth',
            'Is the codebase growing, stable, or shrinking? Tracks the net change in file count over the project lifetime.',
            'Lehman 1996',
            renderKeyValueList([
                ['Current Files', formatInt(g.currentFileCount || 0)],
                ['Monthly Growth', formatNumber(g.avgMonthlyGrowth, 1) + ' files/month'],
                ['Trend', escapeHtml(trendLabel[g.trend] || g.trend || 'unknown')],
                ['Net Growth', formatInt(g.netGrowth || 0) + ' files'],
            ]),
            'Accelerating growth may signal feature expansion but also increasing maintenance burden.'
        ));
    }

    // File lifecycles — fields verified: insights.rs:407-442
    const l = cachedData.lifecycle;
    if (l) {
        const stableCount = Math.max(0,
            (l.totalFilesSeen || 0) - (l.activeCount || 0) -
            (l.ephemeralCount || 0) - (l.deadCount || 0) - (l.deletedCount || 0)
        );
        parts.push(renderMetricSection(
            'File Lifecycles',
            'Where are files in their lifecycle? Active files get regular changes, stable files are mature, ephemeral files were short-lived, and dead files haven\u2019t been touched in a long time.',
            'Godfrey &amp; Tu 2000',
            renderKeyValueList([
                ['Active (recent changes)', formatInt(l.activeCount || 0)],
                ['Stable (mature)', formatInt(stableCount)],
                ['Ephemeral (short-lived)', formatInt(l.ephemeralCount || 0)],
                ['Dead (no recent activity)', formatInt(l.deadCount || 0)],
                ['Deleted', formatInt(l.deletedCount || 0)],
                ['Churn Rate', formatNumber(l.churnRate, 2)],
            ]),
            'High ephemeral counts suggest experimental code that doesn\u2019t stick. High dead file counts may indicate cleanup opportunities.'
        ));
    }

    // File survival — fields verified: insights.rs:674-694
    const s = cachedData.survival;
    if (s) {
        parts.push(renderMetricSection(
            'File Survival',
            'Once a file is created, how long does it last before being deleted? Uses the same statistical method (Kaplan-Meier) that medical studies use to measure patient survival.',
            'Cito et al. 2021, EMSE',
            renderKeyValueList([
                ['Median Survival', s.medianSurvivalDays != null ? formatNumber(s.medianSurvivalDays, 1) + ' days' : 'No deletions observed'],
                ['Files Created', formatInt(s.totalBirths || 0)],
                ['Files Deleted', formatInt(s.totalDeaths || 0)],
                ['Early Deletion Rate', formatPercentage(s.infantMortalityRate)],
            ]),
            'A high early deletion rate means many files are created and quickly removed \u2014 this can signal poor planning or excessive experimentation.'
        ));
    }

    // Release rhythm — fields verified: insights.rs:1713-1722
    const rr = cachedData.releaseRhythm;
    if (rr) {
        const phaseLabels = {
            PostRelease: 'Post-Release (cooldown)',
            Building: 'Building (ramping up)',
            Quiet: 'Quiet (low activity)',
            Unknown: 'Unknown',
        };
        const trendLabels = {
            Accelerating: 'Speeding up',
            Stable: 'Steady pace',
            Decelerating: 'Slowing down',
        };
        parts.push(renderMetricSection(
            'Release Rhythm',
            'Analyzes commit velocity patterns over 7-day windows to detect release cycles, development phases, and whether the pace is accelerating or decelerating.',
            'Khomh et al. 2012; da Costa et al. 2016',
            renderKeyValueList([
                ['Avg Release Interval', rr.avgReleaseIntervalDays > 0 ? formatNumber(rr.avgReleaseIntervalDays, 1) + ' days' : 'No clear cycle detected'],
                ['Regularity', formatNumber(rr.releaseRegularity, 3) + (rr.releaseRegularity > 0.7 ? ' (regular)' : rr.releaseRegularity > 0.3 ? ' (moderate)' : ' (irregular)')],
                ['Current Phase', escapeHtml(phaseLabels[rr.currentPhase] || rr.currentPhase || 'Unknown')],
                ['Velocity Trend', escapeHtml(trendLabels[rr.velocityTrend] || rr.velocityTrend || 'Unknown')],
                ['Activity Peaks', formatInt(rr.peakCount || 0)],
            ]),
            rr.releaseRegularity > 0.7
                ? 'Regular release cadence \u2014 a sign of mature engineering practices.'
                : 'Irregular release pattern \u2014 consider adopting a fixed release schedule to reduce risk.'
        ));
    }

    return parts.join('');
}

/**
 * Quality tab: work type mix, modularity, congruence, churn volatility, commit complexity, defect patterns, change coupling.
 *
 * Data sources:
 * - cachedData.workType: unwrapped from getWorkTypeMix().workType
 *   (insights.rs:288-300)
 * - cachedData.modularity: unwrapped from getModularity().modularity
 *   (insights.rs:624-644)
 * - cachedData.congruence: unwrapped from getCongruence().congruence
 *   (insights.rs:648-670)
 * - cachedData.coupling: flat array from getChangeCoupling()
 *   (insights.rs:824-838)
 */
export function renderQualityTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Code Quality',
        'Structural health of the codebase — how work is split between features and maintenance, how modular the code is, and hidden dependencies.'
    ));

    // Work type mix — fields verified: insights.rs:288-300
    const w = cachedData.workType;
    if (w) {
        parts.push(renderMetricSection(
            'Work Type Mix',
            'What kind of work is happening? A healthy project balances new features with maintenance. Too much feature work without cleanup leads to technical debt.',
            'Hindle et al. 2008',
            renderKeyValueList([
                ['New Features', formatFixed(w.featurePct, 1) + '%'],
                ['Maintenance', formatFixed(w.maintenancePct, 1) + '%'],
                ['Cleanup / Deletions', formatFixed(w.cleanupPct, 1) + '%'],
                ['Mixed Changes', formatFixed(w.mixedPct, 1) + '%'],
                ['Primary Focus', escapeHtml(capitalize(w.dominantType || 'unknown'))],
            ]),
            w.maintenancePct < 20
                ? 'Maintenance is under 20% \u2014 the team may be accumulating technical debt.'
                : 'Healthy maintenance ratio \u2014 the team is investing in code quality.'
        ));
    }

    // Modularity — fields verified: insights.rs:624-644
    const m = cachedData.modularity;
    if (m) {
        const modHealth = m.modularityIndex > 0.7 ? 'well-modular' : m.modularityIndex > 0.4 ? 'moderately modular' : 'tightly coupled';
        parts.push(renderMetricSection(
            'Modularity',
            'When you change a file, do you also need to change files in other directories? High modularity means changes stay contained within their module.',
            'MacCormack et al. 2006',
            renderKeyValueList([
                ['Modularity Index', formatNumber(m.modularityIndex, 3) + ` (${modHealth})`],
                ['Cross-Module Changes', formatPercentage(m.crossModuleRatio)],
                ['Modules Analyzed', formatInt(m.directories ? m.directories.length : 0)],
            ]),
            'Low modularity means changes ripple across the codebase \u2014 making refactoring and testing harder.'
        ));
    }

    // Congruence — fields verified: insights.rs:648-670
    const c = cachedData.congruence;
    if (c) {
        const gaps = c.coordinationGaps ? c.coordinationGaps.length : 0;
        parts.push(renderMetricSection(
            'Sociotechnical Congruence',
            'Do developers who work on interconnected code actually communicate? Gaps between technical dependencies and team coordination cause integration bugs.',
            'Cataldo et al. 2009, ICSE',
            renderKeyValueList([
                ['Congruence Score', formatNumber(c.congruenceScore, 3)],
                ['Coordination Gaps', formatInt(gaps)],
                ['Required Handoffs', formatInt(c.requiredCoordinations || 0)],
                ['Actual Handoffs', formatInt(c.actualCoordinations || 0)],
            ]),
            gaps > 0
                ? `There are ${gaps} coordination gap${gaps === 1 ? '' : 's'} \u2014 developers working on related code who haven\u2019t collaborated.`
                : 'Great alignment \u2014 developers working on related code are already coordinating.'
        ));
    }

    // Churn volatility — fields verified: insights.rs write_churn_volatility_json
    const cv = cachedData.churnVolatility;
    if (cv) {
        const files = cv.files || [];
        const cvHealth = cv.volatileCount > (cv.stableCount || 1) ? 'many volatile files' : 'mostly stable churn';
        parts.push(renderMetricSection(
            'Churn Volatility',
            'Files with erratic change patterns (alternating high and low activity) are stronger defect predictors than total churn alone.',
            'Nagappan &amp; Ball 2005, ICSE',
            files.length > 0
                ? renderChurnVolatilityTable(files)
                : emptyState('No churn volatility data', 'Requires files with changes across multiple time windows.'),
            `Average CV: ${formatNumber(cv.avgCv, 2)} (${cvHealth}). ${cv.volatileCount || 0} volatile files, ${cv.stableCount || 0} stable files.`
        ));
    }

    // Commit complexity — fields verified: insights.rs write_commit_complexity_json
    const cc = cachedData.commitComplexity;
    if (cc) {
        const commits = cc.commits || [];
        parts.push(renderMetricSection(
            'Commit Complexity',
            'Tangled commits that touch many files across many directories with mixed action types are harder to review and more error-prone.',
            'Herzig &amp; Zeller 2013, MSR',
            commits.length > 0
                ? renderCommitComplexityTable(commits)
                : emptyState('No commit complexity data', 'Requires commits with file change information.'),
            `${cc.tangledCount || 0} tangled commit${(cc.tangledCount || 0) === 1 ? '' : 's'} (above 95th percentile). Average complexity: ${formatNumber(cc.avgComplexity, 1)}, median: ${formatNumber(cc.medianComplexity, 1)}.`
        ));
    }

    // Defect-introducing change patterns — fields verified: insights.rs write_defect_patterns_json
    const dp = cachedData.defectPatterns;
    if (dp) {
        const files = dp.files || [];
        parts.push(renderMetricSection(
            'Defect-Introducing Patterns',
            'Files that receive burst edits shortly after large commits are likely undergoing fix-up for defects introduced by that commit.',
            'Kim et al. 2008, TSE; Sliwerski et al. 2005',
            files.length > 0
                ? renderDefectPatternsTable(files)
                : emptyState('No defect patterns detected', 'Requires large commits followed by burst edits within 3 days.'),
            `${dp.highRiskCount || 0} high-risk file${(dp.highRiskCount || 0) === 1 ? '' : 's'} (score > 0.5). ${dp.largeCommitCount || 0} large commits detected, ${dp.burstAfterLargeCount || 0} burst-after-large events.`
        ));
    }

    // Change coupling — fields verified: insights.rs:824-838
    const coupling = cachedData.coupling;
    parts.push(renderMetricSection(
        'Change Coupling',
        'Files that always change together, even though they don\u2019t import each other. These hidden dependencies make the codebase harder to maintain.',
        'D\'Ambros et al. 2009, EMSE',
        coupling && coupling.length > 0
            ? renderCouplingTable(coupling)
            : emptyState('No coupling pairs detected', 'Requires files that frequently change together in the same commit.'),
        coupling && coupling.length > 0
            ? 'Consider extracting shared logic into a common module, or documenting why these files must change together.'
            : null
    ));

    return parts.join('');
}

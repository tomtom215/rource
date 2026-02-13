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
    renderMetricSection, renderTabIntro, renderKeyValueList,
    renderMetricNav, truncatePath
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

// ============================================================================
// Academic Citation Registry
//
// Every citation links to its peer-reviewed published paper via DOI.
// All DOIs verified against publisher records (ACM, IEEE, Springer, PLOS).
// ============================================================================

const CITE = {
    nagappan2005: { text: 'Nagappan, Ball & Zeller 2006, ICSE', url: 'https://doi.org/10.1145/1134285.1134349' },
    hassan2009: { text: 'Hassan 2009, ICSE', url: 'https://doi.org/10.1109/ICSE.2009.5070510' },
    nagappan2010: { text: 'Nagappan et al. 2010, ISSRE', url: 'https://doi.org/10.1109/ISSRE.2010.25' },
    bird2011: { text: 'Bird et al. 2011, FSE', url: 'https://doi.org/10.1145/2025113.2025119' },
    rigby2013: { text: 'Rigby & Bird 2013, FSE', url: 'https://doi.org/10.1145/2491411.2491444' },
    avelino2016: { text: 'Avelino et al. 2016, ICPC', url: 'https://doi.org/10.1109/ICPC.2016.7503718' },
    eyolfson2011: { text: 'Eyolfson, Tan & Lam 2011, MSR', url: 'https://doi.org/10.1145/1985441.1985464' },
    mockus2002: { text: 'Mockus, Fielding & Herbsleb 2002, TOSEM', url: 'https://doi.org/10.1145/567793.567795' },
    eyolfson2014: { text: 'Eyolfson, Tan & Lam 2014, EMSE', url: 'https://doi.org/10.1007/s10664-013-9245-0' },
    chelkowski2016: { text: 'Chelkowski, Gloor & Jemielniak 2016, PLOS ONE', url: 'https://doi.org/10.1371/journal.pone.0152976' },
    posnett2013: { text: 'Posnett et al. 2013, ICSE', url: 'https://doi.org/10.1109/ICSE.2013.6606591' },
    lehman1996: { text: 'Lehman 1996, EWSPT', url: 'https://doi.org/10.1007/BFb0017737' },
    godfrey2000: { text: 'Godfrey & Tu 2000, ICSM', url: 'https://doi.org/10.1109/ICSM.2000.883030' },
    cataldo2008: { text: 'Cataldo, Herbsleb & Carley 2008, ESEM', url: 'https://doi.org/10.1145/1414004.1414008' },
    maccormack2006: { text: 'MacCormack, Rusnak & Baldwin 2006, Mgmt. Sci.', url: 'https://doi.org/10.1287/mnsc.1060.0552' },
    dambros2009: { text: "D'Ambros, Lanza & Robbes 2009, WCRE", url: 'https://doi.org/10.1109/WCRE.2009.19' },
    hindle2008: { text: 'Hindle, German & Holt 2008, MSR', url: 'https://doi.org/10.1145/1370750.1370773' },
    herzig2013: { text: 'Herzig & Zeller 2013, MSR', url: 'https://doi.org/10.1109/MSR.2013.6624018' },
    kim2007: { text: 'Kim et al. 2007, ICSE', url: 'https://doi.org/10.1109/ICSE.2007.66' },
    sliwerski2005: { text: 'Sliwerski, Zimmermann & Zeller 2005, MSR', url: 'https://doi.org/10.1145/1083142.1083147' },
    khomh2012: { text: 'Khomh et al. 2012, MSR', url: 'https://doi.org/10.1109/MSR.2012.6224279' },
    dacosta2016: { text: 'da Costa et al. 2016, MSR', url: 'https://doi.org/10.1145/2901739.2901764' },
    greiler2015: { text: 'Greiler, Herzig & Czerwonka 2015, MSR', url: 'https://doi.org/10.1109/MSR.2015.8' },
    mockus2000: { text: 'Mockus & Votta 2000, ICSM', url: 'https://doi.org/10.1109/ICSM.2000.883028' },
    constantinou2017: { text: 'Constantinou & Mens 2017, SANER', url: 'https://doi.org/10.1109/SANER.2017.7884607' },
    fritz2010: { text: 'Fritz et al. 2010, ICSE', url: 'https://doi.org/10.1145/1806799.1806856' },
    kalliamvakou2014: { text: 'Kalliamvakou et al. 2014, MSR', url: 'https://doi.org/10.1145/2597073.2597074' },
    mockus2002_expertise: { text: 'Mockus & Herbsleb 2002, ICSE', url: 'https://doi.org/10.1145/581339.581401' },
    mockus2009: { text: 'Mockus 2009, ICSE', url: '' },
    rigby2016: { text: 'Rigby et al. 2016', url: '' },
    claes2018: { text: 'Claes et al. 2018, ICSE', url: '' },
    begel2023: { text: 'Begel et al. 2023', url: '' },
    spinellis2021: { text: 'Spinellis, Louridas & Kechagia 2021, PeerJ CS', url: 'https://doi.org/10.7717/peerj-cs.372' },
    // Intelligence tab citations (M1-M7)
    bavota2013: { text: 'Bavota et al. 2013, ICSM', url: 'https://doi.org/10.1109/ICSM.2013.24' },
    gall1998: { text: 'Gall, Hajek & Jazayeri 1998, ICSE', url: 'https://doi.org/10.1109/ICSE.1998.671583' },
    denning1968: { text: 'Denning 1968, CACM', url: 'https://doi.org/10.1145/363095.363141' },
    herzig2013_icse: { text: 'Herzig & Zeller 2013, ICSE', url: 'https://doi.org/10.1109/ICSE.2013.6606588' },
    kirinuki2014: { text: 'Kirinuki et al. 2014, SANER', url: '' },
    hassan2004: { text: 'Hassan & Holt 2004, ICSM', url: 'https://doi.org/10.1109/ICSM.2004.1357802' },
    zimmermann2005: { text: 'Zimmermann et al. 2005, ESEC/FSE', url: 'https://doi.org/10.1145/1081706.1081728' },
    dyer2013: { text: 'Dyer et al. 2013, MSR', url: 'https://doi.org/10.1109/MSR.2013.6624016' },
    hindle2012: { text: 'Hindle et al. 2012, ICSE', url: 'https://doi.org/10.1109/ICSE.2012.6227135' },
    fritz2010_dok: { text: 'Fritz et al. 2010, ICSE', url: 'https://doi.org/10.1145/1806799.1806856' },
    robillard2014: { text: 'Robillard et al. 2014, IEEE Software', url: '' },
    garcia2009: { text: 'Garcia et al. 2009, WICSA', url: 'https://doi.org/10.1109/WICSA.2009.5290649' },
    maqbool2007: { text: 'Maqbool & Babri 2007, JSS', url: 'https://doi.org/10.1016/j.jss.2006.10.029' },
    raghavan2007: { text: 'Raghavan, Albert & Kumara 2007, Phys Rev E', url: 'https://doi.org/10.1103/PhysRevE.76.036106' },
    ricca2011: { text: 'Ricca et al. 2011, JSS', url: 'https://doi.org/10.1016/j.jss.2011.03.033' },
    // Intelligence tab M8-M32 citations
    thongtanunam2015: { text: 'Thongtanunam et al. 2015, SANER', url: 'https://doi.org/10.1109/SANER.2015.7081824' },
    balachandran2013: { text: 'Balachandran 2013, ICSE', url: 'https://doi.org/10.1109/ICSE.2013.6606642' },
    rigby2011: { text: 'Rigby & Storey 2011, ICSE', url: 'https://doi.org/10.1145/1985793.1985867' },
    baysal2016: { text: 'Baysal et al. 2016, ESE', url: 'https://doi.org/10.1007/s10664-015-9404-2' },
    zhou2012: { text: 'Zhou & Mockus 2012, ICSE', url: 'https://doi.org/10.1109/ICSE.2012.6227164' },
    steinmacher2015: { text: 'Steinmacher et al. 2015, ISSE', url: 'https://doi.org/10.1007/s11219-014-9236-x' },
    martin2003: { text: 'Martin 2003, Agile Software Development', url: '' },
    wehaibi2016: { text: 'Wehaibi et al. 2016, SANER', url: 'https://doi.org/10.1109/SANER.2016.95' },
    maldonado2015: { text: 'Maldonado & Shihab 2015, MSR', url: 'https://doi.org/10.1109/MSR.2015.14' },
    hassan2008: { text: 'Hassan 2008, FoSE', url: 'https://doi.org/10.1145/1370175.1370177' },
    dambros2010: { text: "D'Ambros & Lanza 2010, SCP", url: 'https://doi.org/10.1016/j.scico.2009.04.007' },
    imai2022: { text: 'Imai 2022, ESEM', url: 'https://doi.org/10.1145/3544902.3546244' },
    dakhel2023: { text: 'Dakhel et al. 2023, JSS', url: 'https://doi.org/10.1016/j.jss.2023.111734' },
    vasilescu2015: { text: 'Vasilescu et al. 2015, FSE', url: 'https://doi.org/10.1145/2786805.2786850' },
    yamashita2013: { text: 'Yamashita & Moonen 2013, WCRE', url: 'https://doi.org/10.1109/WCRE.2013.6671299' },
    mockus2002_expertise2: { text: 'Mockus & Herbsleb 2002, ICSE', url: 'https://doi.org/10.1145/581339.581401' },
    fritz2010_expertise: { text: 'Fritz et al. 2010, FSE', url: 'https://doi.org/10.1145/1882291.1882300' },
    fakhoury2019: { text: 'Fakhoury et al. 2019, ICPC', url: 'https://doi.org/10.1109/ICPC.2019.00014' },
    kapur2023: { text: 'Kapur & Musgrove 2023, ESEC/FSE', url: 'https://doi.org/10.1145/3611643.3616295' },
    // Strategic tab citations
    forsgren2018: { text: 'Forsgren, Humble & Kim 2018, Accelerate', url: '' },
    ebbinghaus1885: { text: 'Ebbinghaus 1885, Memory', url: '' },
    jabrayilzade2022: { text: 'Jabrayilzade et al. 2022, JSS', url: '' },
    fisher1993: { text: 'Fisher 1993, Statistical Analysis of Circular Data', url: '' },
    cataldo2008_coord: { text: 'Cataldo & Herbsleb 2008, ESEM', url: 'https://doi.org/10.1145/1414004.1414008' },
    xu2025: { text: 'Xu et al. 2025, JCST', url: '' },
    borg2024: { text: 'Borg et al. 2024, IEEE Software', url: '' },
};

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

    parts.push(renderMetricNav([
        'Technology Distribution', 'File Hotspots', 'Change Entropy', 'Change Bursts'
    ]));

    // Technology distribution — fields verified: insights.rs write_tech_distribution_json
    const td = cachedData.techDistribution;
    if (td) {
        const langs = td.languages || [];
        parts.push(renderMetricSection(
            'Technology Distribution',
            'The languages and technologies in the repository, classified by file extension from the active file set.',
            [CITE.mockus2002, CITE.kalliamvakou2014],
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
        [CITE.nagappan2005],
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
            [CITE.hassan2009],
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
            [CITE.nagappan2010],
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
        'Spots where your team is vulnerable \u2014 single points of failure, knowledge concentration, and risky commit patterns.'
    ));

    parts.push(renderMetricNav([
        'Bus Factor', 'Knowledge Silos', 'Ownership Fragmentation',
        'Knowledge Distribution', 'Truck Factor (DOA Model)', 'Turnover Impact', 'Circadian Risk'
    ]));

    // Bus factors — fields verified: insights.rs:858-876
    const bus = cachedData.busFactors;
    const criticalCount = bus ? bus.filter(b => b.busFactor <= 1).length : 0;
    parts.push(renderMetricSection(
        'Bus Factor',
        'If a key contributor leaves, can someone else maintain this code? A bus factor of 1 means a single person controls it.',
        [CITE.bird2011],
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
            [CITE.rigby2013],
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
            [CITE.bird2011, CITE.greiler2015],
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
            [CITE.constantinou2017, CITE.fritz2010],
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
            [CITE.avelino2016],
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
            [CITE.mockus2009, CITE.rigby2016],
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
            [CITE.eyolfson2011],
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
        'How your team works together \u2014 who contributes what, how often, and how well they collaborate.'
    ));

    parts.push(renderMetricNav([
        'Developer Profiles', 'Commit Cadence', 'Collaboration Network',
        'Contribution Inequality', 'Developer Focus', 'Developer Experience', 'Technology Expertise'
    ]));

    // Developer profiles — fields verified: insights.rs:376-403
    const p = cachedData.profiles;
    if (p) {
        const devs = p.developers || [];
        parts.push(renderMetricSection(
            'Developer Profiles',
            'Each contributor classified by their involvement: core (regular, broad contributions), peripheral (occasional), or drive-by (1\u20132 commits total).',
            [CITE.mockus2002],
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
            [CITE.eyolfson2014],
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
            [CITE.begel2023],
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
            [CITE.chelkowski2016],
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
            [CITE.posnett2013],
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
            [CITE.mockus2000, CITE.eyolfson2014],
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
            [CITE.mockus2002_expertise, CITE.fritz2010],
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
        'When work happens and how the codebase evolves over time \u2014 activity rhythms, growth trends, and file lifespans.'
    ));

    parts.push(renderMetricNav([
        'Activity Patterns', 'Commit Heatmap', 'Codebase Growth',
        'File Lifecycles', 'File Survival', 'Release Rhythm'
    ]));

    // Temporal patterns — fields verified: insights.rs:898-922
    const t = cachedData.temporal;
    if (t) {
        const days = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
        parts.push(renderMetricSection(
            'Activity Patterns',
            'When does your team do the most work? Shows peak hours and days, plus whether work comes in focused bursts or steady streams.',
            [CITE.eyolfson2011],
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
            [CITE.eyolfson2011, CITE.claes2018],
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
            [CITE.lehman1996],
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
            [CITE.godfrey2000],
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
            [CITE.spinellis2021],
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
            [CITE.khomh2012, CITE.dacosta2016],
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
        'Structural health of the codebase \u2014 how work is split between features and maintenance, how modular the code is, and hidden dependencies.'
    ));

    parts.push(renderMetricNav([
        'Work Type Mix', 'Modularity', 'Sociotechnical Congruence',
        'Churn Volatility', 'Commit Complexity', 'Defect-Introducing Patterns', 'Change Coupling'
    ]));

    // Work type mix — fields verified: insights.rs:288-300
    const w = cachedData.workType;
    if (w) {
        parts.push(renderMetricSection(
            'Work Type Mix',
            'What kind of work is happening? A healthy project balances new features with maintenance. Too much feature work without cleanup leads to technical debt.',
            [CITE.hindle2008],
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
            [CITE.maccormack2006],
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
            [CITE.cataldo2008],
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
            [CITE.nagappan2005],
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
            [CITE.herzig2013],
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
            [CITE.kim2007, CITE.sliwerski2005],
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
        [CITE.dambros2009],
        coupling && coupling.length > 0
            ? renderCouplingTable(coupling)
            : emptyState('No coupling pairs detected', 'Requires files that frequently change together in the same commit.'),
        coupling && coupling.length > 0
            ? 'Consider extracting shared logic into a common module, or documenting why these files must change together.'
            : null
    ));

    return parts.join('');
}

/**
 * Intelligence tab: 7 novel research metrics (M1-M7).
 *
 * These metrics are original combinations of published techniques, producing
 * continuous multi-dimensional scores where prior work used binary indicators.
 *
 * Data sources (all verified against insights.rs):
 * - cachedData.contextualComplexity: unwrapped from getContextualComplexity().contextualComplexity
 * - cachedData.commitCohesion: unwrapped from getCommitCohesion().commitCohesion
 * - cachedData.changePropagation: unwrapped from getChangePropagation().changePropagation
 * - cachedData.commitMessageEntropy: unwrapped from getCommitMessageEntropy().commitMessageEntropy
 * - cachedData.knowledgeHalfLife: unwrapped from getKnowledgeHalfLife().knowledgeHalfLife
 * - cachedData.architecturalDrift: unwrapped from getArchitecturalDrift().architecturalDrift
 * - cachedData.successionReadiness: unwrapped from getSuccessionReadiness().successionReadiness
 */
export function renderIntelligenceTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Research Intelligence',
        'Novel metrics combining peer-reviewed techniques in new ways. Each metric produces continuous, multi-dimensional scores where prior work used binary indicators.'
    ));

    parts.push(renderMetricNav([
        'Contextual Complexity', 'Commit Cohesion', 'Change Propagation',
        'Commit Message Quality', 'Knowledge Half-Life',
        'Architectural Drift', 'Succession Readiness',
        'Reviewer Recommendation', 'Review Response',
        'Onboarding Velocity', 'Interface Stability',
        'Tech Debt Velocity', 'Focus Drift',
        'AI Change Detection', 'Knowledge Gini',
        'Expertise Profile', 'Cognitive Load'
    ]));

    // M1: Contextual Complexity
    const ctx = cachedData.contextualComplexity;
    if (ctx) {
        const files = ctx.files || [];
        const topFiles = files.slice(0, 15);
        parts.push(renderMetricSection(
            'Contextual Complexity',
            'For each file, the number of other files a developer must simultaneously understand to safely modify it \u2014 the file\u2019s cognitive working set.',
            [CITE.bavota2013, CITE.gall1998, CITE.denning1968],
            topFiles.length > 0
                ? renderContextualComplexityTable(topFiles)
                : emptyState('No contextual complexity data', 'Requires coupling pairs from co-change analysis.'),
            `Average context size: ${formatFixed(ctx.avgContextSize, 1)} files. Threshold (P75): ${formatFixed(ctx.threshold, 3)}. ${ctx.filesWithContext || 0} files have non-trivial context sets. Maximum: ${ctx.maxContextSize || 0} files.`
        ));
    }

    // M2: Commit Cohesion
    const coh = cachedData.commitCohesion;
    if (coh) {
        const devs = coh.developerCohesion || [];
        const topDevs = devs.slice(0, 15);
        const cohHealth = (coh.medianCohesion || 0) > 0.7 ? 'well-focused commits' : (coh.medianCohesion || 0) > 0.4 ? 'moderately focused' : 'many tangled commits';
        parts.push(renderMetricSection(
            'Commit Cohesion',
            'Measures whether commits are atomic (tightly related changes) or tangled (mixing unrelated modifications). Tangled commits make review harder and introduce more bugs.',
            [CITE.herzig2013_icse],
            topDevs.length > 0
                ? renderCommitCohesionTable(topDevs)
                : emptyState('No commit cohesion data', 'Requires commits with multiple file changes.'),
            `Median cohesion: ${formatFixed(coh.medianCohesion, 3)} (${cohHealth}). Tangled ratio: ${formatPercentage(coh.tangledRatio)}. ${coh.totalAnalyzed || 0} commits analyzed.`
        ));
    }

    // M3: Change Propagation
    const prop = cachedData.changePropagation;
    if (prop) {
        const files = prop.files || [];
        const topFiles = files.slice(0, 15);
        parts.push(renderMetricSection(
            'Change Propagation',
            'Predicts which files will need concurrent modification when you change a file, with transitive cascade depth up to 3 levels.',
            [CITE.hassan2004, CITE.zimmermann2005],
            topFiles.length > 0
                ? renderChangePropagationTable(topFiles)
                : emptyState('No propagation data', 'Requires coupling pairs from co-change analysis.'),
            `Average risk score: ${formatFixed(prop.avgRiskScore, 3)}. Average cascade depth: ${formatFixed(prop.avgExpectedDepth, 2)}. ${prop.cascadeCount || 0} files have depth-3 cascades.`
        ));
    }

    // M4: Commit Message Quality
    const cme = cachedData.commitMessageEntropy;
    if (cme) {
        const devs = cme.developerQuality || [];
        const topDevs = devs.slice(0, 15);
        parts.push(renderMetricSection(
            'Commit Message Quality',
            'Measures the information density and quality of commit messages using Shannon entropy and cross-entropy against a corpus model.',
            [CITE.dyer2013, CITE.hindle2012],
            topDevs.length > 0
                ? renderMessageQualityTable(topDevs)
                : emptyState('No message quality data', 'Requires commits with non-empty messages.'),
            `Median info density: ${formatFixed(cme.medianInfoDensity, 3)}. Low-info ratio: ${formatPercentage(cme.lowInfoRatio)}. ${cme.noMessageCount || 0} commits had no message. ${cme.totalAnalyzed || 0} analyzed.`
        ));
    }

    // M5: Knowledge Half-Life
    const khl = cachedData.knowledgeHalfLife;
    if (khl) {
        const files = khl.files || [];
        const topFiles = files.slice(0, 15);
        const freshness = khl.teamKnowledgeFreshness || 0;
        const freshnessLabel = freshness > 0.7 ? 'knowledge is fresh' : freshness > 0.4 ? 'some knowledge decay' : 'significant knowledge loss';
        parts.push(renderMetricSection(
            'Knowledge Half-Life',
            'Models exponential knowledge decay per-file. As time passes since a developer\u2019s last edit, their understanding fades \u2014 like Ebbinghaus\u2019 forgetting curve.',
            [CITE.fritz2010_dok, CITE.rigby2013],
            topFiles.length > 0
                ? renderKnowledgeHalfLifeTable(topFiles)
                : emptyState('No knowledge half-life data', 'Requires file-level commit history with timestamps.'),
            `Team freshness: ${formatFixed(freshness, 3)} (${freshnessLabel}). ${khl.cliffCount || 0} knowledge cliffs. Median half-life: ${formatFixed(khl.medianHalfLifeDays, 0)} days (range: ${formatFixed(khl.minHalfLifeDays, 0)}\u2013${formatFixed(khl.maxHalfLifeDays, 0)}).`
        ));
    }

    // M6: Architectural Drift
    const ad = cachedData.architecturalDrift;
    if (ad) {
        const dirs = ad.directories || [];
        const topDirs = dirs.slice(0, 15);
        const driftLevel = (ad.driftIndex || 0) > 0.5 ? 'significant drift' : (ad.driftIndex || 0) > 0.2 ? 'moderate drift' : 'well-aligned';
        parts.push(renderMetricSection(
            'Architectural Drift',
            'Measures divergence between your directory structure and how files actually co-change. Drift means the architecture on disk no longer reflects the architecture in practice.',
            [CITE.garcia2009, CITE.maqbool2007, CITE.raghavan2007],
            topDirs.length > 0
                ? renderArchitecturalDriftTable(topDirs)
                : emptyState('No architectural drift data', 'Requires coupling pairs and directory structure.'),
            `Drift index: ${formatFixed(ad.driftIndex, 3)} (${driftLevel}). NMI: ${formatFixed(ad.nmi, 3)}. ${ad.clusterCount || 0} co-change clusters found. ${ad.misplacedCount || 0} misplaced files. ${(ad.ghostModules || []).length} ghost modules.`
        ));
    }

    // M7: Succession Readiness
    const sr = cachedData.successionReadiness;
    if (sr) {
        const files = sr.files || [];
        const topFiles = files.slice(0, 15);
        const readiness = sr.codebaseReadiness || 0;
        const readinessLabel = readiness > 0.5 ? 'well-prepared' : readiness > 0.2 ? 'partially prepared' : 'at risk';
        parts.push(renderMetricSection(
            'Succession Readiness',
            'For each file, scores how prepared the team is for the primary contributor to become unavailable. Combines knowledge freshness, commit depth, and directory similarity.',
            [CITE.ricca2011, CITE.rigby2013],
            topFiles.length > 0
                ? renderSuccessionReadinessTable(topFiles)
                : emptyState('No succession data', 'Requires knowledge half-life data and multiple contributors.'),
            `Codebase readiness: ${formatFixed(readiness, 3)} (${readinessLabel}). ${sr.singlePointOfFailureCount || 0} single points of failure. ${sr.adequateSuccessionCount || 0} files with adequate succession (> 0.5). ${sr.totalFiles || 0} total files.`
        ));
    }

    // M9: Reviewer Recommendation
    const rr = cachedData.reviewerRecommendation;
    if (rr) {
        const files = rr.files || [];
        const topFiles = files.slice(0, 15);
        parts.push(renderMetricSection(
            'Reviewer Recommendation',
            'Recommends the best code reviewers for each file using a composite score of ownership, recency, and review frequency.',
            [CITE.thongtanunam2015, CITE.balachandran2013],
            topFiles.length > 0
                ? renderReviewerRecommendationTable(topFiles)
                : emptyState('No reviewer data', 'Requires files with multiple contributors.'),
            `${rr.singleReviewerCount || 0} files depend on a single reviewer. Average ${formatFixed(rr.avgReviewersPerFile, 1)} reviewers per file.`
        ));
    }

    // M19: Review Response
    const rrsp = cachedData.reviewResponse;
    if (rrsp) {
        const files = rrsp.files || [];
        const topFiles = files.slice(0, 15);
        parts.push(renderMetricSection(
            'Review Response',
            'Measures review turnaround time by tracking how quickly a file gets touched by a different author after a change \u2014 a proxy for code review responsiveness.',
            [CITE.rigby2011, CITE.baysal2016],
            topFiles.length > 0
                ? renderReviewResponseTable(topFiles)
                : emptyState('No review response data', 'Requires files touched by multiple authors.'),
            `Team P50: ${formatFixed(rrsp.teamP50Hours, 1)}h. P90: ${formatFixed(rrsp.teamP90Hours, 1)}h.`
        ));
    }

    // M20: Onboarding Velocity
    const ob = cachedData.onboardingVelocity;
    if (ob) {
        const devs = ob.developers || [];
        const topDevs = devs.slice(0, 15);
        parts.push(renderMetricSection(
            'Onboarding Velocity',
            'Measures how quickly new contributors ramp up by comparing commit activity in their first 4 weeks vs weeks 5\u20138. Classifies contributors as one-shot, slow-ramp, fast-ramp, or sustained.',
            [CITE.zhou2012, CITE.steinmacher2015],
            topDevs.length > 0
                ? renderOnboardingTable(topDevs)
                : emptyState('No onboarding data', 'Requires contributors with commit history.'),
            `${ob.oneShotCount || 0} one-shot, ${ob.fastRampCount || 0} fast-ramp, ${ob.slowRampCount || 0} slow-ramp, ${ob.sustainedCount || 0} sustained. Median days to core: ${formatFixed(ob.medianDaysToCore, 0)}.`
        ));
    }

    // M23: Interface Stability
    const is = cachedData.interfaceStability;
    if (is) {
        const dirs = is.directories || [];
        const topDirs = dirs.slice(0, 15);
        const stabilityLabel = (is.avgStability || 0) > 0.8 ? 'stable boundaries' : (is.avgStability || 0) > 0.5 ? 'moderate stability' : 'volatile boundaries';
        parts.push(renderMetricSection(
            'Interface Stability',
            'Measures how stable module boundaries are. Stable interfaces allow independent development; unstable ones force coordination overhead.',
            [CITE.martin2003, CITE.maccormack2006],
            topDirs.length > 0
                ? renderInterfaceStabilityTable(topDirs)
                : emptyState('No interface stability data', 'Requires files in multiple directories with shared contributors.'),
            `Average stability: ${formatFixed(is.avgStability, 3)} (${stabilityLabel}). ${is.volatileCount || 0} volatile, ${is.stableCount || 0} stable out of ${is.totalAnalyzed || 0} directories.`
        ));
    }

    // M25: Tech Debt Velocity
    const tdv = cachedData.techDebtVelocity;
    if (tdv) {
        const windows = tdv.windows || [];
        const trendLabel = tdv.trend || 'Stable';
        parts.push(renderMetricSection(
            'Tech Debt Velocity',
            'Tracks whether maintenance burden is accumulating or being paid down over time by classifying commits as maintenance, feature, or debt-reduction work.',
            [CITE.wehaibi2016, CITE.maldonado2015],
            windows.length > 0
                ? renderTechDebtTable(windows)
                : emptyState('No tech debt data', 'Requires commits with descriptive messages over 60+ days.'),
            `Trend: ${trendLabel} (slope: ${formatFixed(tdv.velocitySlope, 4)}). Overall maintenance ratio: ${formatPercentage(tdv.overallMaintenanceRatio)}. Feature: ${formatPercentage(tdv.overallFeatureRatio)}. Debt reduction: ${formatPercentage(tdv.overallDebtReductionRatio)}.`
        ));
    }

    // M30: Focus Drift
    const fd = cachedData.focusDrift;
    if (fd) {
        const dirs = fd.directories || [];
        const topDirs = dirs.slice(0, 15);
        parts.push(renderMetricSection(
            'Focus Drift',
            'Tracks which areas of the codebase are getting more or less development attention over time, revealing shifting priorities and potential neglect.',
            [CITE.hassan2008, CITE.dambros2010],
            topDirs.length > 0
                ? renderFocusDriftTable(topDirs)
                : emptyState('No focus drift data', 'Requires commits spanning a meaningful time range.'),
            `${fd.risingCount || 0} rising, ${fd.decliningCount || 0} declining, ${fd.abandonedCount || 0} abandoned out of ${fd.totalAnalyzed || 0} directories.`
        ));
    }

    // M31: AI Change Detection
    const ai = cachedData.aiChangeDetection;
    if (ai) {
        const flagged = ai.flaggedCommits || [];
        const topFlagged = flagged.slice(0, 15);
        parts.push(renderMetricSection(
            'AI Change Detection',
            'Detects commits that deviate significantly from an author\u2019s established baseline \u2014 unusual breadth of file changes or directory spread may indicate AI-assisted generation.',
            [CITE.imai2022, CITE.dakhel2023, CITE.vasilescu2015],
            topFlagged.length > 0
                ? renderAiDetectionTable(topFlagged)
                : emptyState('No anomalous commits detected', 'All commits are within normal patterns for their authors.'),
            `${ai.totalFlagged || 0} flagged out of ${ai.totalAnalyzed || 0} commits (${formatPercentage(ai.flaggedRatio)}).`
        ));
    }

    // M10: Knowledge Gini
    const kg = cachedData.knowledgeGini;
    if (kg) {
        const devs = kg.developers || [];
        const topDevs = devs.slice(0, 15);
        const giniLabel = (kg.giniCoefficient || 0) > 0.6 ? 'high inequality' : (kg.giniCoefficient || 0) > 0.3 ? 'moderate inequality' : 'well-distributed';
        parts.push(renderMetricSection(
            'Knowledge Gini',
            'Measures inequality of code knowledge across team members using the Gini coefficient. High values indicate knowledge hoarding; low values mean well-distributed expertise.',
            [CITE.yamashita2013, CITE.greiler2015],
            topDevs.length > 0
                ? renderKnowledgeGiniTable(topDevs)
                : emptyState('No knowledge distribution data', 'Requires files with multiple contributors.'),
            `Gini coefficient: ${formatFixed(kg.giniCoefficient, 3)} (${giniLabel}). Top 10% hold ${formatPercentage(kg.top10PctShare)}. Top 20% hold ${formatPercentage(kg.top20PctShare)}. ${kg.totalDevelopers || 0} developers.`
        ));
    }

    // M11: Expertise Profile
    const ep = cachedData.expertiseProfile;
    if (ep) {
        const devs = ep.developers || [];
        const topDevs = devs.slice(0, 15);
        parts.push(renderMetricSection(
            'Expertise Profile',
            'Classifies developers as specialists (deep in few files) or generalists (shallow across many). Teams need both \u2014 the quadrant distribution reveals team shape.',
            [CITE.mockus2002_expertise2, CITE.fritz2010_expertise],
            topDevs.length > 0
                ? renderExpertiseProfileTable(topDevs)
                : emptyState('No expertise data', 'Requires files with authorship data.'),
            `${ep.specialistDeepCount || 0} specialist-deep, ${ep.specialistShallowCount || 0} specialist-shallow, ${ep.generalistDeepCount || 0} generalist-deep, ${ep.generalistShallowCount || 0} generalist-shallow. Median breadth: ${formatFixed(ep.medianBreadth, 3)}, depth: ${formatFixed(ep.medianDepth, 1)}.`
        ));
    }

    // M32: Cognitive Load
    const cl = cachedData.cognitiveLoad;
    if (cl) {
        const files = cl.files || [];
        const topFiles = files.slice(0, 15);
        const loadLabel = (cl.avgLoad || 0) > 0.7 ? 'high cognitive burden' : (cl.avgLoad || 0) > 0.4 ? 'moderate' : 'manageable';
        parts.push(renderMetricSection(
            'Cognitive Load',
            'Estimates the cognitive complexity a developer must manage when working on a file, based on coupling degree, directory spread, author diversity, and temporal dispersion.',
            [CITE.fakhoury2019, CITE.kapur2023],
            topFiles.length > 0
                ? renderCognitiveLoadTable(topFiles)
                : emptyState('No cognitive load data', 'Requires files with co-change history.'),
            `Average load: ${formatFixed(cl.avgLoad, 3)} (${loadLabel}). ${cl.highLoadCount || 0} high-load files out of ${cl.totalAnalyzed || 0} analyzed.`
        ));
    }

    return parts.join('');
}

// ============================================================================
// Intelligence Tab Table Renderers
// ============================================================================

function renderContextualComplexityTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Context Size</th><th>Weighted</th><th>Top Context Files</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const ctxFiles = (f.contextFiles || []).slice(0, 3).map(
            ([g, c]) => `${escapeHtml(truncatePath(g))} (${formatFixed(c, 2)})`
        ).join(', ');
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td>${f.contextSize || 0}</td>`;
        html += `<td>${formatFixed(f.weightedComplexity, 2)}</td>`;
        html += `<td class="insights-cell-small">${ctxFiles || '\u2014'}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderCommitCohesionTable(devs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Developer</th><th>Median Cohesion</th><th>Commits</th><th>Tangled Ratio</th>';
    html += '</tr></thead><tbody>';
    for (const d of devs) {
        const cohClass = (d.medianCohesion || 0) < 0.4 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td>${escapeHtml(d.author)}</td>`;
        html += `<td${cohClass}>${formatFixed(d.medianCohesion, 3)}</td>`;
        html += `<td>${d.commitCount || 0}</td>`;
        html += `<td>${formatPercentage(d.tangledRatio)}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderChangePropagationTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Risk Score</th><th>Expected Depth</th><th>Top Predictions</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const preds = (f.predictions || []).slice(0, 3).map(
            ([g, p]) => `${escapeHtml(truncatePath(g))} (${formatFixed(p, 2)})`
        ).join(', ');
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td>${formatFixed(f.riskScore, 3)}</td>`;
        html += `<td>${formatFixed(f.expectedDepth, 2)}</td>`;
        html += `<td class="insights-cell-small">${preds || '\u2014'}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderMessageQualityTable(devs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Developer</th><th>Info Density</th><th>Low-Info Ratio</th><th>Commits</th>';
    html += '</tr></thead><tbody>';
    for (const d of devs) {
        const warnClass = (d.lowInfoRatio || 0) > 0.5 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td>${escapeHtml(d.author)}</td>`;
        html += `<td>${formatFixed(d.medianInfoDensity, 3)}</td>`;
        html += `<td${warnClass}>${formatPercentage(d.lowInfoRatio)}</td>`;
        html += `<td>${d.commitCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderKnowledgeHalfLifeTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Freshness</th><th>Top Expert</th><th>Half-Life (days)</th><th>Cliff</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const cliffIcon = f.isKnowledgeCliff ? '\u26a0' : '\u2014';
        const freshClass = (f.knowledgeFreshness || 0) < 0.3 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td${freshClass}>${formatFixed(f.knowledgeFreshness, 3)}</td>`;
        html += `<td>${escapeHtml(f.topExpert || '\u2014')}</td>`;
        html += `<td>${formatFixed(f.halfLifeDays, 0)}</td>`;
        html += `<td>${cliffIcon}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderArchitecturalDriftTable(dirs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Directory</th><th>Clusters</th><th>Dominant %</th><th>Files</th>';
    html += '</tr></thead><tbody>';
    for (const d of dirs) {
        const mixedClass = (d.clusterCount || 0) > 2 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td title="${escapeHtml(d.directory)}">${escapeHtml(truncatePath(d.directory))}</td>`;
        html += `<td${mixedClass}>${d.clusterCount || 0}</td>`;
        html += `<td>${formatPercentage(d.dominantClusterPct)}</td>`;
        html += `<td>${d.fileCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderSuccessionReadinessTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Readiness</th><th>Primary</th><th>Best Successor</th><th>Gap</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const readClass = (f.readiness || 0) < 0.2 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td${readClass}>${formatFixed(f.readiness, 3)}</td>`;
        html += `<td>${escapeHtml(f.primaryContributor || '\u2014')}</td>`;
        html += `<td>${escapeHtml(f.bestSuccessor || 'None')}</td>`;
        html += `<td>${formatFixed(f.successionGap, 3)}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

// ============================================================================
// M8-M32 Table Renderers
// ============================================================================

function renderReviewerRecommendationTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Top Reviewer</th><th>Score</th><th>Ownership</th><th>Recency</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const top = (f.reviewers || [])[0];
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td>${escapeHtml(top ? top.author : '\u2014')}</td>`;
        html += `<td>${top ? formatFixed(top.score, 3) : '\u2014'}</td>`;
        html += `<td>${top ? formatFixed(top.ownership, 3) : '\u2014'}</td>`;
        html += `<td>${top ? formatFixed(top.recency, 3) : '\u2014'}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderReviewResponseTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Median (h)</th><th>P90 (h)</th><th>Reviewers</th><th>Responses</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td>${formatFixed(f.medianResponseHours, 1)}</td>`;
        html += `<td>${formatFixed(f.p90ResponseHours, 1)}</td>`;
        html += `<td>${f.uniqueReviewers || 0}</td>`;
        html += `<td>${f.totalResponses || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderOnboardingTable(devs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Developer</th><th>Type</th><th>Commits</th><th>W1\u20134</th><th>W5\u20138</th><th>Files</th>';
    html += '</tr></thead><tbody>';
    for (const d of devs) {
        html += `<tr><td>${escapeHtml(d.author)}</td>`;
        html += `<td>${escapeHtml(d.onboardingType)}</td>`;
        html += `<td>${d.totalCommits || 0}</td>`;
        html += `<td>${d.week14Commits || 0}</td>`;
        html += `<td>${d.week58Commits || 0}</td>`;
        html += `<td>${d.uniqueFiles || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderInterfaceStabilityTable(dirs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Directory</th><th>Stability</th><th>Changes</th><th>Cross-Boundary</th><th>External</th>';
    html += '</tr></thead><tbody>';
    for (const d of dirs) {
        const stabClass = (d.stability || 0) < 0.5 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td>${escapeHtml(d.directory)}</td>`;
        html += `<td${stabClass}>${formatFixed(d.stability, 3)}</td>`;
        html += `<td>${d.totalChanges || 0}</td>`;
        html += `<td>${d.crossBoundaryChanges || 0}</td>`;
        html += `<td>${d.externalContributorCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderTechDebtTable(windows) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Window</th><th>Maint %</th><th>Feature %</th><th>Debt Red %</th><th>Commits</th>';
    html += '</tr></thead><tbody>';
    for (let i = 0; i < windows.length; i++) {
        const w = windows[i];
        html += `<tr><td>Window ${i + 1}</td>`;
        html += `<td>${formatPercentage(w.maintenanceRatio)}</td>`;
        html += `<td>${formatPercentage(w.featureRatio)}</td>`;
        html += `<td>${formatPercentage(w.debtReductionRatio)}</td>`;
        html += `<td>${w.totalCommits || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderFocusDriftTable(dirs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Directory</th><th>Trend</th><th>Current</th><th>Previous</th><th>Delta</th>';
    html += '</tr></thead><tbody>';
    for (const d of dirs) {
        html += `<tr><td>${escapeHtml(d.directory)}</td>`;
        html += `<td>${escapeHtml(d.trend)}</td>`;
        html += `<td>${formatPercentage(d.currentShare)}</td>`;
        html += `<td>${formatPercentage(d.previousShare)}</td>`;
        html += `<td>${formatFixed(d.shareDelta, 3)}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderAiDetectionTable(commits) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Author</th><th>Score</th><th>Files</th><th>Dirs</th><th>Reason</th>';
    html += '</tr></thead><tbody>';
    for (const c of commits) {
        html += `<tr><td>${escapeHtml(c.author)}</td>`;
        html += `<td>${formatFixed(c.anomalyScore, 2)}</td>`;
        html += `<td>${c.filesTouched || 0}</td>`;
        html += `<td>${c.dirsTouched || 0}</td>`;
        html += `<td title="${escapeHtml(c.reason)}">${escapeHtml((c.reason || '').substring(0, 50))}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderKnowledgeGiniTable(devs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Developer</th><th>Share</th><th>Commits</th><th>Files</th>';
    html += '</tr></thead><tbody>';
    for (const d of devs) {
        html += `<tr><td>${escapeHtml(d.author)}</td>`;
        html += `<td>${formatPercentage(d.knowledgeShare)}</td>`;
        html += `<td>${d.totalCommits || 0}</td>`;
        html += `<td>${d.filesTouched || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderExpertiseProfileTable(devs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Developer</th><th>Quadrant</th><th>Breadth</th><th>Depth</th><th>Commits</th>';
    html += '</tr></thead><tbody>';
    for (const d of devs) {
        html += `<tr><td>${escapeHtml(d.author)}</td>`;
        html += `<td>${escapeHtml(d.quadrant)}</td>`;
        html += `<td>${formatFixed(d.breadth, 3)}</td>`;
        html += `<td>${formatFixed(d.depth, 1)}</td>`;
        html += `<td>${d.totalCommits || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderCognitiveLoadTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Load</th><th>Coupling</th><th>Spread</th><th>Authors</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const loadClass = (f.loadScore || 0) > 0.7 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td${loadClass}>${formatFixed(f.loadScore, 3)}</td>`;
        html += `<td>${formatFixed(f.couplingComponent, 3)}</td>`;
        html += `<td>${formatFixed(f.dirSpreadComponent, 3)}</td>`;
        html += `<td>${f.authorCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

// ============================================================================
// Strategic Tab: Next-Generation Git Mining Insights
// ============================================================================

/**
 * Strategic tab: DORA proxy metrics, knowledge currency, team rhythm,
 * commit coherence, Markov prediction, repository health score.
 *
 * Data sources (all verified against insights.rs):
 * - cachedData.doraProxy: unwrapped from getDoraProxy().doraProxy
 * - cachedData.knowledgeCurrencyData: unwrapped from getKnowledgeCurrency().knowledgeCurrency
 * - cachedData.teamRhythmData: unwrapped from getTeamRhythm().teamRhythm
 * - cachedData.commitCoherenceData: unwrapped from getCommitCoherence().commitCoherence
 * - cachedData.markovPrediction: unwrapped from getMarkovPrediction().markovPrediction
 * - cachedData.repoHealth: unwrapped from getRepoHealth().repoHealth
 */
export function renderStrategicTab(cachedData) {
    const parts = [];

    parts.push(renderTabIntro(
        'Strategic Intelligence',
        'Next-generation metrics combining DORA performance proxies, knowledge decay modeling, circular statistics, Markov chain predictions, and composite health scoring. All computed purely from VCS commit data.'
    ));

    parts.push(renderMetricNav([
        'Repository Health', 'DORA Proxy', 'Knowledge Currency',
        'Team Rhythm', 'Commit Coherence', 'Markov Prediction'
    ]));

    // Repository Health Score (Borg et al. 2024)
    const rh = cachedData.repoHealth;
    if (rh) {
        const dims = rh.dimensions || {};
        const dimList = [
            ['Bus Factor Coverage', formatFixed(dims.busFactorCoverage, 3)],
            ['Knowledge Currency', formatFixed(dims.knowledgeCurrency, 3)],
            ['Commit Atomicity', formatFixed(dims.commitAtomicity, 3)],
            ['Ownership Health', formatFixed(dims.ownershipHealth, 3)],
            ['Change Stability', formatFixed(dims.changeStability, 3)],
            ['Defect Risk (inverse)', formatFixed(dims.defectRiskInverse, 3)],
        ];
        parts.push(renderMetricSection(
            'Repository Health',
            'Composite health score combining 6 weighted dimensions into a single grade. Higher scores indicate healthier repositories with lower risk.',
            [CITE.borg2024, CITE.avelino2016, CITE.bird2011],
            renderKeyValueList(dimList),
            `Overall score: ${formatFixed(rh.score, 1)}/100 (Grade: ${escapeHtml(rh.grade || '?')}). ${escapeHtml(rh.interpretation || '')}`
        ));
    }

    // DORA Proxy Metrics (Forsgren et al. 2018)
    const dora = cachedData.doraProxy;
    if (dora) {
        const kvs = [
            ['Merge Frequency', `${formatFixed(dora.mergeFrequencyPerWeek, 2)}/week`],
            ['Avg Branch Duration', `${formatFixed(dora.avgBranchDurationHours, 1)} hours`],
            ['Revert Ratio', formatFixed(dora.revertRatio, 4)],
            ['Avg Recovery Time', `${formatFixed(dora.avgRecoveryHours, 1)} hours`],
            ['Rework Ratio', formatFixed(dora.reworkRatio, 4)],
            ['Performance Tier', escapeHtml(dora.performanceTier || 'unknown')],
        ];
        parts.push(renderMetricSection(
            'DORA Proxy',
            'Proxy measures for DORA\u2019s Four Key Metrics derived entirely from VCS commit patterns: merge frequency, branch duration, revert ratio, and recovery time.',
            [CITE.forsgren2018],
            renderKeyValueList(kvs),
            `${dora.totalCommits || 0} total commits. ${dora.mergeCount || 0} merges, ${dora.revertCount || 0} reverts, ${dora.fixCount || 0} fixes detected.`
        ));
    }

    // Knowledge Currency (Fritz et al. 2010, Ebbinghaus 1885)
    const kc = cachedData.knowledgeCurrencyData;
    if (kc) {
        const files = (kc.files || []).slice(0, 15);
        parts.push(renderMetricSection(
            'Knowledge Currency',
            'Per-file knowledge freshness combining recency, exponential decay (Ebbinghaus forgetting curve), knowledge refreshes, and active contributor count.',
            [CITE.fritz2010_dok, CITE.ebbinghaus1885, CITE.jabrayilzade2022],
            files.length > 0
                ? renderKnowledgeCurrencyTable(files)
                : emptyState('No knowledge currency data', 'Requires commit history with file-author timestamps.'),
            `Average currency: ${formatFixed(kc.avgCurrency, 3)}. ${kc.staleCount || 0} stale files (< 0.3), ${kc.currentCount || 0} current files (\u2265 0.7) out of ${kc.totalFiles || 0} total.`
        ));
    }

    // Team Rhythm (Fisher 1993)
    const tr = cachedData.teamRhythmData;
    if (tr) {
        const devs = (tr.developers || []).slice(0, 15);
        parts.push(renderMetricSection(
            'Team Rhythm',
            'Circular statistics on commit hour-of-day distributions measuring developer regularity and team synchronization. High sync indicates cadence alignment; low sync suggests asynchronous patterns.',
            [CITE.fisher1993, CITE.eyolfson2011, CITE.cataldo2008_coord],
            devs.length > 0
                ? renderTeamRhythmTable(devs)
                : emptyState('No team rhythm data', 'Requires commits from multiple developers.'),
            `Team sync score: ${formatFixed(tr.teamSyncScore, 3)}. Mean hour: ${formatFixed(tr.teamMeanHour, 1)}h. ${tr.highSyncPairs || 0} high-sync pairs, ${tr.lowSyncPairs || 0} low-sync pairs out of ${tr.totalPairs || 0} total.`
        ));
    }

    // Commit Coherence (Herzig & Zeller 2013)
    const cc = cachedData.commitCoherenceData;
    if (cc) {
        const commits = (cc.commits || []).slice(0, 15);
        parts.push(renderMetricSection(
            'Commit Coherence',
            'Per-commit quality score measuring how logically coherent each change is. Low coherence indicates tangled commits that combine unrelated concerns and should have been split.',
            [CITE.herzig2013, CITE.xu2025],
            commits.length > 0
                ? renderCommitCoherenceTable(commits)
                : emptyState('No commit coherence data', 'Requires multi-file commits for analysis.'),
            `Atomicity index (median coherence): ${formatFixed(cc.atomicityIndex, 3)}. Tangled fraction: ${formatFixed(cc.tangledFraction, 3)}. ${cc.totalAnalyzed || 0} multi-file commits analyzed.`
        ));
    }

    // Markov Prediction (Hassan & Holt 2004)
    const mp = cachedData.markovPrediction;
    if (mp) {
        const preds = (mp.filePredictions || []).slice(0, 15);
        parts.push(renderMetricSection(
            'Markov Prediction',
            'First-order Markov chain transition matrix predicting which files are likely to need changes next based on historical co-change patterns.',
            [CITE.hassan2004, CITE.zimmermann2005, CITE.balachandran2013],
            preds.length > 0
                ? renderMarkovPredictionTable(preds)
                : emptyState('No prediction data', 'Requires multi-file commits for transition analysis.'),
            `${mp.totalFiles || 0} files in transition matrix, ${mp.totalTransitions || 0} transitions observed. Matrix sparsity: ${formatFixed(mp.matrixSparsity, 3)}.`
        ));
    }

    return parts.join('');
}

// ---- Strategic tab table renderers ----

function renderKnowledgeCurrencyTable(files) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>File</th><th>Currency</th><th>Days Stale</th><th>Active</th><th>Total</th><th>Refreshes</th>';
    html += '</tr></thead><tbody>';
    for (const f of files) {
        const cls = (f.currency || 0) < 0.3 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td title="${escapeHtml(f.path)}">${escapeHtml(truncatePath(f.path))}</td>`;
        html += `<td${cls}>${formatFixed(f.currency, 3)}</td>`;
        html += `<td>${formatFixed(f.daysSinceLastTouch, 0)}</td>`;
        html += `<td>${f.activeContributors || 0}</td>`;
        html += `<td>${f.totalContributors || 0}</td>`;
        html += `<td>${f.refreshCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderTeamRhythmTable(devs) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Developer</th><th>Mean Hour</th><th>R\u0304</th><th>Type</th><th>Commits</th>';
    html += '</tr></thead><tbody>';
    for (const d of devs) {
        html += `<tr><td>${escapeHtml(d.author)}</td>`;
        html += `<td>${formatFixed(d.meanHour, 1)}h</td>`;
        html += `<td>${formatFixed(d.resultantLength, 3)}</td>`;
        html += `<td>${escapeHtml(d.rhythmType || '')}</td>`;
        html += `<td>${d.commitCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderCommitCoherenceTable(commits) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Author</th><th>Coherence</th><th>Files</th><th>Dirs</th><th>Type Homog.</th>';
    html += '</tr></thead><tbody>';
    for (const c of commits) {
        const cls = (c.coherence || 0) < 0.5 ? ' class="insights-cell-warn"' : '';
        html += `<tr><td>${escapeHtml(c.author)}</td>`;
        html += `<td${cls}>${formatFixed(c.coherence, 3)}</td>`;
        html += `<td>${c.fileCount || 0}</td>`;
        html += `<td>${c.directoryCount || 0}</td>`;
        html += `<td>${formatFixed(c.typeHomogeneity, 3)}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

function renderMarkovPredictionTable(preds) {
    let html = '<div class="insights-table-wrapper"><table class="insights-table"><thead><tr>';
    html += '<th>Source File</th><th>Top Prediction</th><th>Probability</th><th>Transitions</th>';
    html += '</tr></thead><tbody>';
    for (const fp of preds) {
        const top = (fp.predictions || [])[0];
        html += `<tr><td title="${escapeHtml(fp.source)}">${escapeHtml(truncatePath(fp.source))}</td>`;
        if (top) {
            html += `<td title="${escapeHtml(top.target)}">${escapeHtml(truncatePath(top.target))}</td>`;
            html += `<td>${formatFixed(top.probability, 3)}</td>`;
        } else {
            html += '<td>-</td><td>-</td>';
        }
        html += `<td>${fp.transitionCount || 0}</td></tr>`;
    }
    html += '</tbody></table></div>';
    return html;
}

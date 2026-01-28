// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Timeline Date Tick Marks
 *
 * Generates visual tick marks on the timeline slider showing time period boundaries
 * (days, weeks, months, years) to help users understand the temporal distribution of commits.
 */

import { getRource } from './state.js';
import { safeWasmCall } from './wasm-api.js';
import { getElement } from './dom.js';

// Constants for interval determination
const MS_PER_DAY = 24 * 60 * 60 * 1000;
const DAYS_PER_WEEK = 7;
const DAYS_IN_YEAR = 365;

/**
 * Interval types in order of granularity (finest to coarsest)
 */
const INTERVAL_TYPES = {
    DAILY: 'daily',
    WEEKLY: 'weekly',
    MONTHLY: 'monthly',
    QUARTERLY: 'quarterly',
    YEARLY: 'yearly',
};

/**
 * Configuration for each interval type
 */
const INTERVAL_CONFIG = {
    [INTERVAL_TYPES.DAILY]: {
        maxDays: 14,              // Use daily ticks for repos up to 14 days
        minTicks: 2,              // Minimum ticks to display
        maxTicks: 14,             // Maximum ticks to display
        markerClass: 'tick-day',
        heightClass: 'tick-minor',
    },
    [INTERVAL_TYPES.WEEKLY]: {
        maxDays: 90,              // Use weekly ticks for repos up to ~3 months
        minTicks: 2,
        maxTicks: 13,             // ~13 weeks in 3 months
        markerClass: 'tick-week',
        heightClass: 'tick-minor',
    },
    [INTERVAL_TYPES.MONTHLY]: {
        maxDays: DAYS_IN_YEAR * 3, // Use monthly for repos up to 3 years
        minTicks: 2,
        maxTicks: 36,             // 36 months in 3 years
        markerClass: 'tick-month',
        heightClass: 'tick-medium',
    },
    [INTERVAL_TYPES.QUARTERLY]: {
        maxDays: DAYS_IN_YEAR * 8, // Use quarterly for repos up to 8 years
        minTicks: 2,
        maxTicks: 32,             // 32 quarters in 8 years
        markerClass: 'tick-quarter',
        heightClass: 'tick-medium',
    },
    [INTERVAL_TYPES.YEARLY]: {
        maxDays: Infinity,        // Use yearly for anything larger
        minTicks: 2,
        maxTicks: 25,             // Allow more year ticks but will be dynamically spaced
        markerClass: 'tick-year',
        heightClass: 'tick-major',
    },
};

/**
 * Determines the optimal year step for very long repositories.
 * For repos spanning many years, we skip years to avoid overcrowding.
 *
 * @param {number} totalYears - Total number of years in the repo
 * @returns {number} Step size for year boundaries (1, 2, 5, 10, etc.)
 */
function getYearStep(totalYears) {
    if (totalYears <= 15) return 1;       // Show every year
    if (totalYears <= 30) return 2;       // Show every 2 years
    if (totalYears <= 60) return 5;       // Show every 5 years
    if (totalYears <= 120) return 10;     // Show every decade
    return 20;                            // Show every 20 years for very old repos
}

/**
 * Determines the appropriate tick interval based on the date range.
 * @param {number} startTimestamp - Start timestamp in seconds
 * @param {number} endTimestamp - End timestamp in seconds
 * @returns {string} Interval type from INTERVAL_TYPES
 */
export function determineInterval(startTimestamp, endTimestamp) {
    const rangeDays = (endTimestamp - startTimestamp) / (24 * 60 * 60);

    for (const [type, config] of Object.entries(INTERVAL_CONFIG)) {
        if (rangeDays <= config.maxDays) {
            return type;
        }
    }

    return INTERVAL_TYPES.YEARLY;
}

/**
 * Gets the start of the day for a given date.
 * @param {Date} date - Input date
 * @returns {Date} Start of day
 */
function startOfDay(date) {
    const d = new Date(date);
    d.setHours(0, 0, 0, 0);
    return d;
}

/**
 * Gets the start of the week (Monday) for a given date.
 * @param {Date} date - Input date
 * @returns {Date} Start of week (Monday)
 */
function startOfWeek(date) {
    const d = new Date(date);
    const day = d.getDay();
    const diff = day === 0 ? -6 : 1 - day; // Monday is day 1
    d.setDate(d.getDate() + diff);
    d.setHours(0, 0, 0, 0);
    return d;
}

/**
 * Gets the start of the month for a given date.
 * @param {Date} date - Input date
 * @returns {Date} Start of month
 */
function startOfMonth(date) {
    return new Date(date.getFullYear(), date.getMonth(), 1);
}

/**
 * Gets the start of the quarter for a given date.
 * @param {Date} date - Input date
 * @returns {Date} Start of quarter
 */
function startOfQuarter(date) {
    const quarterMonth = Math.floor(date.getMonth() / 3) * 3;
    return new Date(date.getFullYear(), quarterMonth, 1);
}

/**
 * Gets the start of the year for a given date.
 * @param {Date} date - Input date
 * @returns {Date} Start of year
 */
function startOfYear(date) {
    return new Date(date.getFullYear(), 0, 1);
}

/**
 * Generates date boundaries for daily ticks.
 * For very short repos (< 7 days), includes the start date itself to ensure
 * at least one tick is shown.
 *
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean, isMajor: boolean}>} Array of boundaries
 */
function generateDailyBoundaries(start, end) {
    const boundaries = [];
    const rangeDays = (end - start) / MS_PER_DAY;

    // For very short repos (< 3 days), include the start date boundary
    // to ensure we have at least one tick
    if (rangeDays < 3) {
        boundaries.push({
            date: new Date(startOfDay(start)),
            label: formatDayLabel(start),
            isFirst: true,
            isMajor: true,
        });
    }

    let current = startOfDay(new Date(start.getTime() + MS_PER_DAY));

    while (current <= end) {
        const isFirstOfMonth = current.getDate() === 1;
        boundaries.push({
            date: new Date(current),
            label: formatDayLabel(current),
            isFirst: isFirstOfMonth,
            isMajor: isFirstOfMonth || rangeDays < 7, // All ticks major for very short repos
        });
        current.setDate(current.getDate() + 1);
    }

    return boundaries;
}

/**
 * Generates date boundaries for weekly ticks.
 * For repos < 3 weeks, includes the first week's Monday to ensure visibility.
 *
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean, isMajor: boolean}>} Array of boundaries
 */
function generateWeeklyBoundaries(start, end) {
    const boundaries = [];
    const rangeWeeks = (end - start) / (DAYS_PER_WEEK * MS_PER_DAY);

    // For very short repos (< 2 weeks), include the start week
    if (rangeWeeks < 2) {
        const startWeek = startOfWeek(start);
        boundaries.push({
            date: new Date(startWeek),
            label: formatWeekLabel(startWeek),
            isFirst: true,
            isMajor: true,
        });
    }

    let current = startOfWeek(new Date(start.getTime() + DAYS_PER_WEEK * MS_PER_DAY));

    while (current <= end) {
        const isFirstOfMonth = current.getDate() <= 7;
        boundaries.push({
            date: new Date(current),
            label: formatWeekLabel(current),
            isFirst: isFirstOfMonth,
            isMajor: isFirstOfMonth || rangeWeeks < 6, // All ticks major for short repos
        });
        current.setDate(current.getDate() + 7);
    }

    return boundaries;
}

/**
 * Generates date boundaries for monthly ticks.
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean}>} Array of boundaries
 */
function generateMonthlyBoundaries(start, end) {
    const boundaries = [];
    let current = startOfMonth(start);
    current.setMonth(current.getMonth() + 1);

    while (current <= end) {
        const isJanuary = current.getMonth() === 0;
        boundaries.push({
            date: new Date(current),
            label: formatMonthLabel(current),
            isFirst: isJanuary,
            isMajor: isJanuary,
        });
        current.setMonth(current.getMonth() + 1);
    }

    return boundaries;
}

/**
 * Generates date boundaries for quarterly ticks.
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean}>} Array of boundaries
 */
function generateQuarterlyBoundaries(start, end) {
    const boundaries = [];
    let current = startOfQuarter(start);
    current.setMonth(current.getMonth() + 3);

    while (current <= end) {
        const isQ1 = current.getMonth() === 0;
        boundaries.push({
            date: new Date(current),
            label: formatQuarterLabel(current),
            isFirst: isQ1,
            isMajor: isQ1,
        });
        current.setMonth(current.getMonth() + 3);
    }

    return boundaries;
}

/**
 * Generates date boundaries for yearly ticks with adaptive stepping.
 * For very long repos (10+ years), uses dynamic year stepping to avoid overcrowding.
 *
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean, isMajor: boolean}>} Array of boundaries
 */
function generateYearlyBoundaries(start, end) {
    const boundaries = [];
    const startYear = start.getFullYear();
    const endYear = end.getFullYear();
    const totalYears = endYear - startYear + 1;

    // Determine optimal step size based on total years
    const yearStep = getYearStep(totalYears);

    // Find the first "round" year boundary after start (aligned to step)
    // e.g., if step=5 and startYear=2013, first boundary is 2015
    let firstBoundaryYear = Math.ceil((startYear + 1) / yearStep) * yearStep;
    if (firstBoundaryYear <= startYear) {
        firstBoundaryYear += yearStep;
    }

    let current = new Date(firstBoundaryYear, 0, 1);

    while (current <= end) {
        const year = current.getFullYear();
        // Mark as major if it's a decade or the step is large
        const isDecade = year % 10 === 0;
        const isMajor = isDecade || yearStep >= 5;

        boundaries.push({
            date: new Date(current),
            label: formatYearLabel(current),
            isFirst: false,
            isMajor: isMajor,
        });
        current.setFullYear(current.getFullYear() + yearStep);
    }

    // Always include the start year if not already present and there are boundaries
    // This helps anchor the timeline visually
    if (boundaries.length > 0 && boundaries[0].date.getFullYear() > startYear + 1) {
        const startBoundary = new Date(startYear + 1, 0, 1);
        if (startBoundary <= end) {
            boundaries.unshift({
                date: startBoundary,
                label: formatYearLabel(startBoundary),
                isFirst: true,
                isMajor: false,
            });
        }
    }

    return boundaries;
}

/**
 * Formats a day label.
 * @param {Date} date - Date to format
 * @returns {string} Formatted label
 */
function formatDayLabel(date) {
    return date.toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
}

/**
 * Formats a week label.
 * @param {Date} date - Date to format
 * @returns {string} Formatted label
 */
function formatWeekLabel(date) {
    return date.toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
}

/**
 * Formats a month label.
 * @param {Date} date - Date to format
 * @returns {string} Formatted label
 */
function formatMonthLabel(date) {
    return date.toLocaleDateString(undefined, { month: 'short', year: '2-digit' });
}

/**
 * Formats a quarter label.
 * @param {Date} date - Date to format
 * @returns {string} Formatted label
 */
function formatQuarterLabel(date) {
    const quarter = Math.floor(date.getMonth() / 3) + 1;
    return `Q${quarter} ${date.getFullYear()}`;
}

/**
 * Formats a year label.
 * @param {Date} date - Date to format
 * @returns {string} Formatted label
 */
function formatYearLabel(date) {
    return date.getFullYear().toString();
}

/**
 * Generates tick boundaries based on interval type.
 * @param {string} intervalType - Interval type from INTERVAL_TYPES
 * @param {Date} startDate - Start date
 * @param {Date} endDate - End date
 * @returns {Array} Array of boundary objects
 */
function generateBoundaries(intervalType, startDate, endDate) {
    switch (intervalType) {
        case INTERVAL_TYPES.DAILY:
            return generateDailyBoundaries(startDate, endDate);
        case INTERVAL_TYPES.WEEKLY:
            return generateWeeklyBoundaries(startDate, endDate);
        case INTERVAL_TYPES.MONTHLY:
            return generateMonthlyBoundaries(startDate, endDate);
        case INTERVAL_TYPES.QUARTERLY:
            return generateQuarterlyBoundaries(startDate, endDate);
        case INTERVAL_TYPES.YEARLY:
            return generateYearlyBoundaries(startDate, endDate);
        default:
            return [];
    }
}

/**
 * Calculates the position percentage for a timestamp within the timeline.
 * NOTE: This function is deprecated for tick positioning. Use calculatePositionByCommitIndex instead.
 * @param {number} timestamp - Timestamp in seconds
 * @param {number} startTimestamp - Start timestamp in seconds
 * @param {number} endTimestamp - End timestamp in seconds
 * @returns {number} Position as percentage (0-100)
 */
function calculatePosition(timestamp, startTimestamp, endTimestamp) {
    if (endTimestamp === startTimestamp) return 50;
    return ((timestamp - startTimestamp) / (endTimestamp - startTimestamp)) * 100;
}

/**
 * Finds the first commit index ON OR AFTER a given timestamp using binary search.
 * The slider is positioned by commit index, not timestamp, so tick marks
 * must be positioned by commit index to align properly.
 *
 * Returns -1 if no commit exists on or after the target timestamp.
 *
 * @param {Object} rource - Rource WASM instance
 * @param {number} targetTimestamp - Target timestamp in seconds
 * @param {number} totalCommits - Total number of commits
 * @returns {number} First commit index on or after the target timestamp, or -1 if none
 */
function findFirstCommitOnOrAfter(rource, targetTimestamp, totalCommits) {
    if (totalCommits === 0) return -1;
    if (totalCommits === 1) {
        const ts = safeWasmCall('getCommitTimestamp', () => rource.getCommitTimestamp(0), 0);
        return ts >= targetTimestamp ? 0 : -1;
    }

    let low = 0;
    let high = totalCommits - 1;

    // Binary search for first commit >= target
    while (low < high) {
        const mid = Math.floor((low + high) / 2);
        const midTimestamp = safeWasmCall(
            'getCommitTimestamp',
            () => rource.getCommitTimestamp(mid),
            0
        );

        if (midTimestamp < targetTimestamp) {
            low = mid + 1;
        } else {
            high = mid;
        }
    }

    // Verify the commit at 'low' is actually >= target
    const lowTimestamp = safeWasmCall(
        'getCommitTimestamp',
        () => rource.getCommitTimestamp(low),
        0
    );

    if (lowTimestamp < targetTimestamp) {
        return -1; // No commit on or after this boundary
    }

    return low;
}

/**
 * Calculates the position percentage for a tick based on commit index.
 * This aligns tick marks with the slider's commit-based positioning.
 *
 * @param {number} commitIndex - Commit index
 * @param {number} totalCommits - Total number of commits
 * @returns {number} Position as percentage (0-100)
 */
function calculatePositionByCommitIndex(commitIndex, totalCommits) {
    if (totalCommits <= 1) return 50;
    return (commitIndex / (totalCommits - 1)) * 100;
}

/**
 * Formats a full date label for tooltip display.
 * @param {Date} date - Date to format
 * @returns {string} Full formatted date
 */
function formatFullDateLabel(date) {
    return date.toLocaleDateString(undefined, {
        weekday: 'short',
        year: 'numeric',
        month: 'short',
        day: 'numeric',
    });
}

/**
 * Creates a tick marker DOM element.
 * The tick represents a time period boundary (e.g., start of 2024) but is positioned
 * at the first commit on or after that boundary, so the tooltip shows both the
 * period label and the actual commit date for clarity.
 *
 * @param {Object} boundary - Boundary object with date, label, isMajor, actualDate
 * @param {number} position - Position percentage
 * @param {Object} config - Interval configuration
 * @param {boolean} showLabel - Whether to show an inline label
 * @returns {HTMLElement} Tick marker element
 */
function createTickElement(boundary, position, config, showLabel = false) {
    const tick = document.createElement('div');
    tick.className = `timeline-tick ${config.markerClass} ${config.heightClass}`;

    if (boundary.isMajor) {
        tick.classList.add('tick-major');
    }

    tick.style.left = `${position}%`;

    // Use actual commit date for accurate positioning and tooltip
    const displayDate = boundary.actualDate || boundary.date;
    const boundaryDate = boundary.date;

    tick.setAttribute('data-date', displayDate.toISOString());

    // Build informative tooltip: show period label + actual commit date
    // E.g., "2024 • First commit: Jan 15, 2024"
    const actualDateStr = formatFullDateLabel(displayDate);
    const periodLabel = boundary.label;

    // Check if actual date differs significantly from boundary date
    const daysDiff = Math.abs(displayDate - boundaryDate) / MS_PER_DAY;
    let tooltipText;
    if (daysDiff < 1) {
        // Commit is on or very close to boundary date
        tooltipText = actualDateStr;
    } else {
        // Commit is after boundary - show both for clarity
        tooltipText = `${periodLabel} • ${actualDateStr}`;
    }

    tick.setAttribute('data-label', tooltipText);
    tick.setAttribute('title', tooltipText);

    // Accessibility: describe the marker
    tick.setAttribute('role', 'img');
    tick.setAttribute('aria-label', `Timeline marker: ${periodLabel}`);

    // Add inline label for major ticks or when explicitly requested
    if (showLabel && (boundary.isMajor || config.heightClass === 'tick-major')) {
        const label = document.createElement('span');
        label.className = 'timeline-tick-label';
        label.textContent = boundary.label;
        tick.appendChild(label);
    }

    return tick;
}

/**
 * Generates and renders date tick marks on the timeline.
 * This is the main entry point called when data is loaded.
 *
 * The algorithm:
 * 1. Determines the appropriate interval type based on date range
 * 2. For very long repos (10+ years), uses adaptive year stepping
 * 3. Positions ticks based on commit index (not timestamp) to align with slider
 * 4. Ensures first/last boundaries are visible for context
 */
export function generateTimelineTicks() {
    const rource = getRource();
    const timelineMarkers = getElement('timelineMarkers');

    if (!rource || !timelineMarkers) {
        return;
    }

    // Clear existing ticks
    timelineMarkers.innerHTML = '';

    // Get commit count
    const totalCommits = safeWasmCall('commitCount', () => rource.commitCount(), 0);
    if (totalCommits < 2) {
        return; // Not enough commits for meaningful ticks
    }

    // Get timestamp range from first and last commits
    const startTimestamp = safeWasmCall(
        'getCommitTimestamp',
        () => rource.getCommitTimestamp(0),
        0
    );
    const endTimestamp = safeWasmCall(
        'getCommitTimestamp',
        () => rource.getCommitTimestamp(totalCommits - 1),
        0
    );

    if (startTimestamp <= 0 || endTimestamp <= 0 || startTimestamp >= endTimestamp) {
        return; // Invalid timestamp range
    }

    // Convert to Date objects
    const startDate = new Date(startTimestamp * 1000);
    const endDate = new Date(endTimestamp * 1000);

    // Calculate date range info for debugging and interval selection
    const rangeDays = (endTimestamp - startTimestamp) / (24 * 60 * 60);
    const rangeYears = rangeDays / DAYS_IN_YEAR;

    // Determine appropriate interval
    const intervalType = determineInterval(startTimestamp, endTimestamp);
    const config = INTERVAL_CONFIG[intervalType];

    // Generate boundaries
    let boundaries = generateBoundaries(intervalType, startDate, endDate);

    // Log useful debug info for development
    if (typeof console !== 'undefined' && console.debug) {
        console.debug(
            `Timeline: ${totalCommits} commits, ${rangeDays.toFixed(0)} days (${rangeYears.toFixed(1)} years), ` +
            `interval: ${intervalType}, boundaries: ${boundaries.length}`
        );
    }

    // Check if we have too few or too many ticks
    if (boundaries.length < config.minTicks) {
        // Try a finer granularity
        const finerInterval = getFinerInterval(intervalType);
        if (finerInterval) {
            const finerConfig = INTERVAL_CONFIG[finerInterval];
            const finerBoundaries = generateBoundaries(finerInterval, startDate, endDate);
            if (finerBoundaries.length >= 2) {
                renderTicks(finerBoundaries, finerConfig, startTimestamp, endTimestamp, timelineMarkers, rource, totalCommits);
                return;
            }
        }

        // If still too few, just render what we have (better than nothing)
        if (boundaries.length > 0) {
            renderTicks(boundaries, config, startTimestamp, endTimestamp, timelineMarkers, rource, totalCommits);
        }
        return;
    }

    // For very long repos that still have too many ticks after boundary generation,
    // the generateYearlyBoundaries function already handles dynamic stepping,
    // so we just render what we have
    if (boundaries.length > config.maxTicks && intervalType === INTERVAL_TYPES.YEARLY) {
        // Yearly with dynamic stepping already applied - render as-is
        // The adaptive getYearStep() should have handled this
        renderTicks(boundaries, config, startTimestamp, endTimestamp, timelineMarkers, rource, totalCommits);
        return;
    }

    if (boundaries.length > config.maxTicks) {
        // Try a coarser granularity for non-yearly intervals
        const coarserInterval = getCoarserInterval(intervalType);
        if (coarserInterval) {
            const coarserConfig = INTERVAL_CONFIG[coarserInterval];
            const coarserBoundaries = generateBoundaries(coarserInterval, startDate, endDate);
            renderTicks(coarserBoundaries, coarserConfig, startTimestamp, endTimestamp, timelineMarkers, rource, totalCommits);
            return;
        }
    }

    renderTicks(boundaries, config, startTimestamp, endTimestamp, timelineMarkers, rource, totalCommits);
}

/**
 * Gets a finer interval type.
 * @param {string} intervalType - Current interval type
 * @returns {string|null} Finer interval type or null
 */
function getFinerInterval(intervalType) {
    const order = [
        INTERVAL_TYPES.DAILY,
        INTERVAL_TYPES.WEEKLY,
        INTERVAL_TYPES.MONTHLY,
        INTERVAL_TYPES.QUARTERLY,
        INTERVAL_TYPES.YEARLY,
    ];
    const index = order.indexOf(intervalType);
    return index > 0 ? order[index - 1] : null;
}

/**
 * Gets a coarser interval type.
 * @param {string} intervalType - Current interval type
 * @returns {string|null} Coarser interval type or null
 */
function getCoarserInterval(intervalType) {
    const order = [
        INTERVAL_TYPES.DAILY,
        INTERVAL_TYPES.WEEKLY,
        INTERVAL_TYPES.MONTHLY,
        INTERVAL_TYPES.QUARTERLY,
        INTERVAL_TYPES.YEARLY,
    ];
    const index = order.indexOf(intervalType);
    return index < order.length - 1 ? order[index + 1] : null;
}

/**
 * Determines which ticks should show inline labels.
 * Returns indices of ticks that should have labels, spaced to avoid overlap.
 * @param {Array} boundaries - Array of boundary objects with positions calculated
 * @param {number} minSpacing - Minimum spacing percentage between labels
 * @returns {Set<number>} Set of indices that should show labels
 */
function selectLabeledTicks(boundaries, minSpacing = 15) {
    const labeled = new Set();
    let lastLabelPos = -Infinity;

    // First pass: label all major ticks that have enough spacing
    for (let i = 0; i < boundaries.length; i++) {
        const boundary = boundaries[i];
        if (boundary.isMajor && boundary.position - lastLabelPos >= minSpacing) {
            labeled.add(i);
            lastLabelPos = boundary.position;
        }
    }

    // If we have very few labels, try to add more
    if (labeled.size < 3 && boundaries.length >= 3) {
        lastLabelPos = -Infinity;
        for (let i = 0; i < boundaries.length; i++) {
            const boundary = boundaries[i];
            if (boundary.position - lastLabelPos >= minSpacing) {
                labeled.add(i);
                lastLabelPos = boundary.position;
            }
        }
    }

    return labeled;
}

/**
 * Renders tick marks to the container.
 * Tick positions are calculated based on commit index, not timestamp,
 * to align with the slider which is commit-index based.
 *
 * @param {Array} boundaries - Array of boundary objects
 * @param {Object} config - Interval configuration
 * @param {number} startTimestamp - Start timestamp in seconds
 * @param {number} endTimestamp - End timestamp in seconds
 * @param {HTMLElement} container - Container element
 * @param {Object} rource - Rource WASM instance
 * @param {number} totalCommits - Total number of commits
 */
function renderTicks(boundaries, config, startTimestamp, endTimestamp, container, rource, totalCommits) {
    // Create document fragment for performance
    const fragment = document.createDocumentFragment();

    // Calculate positions based on COMMIT INDEX (not timestamp)
    // This is critical: the slider is positioned by commit index, so tick marks
    // must use commit-index-based positions to align correctly.
    const mappedBoundaries = boundaries
        .map((boundary, originalIndex) => {
            const timestampSecs = boundary.date.getTime() / 1000;
            // Find the FIRST commit on or after this boundary date
            // This ensures "February" tick points to the first February commit,
            // not the last January commit (which might be closer in time)
            const commitIndex = findFirstCommitOnOrAfter(rource, timestampSecs, totalCommits);
            if (commitIndex < 0) return null; // No commit on or after this boundary
            // Get the actual commit timestamp for accurate tooltip
            const actualTimestamp = safeWasmCall(
                'getCommitTimestamp',
                () => rource.getCommitTimestamp(commitIndex),
                0
            );
            const actualDate = new Date(actualTimestamp * 1000);
            // Calculate position based on commit index, not timestamp
            const position = calculatePositionByCommitIndex(commitIndex, totalCommits);
            return { ...boundary, position, commitIndex, actualDate, originalIndex };
        })
        .filter(boundary => boundary !== null);

    // Dedupe boundaries that map to the same commit index
    // (e.g., if no commits for 2 months, both month ticks would point to same commit)
    const seenCommitIndices = new Set();
    let dedupedBoundaries = mappedBoundaries.filter(boundary => {
        if (seenCommitIndices.has(boundary.commitIndex)) {
            return false;
        }
        seenCommitIndices.add(boundary.commitIndex);
        return true;
    });

    // Calculate date range to adjust filtering for short repos
    const rangeDays = (endTimestamp - startTimestamp) / (24 * 60 * 60);
    const isShortRepo = rangeDays < 30; // Less than a month

    // Apply edge filtering with special handling for first/last boundaries
    // For short repos, be more permissive to show more context
    const filteredBoundaries = dedupedBoundaries.filter((boundary, index, arr) => {
        const isFirst = index === 0;
        const isLast = index === arr.length - 1;

        // For very short repos, allow ticks anywhere
        if (isShortRepo) {
            return true;
        }

        if (isFirst) {
            // First tick: allow closer to left edge (1%)
            return boundary.position >= 1;
        } else if (isLast) {
            // Last tick: allow closer to right edge (99%)
            return boundary.position <= 99;
        } else {
            // Middle ticks: keep away from edges (3%-97%)
            return boundary.position > 3 && boundary.position < 97;
        }
    });

    // If we have very few ticks after filtering, be more permissive
    let finalBoundaries = filteredBoundaries;
    if (filteredBoundaries.length < 2 && dedupedBoundaries.length >= 2) {
        // Use all deduped boundaries if filtering removed too many
        finalBoundaries = dedupedBoundaries;
    }

    // Determine which ticks get inline labels
    const labeledIndices = selectLabeledTicks(finalBoundaries);

    // Add ticks
    finalBoundaries.forEach((boundary, index) => {
        const showLabel = labeledIndices.has(index);
        const tick = createTickElement(boundary, boundary.position, config, showLabel);
        fragment.appendChild(tick);
    });

    // Append all at once
    container.appendChild(fragment);

    // Trigger animation after a brief delay
    requestAnimationFrame(() => {
        const ticks = container.querySelectorAll('.timeline-tick');
        ticks.forEach((tick, index) => {
            tick.style.animationDelay = `${index * 20}ms`;
            tick.classList.add('visible');
        });
    });
}

/**
 * Clears all timeline tick marks.
 */
export function clearTimelineTicks() {
    const timelineMarkers = getElement('timelineMarkers');
    if (timelineMarkers) {
        timelineMarkers.innerHTML = '';
    }
}

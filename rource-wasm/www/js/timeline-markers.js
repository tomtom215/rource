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
        maxTicks: 20,
        markerClass: 'tick-year',
        heightClass: 'tick-major',
    },
};

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
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean}>} Array of boundaries
 */
function generateDailyBoundaries(start, end) {
    const boundaries = [];
    let current = startOfDay(new Date(start.getTime() + MS_PER_DAY));

    while (current <= end) {
        const isFirstOfMonth = current.getDate() === 1;
        boundaries.push({
            date: new Date(current),
            label: formatDayLabel(current),
            isFirst: isFirstOfMonth,
            isMajor: isFirstOfMonth,
        });
        current.setDate(current.getDate() + 1);
    }

    return boundaries;
}

/**
 * Generates date boundaries for weekly ticks.
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean}>} Array of boundaries
 */
function generateWeeklyBoundaries(start, end) {
    const boundaries = [];
    let current = startOfWeek(new Date(start.getTime() + DAYS_PER_WEEK * MS_PER_DAY));

    while (current <= end) {
        const isFirstOfMonth = current.getDate() <= 7;
        boundaries.push({
            date: new Date(current),
            label: formatWeekLabel(current),
            isFirst: isFirstOfMonth,
            isMajor: isFirstOfMonth,
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
 * Generates date boundaries for yearly ticks.
 * @param {Date} start - Start date
 * @param {Date} end - End date
 * @returns {Array<{date: Date, label: string, isFirst: boolean}>} Array of boundaries
 */
function generateYearlyBoundaries(start, end) {
    const boundaries = [];
    let current = startOfYear(start);
    current.setFullYear(current.getFullYear() + 1);

    while (current <= end) {
        const isDecade = current.getFullYear() % 10 === 0;
        boundaries.push({
            date: new Date(current),
            label: formatYearLabel(current),
            isFirst: false,
            isMajor: isDecade,
        });
        current.setFullYear(current.getFullYear() + 1);
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
 * @param {Object} boundary - Boundary object with date, label, isMajor
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
    tick.setAttribute('data-date', boundary.date.toISOString());
    // Use data-label for CSS ::after tooltip content
    tick.setAttribute('data-label', formatFullDateLabel(boundary.date));
    tick.setAttribute('title', boundary.label);
    // Use role="img" to allow aria-label on a div (visual timeline marker)
    tick.setAttribute('role', 'img');
    tick.setAttribute('aria-label', `Timeline marker: ${boundary.label}`);

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

    // Determine appropriate interval
    const intervalType = determineInterval(startTimestamp, endTimestamp);
    const config = INTERVAL_CONFIG[intervalType];

    // Generate boundaries
    const boundaries = generateBoundaries(intervalType, startDate, endDate);

    // Check if we have too few or too many ticks
    if (boundaries.length < config.minTicks) {
        // Try a finer granularity
        const finerInterval = getFinerInterval(intervalType);
        if (finerInterval) {
            const finerConfig = INTERVAL_CONFIG[finerInterval];
            const finerBoundaries = generateBoundaries(finerInterval, startDate, endDate);
            if (finerBoundaries.length >= 2) {
                renderTicks(finerBoundaries, finerConfig, startTimestamp, endTimestamp, timelineMarkers);
                return;
            }
        }
    } else if (boundaries.length > config.maxTicks) {
        // Try a coarser granularity
        const coarserInterval = getCoarserInterval(intervalType);
        if (coarserInterval) {
            const coarserConfig = INTERVAL_CONFIG[coarserInterval];
            const coarserBoundaries = generateBoundaries(coarserInterval, startDate, endDate);
            renderTicks(coarserBoundaries, coarserConfig, startTimestamp, endTimestamp, timelineMarkers);
            return;
        }
    }

    renderTicks(boundaries, config, startTimestamp, endTimestamp, timelineMarkers);
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
 * @param {Array} boundaries - Array of boundary objects
 * @param {Object} config - Interval configuration
 * @param {number} startTimestamp - Start timestamp in seconds
 * @param {number} endTimestamp - End timestamp in seconds
 * @param {HTMLElement} container - Container element
 */
function renderTicks(boundaries, config, startTimestamp, endTimestamp, container) {
    // Create document fragment for performance
    const fragment = document.createDocumentFragment();

    // Filter out ticks that would be too close to the edges (within 2%)
    // and calculate positions
    const filteredBoundaries = boundaries
        .map(boundary => {
            const timestampSecs = boundary.date.getTime() / 1000;
            const position = calculatePosition(timestampSecs, startTimestamp, endTimestamp);
            return { ...boundary, position };
        })
        .filter(boundary => boundary.position > 2 && boundary.position < 98);

    // Determine which ticks get inline labels
    const labeledIndices = selectLabeledTicks(filteredBoundaries);

    // Add ticks
    filteredBoundaries.forEach((boundary, index) => {
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

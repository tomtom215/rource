// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - iOS-Style Bottom Sheet
 *
 * A native-feeling bottom sheet with:
 * - Touch gesture handling (swipe to dismiss/expand)
 * - Snap points (hidden, peek, half, full)
 * - Spring-based animations
 * - Momentum-based velocity detection
 * - Backdrop blur and tap-to-dismiss
 *
 * Follows Apple Human Interface Guidelines for bottom sheets.
 */

import { addManagedEventListener } from '../state.js';

// ============================================================================
// Constants
// ============================================================================

/** Snap point positions as viewport height percentages (from bottom) */
const SNAP_POINTS = {
    HIDDEN: 0,      // Fully hidden
    PEEK: 20,       // Just quick actions visible (~20vh) - more useful peek
    HALF: 55,       // Slightly more than half - shows most content
    FULL: 90,       // Nearly full screen (leave room for status bar)
};

/** Minimum velocity (px/ms) to trigger momentum-based snap - lower = more sensitive */
const VELOCITY_THRESHOLD = 0.3;

/** Friction for momentum calculation */
const MOMENTUM_FRICTION = 0.92;

/** Spring animation parameters (iOS-like) */
const SPRING = {
    tension: 280,   // Slightly softer for more natural feel
    friction: 26,
    mass: 1,
};

/** Touch detection thresholds */
const TOUCH = {
    minSwipeDistance: 8,     // Lower threshold for more responsive swipes
    maxTapDuration: 250,     // Slightly longer tap window
    dragThreshold: 3,        // Start drag earlier for responsiveness
};

// ============================================================================
// Bottom Sheet State
// ============================================================================

let sheet = null;
let backdrop = null;
let handle = null;
let content = null;

let currentSnap = 'HIDDEN';
let isDragging = false;
let startY = 0;
let startTranslate = 0;
let currentTranslate = 0;
let lastY = 0;
let lastTime = 0;
let velocity = 0;
let animationFrame = null;

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Converts snap point name to pixel position.
 * @param {string} snapName - Snap point name
 * @returns {number} Position in pixels from bottom
 */
function snapToPixels(snapName) {
    const vh = window.innerHeight;
    const percent = SNAP_POINTS[snapName] || 0;
    return (percent / 100) * vh;
}

/**
 * Gets the current translate Y value from the sheet.
 * @returns {number} Current translateY in pixels
 */
function getCurrentTranslate() {
    if (!sheet) return 0;
    const style = window.getComputedStyle(sheet);
    const matrix = new DOMMatrix(style.transform);
    return matrix.m42; // translateY component
}

/**
 * Calculates the nearest snap point based on position and velocity.
 * Uses iOS-style behavior: fast swipes go to extremes, slow drags snap to nearest.
 * @param {number} position - Current position (vh from bottom)
 * @param {number} velocity - Current velocity (positive = dragging down)
 * @returns {string} Snap point name
 */
function calculateSnapPoint(position, velocity) {
    const vh = window.innerHeight;
    const positionVh = (position / vh) * 100;

    // Fast swipe detection - go to extremes
    const fastSwipeThreshold = 0.6;
    if (Math.abs(velocity) > fastSwipeThreshold) {
        if (velocity > 0) {
            // Fast swipe down - dismiss completely
            return 'HIDDEN';
        } else {
            // Fast swipe up - expand fully
            return 'FULL';
        }
    }

    // Medium velocity - step to next snap point in direction of swipe
    if (Math.abs(velocity) > VELOCITY_THRESHOLD) {
        if (velocity > 0) {
            // Dragging down (dismissing) - step down one level
            if (positionVh > SNAP_POINTS.HALF + 10) return 'HALF';
            if (positionVh > SNAP_POINTS.PEEK + 5) return 'PEEK';
            return 'HIDDEN';
        } else {
            // Dragging up (expanding) - step up one level
            if (positionVh < SNAP_POINTS.PEEK + 10) return 'PEEK';
            if (positionVh < SNAP_POINTS.HALF + 15) return 'HALF';
            return 'FULL';
        }
    }

    // Slow drag or release - find nearest snap point
    const snapValues = Object.entries(SNAP_POINTS);
    let nearest = 'HIDDEN';
    let minDistance = Infinity;

    for (const [name, percent] of snapValues) {
        const distance = Math.abs(positionVh - percent);
        if (distance < minDistance) {
            minDistance = distance;
            nearest = name;
        }
    }

    return nearest;
}

/**
 * iOS-style spring animation.
 * @param {number} from - Start value
 * @param {number} to - End value
 * @param {Function} onUpdate - Called each frame with current value
 * @param {Function} onComplete - Called when animation completes
 */
function springAnimate(from, to, onUpdate, onComplete) {
    let current = from;
    let velocity = 0;
    const { tension, friction, mass } = SPRING;

    function step() {
        // Spring physics
        const displacement = current - to;
        const springForce = -tension * displacement;
        const dampingForce = -friction * velocity;
        const acceleration = (springForce + dampingForce) / mass;

        velocity += acceleration * (1 / 60); // Assuming 60fps
        current += velocity * (1 / 60) * 1000; // Convert to ms

        onUpdate(current);

        // Check if settled
        if (Math.abs(velocity) < 0.01 && Math.abs(displacement) < 0.5) {
            onUpdate(to);
            if (onComplete) onComplete();
            return;
        }

        animationFrame = requestAnimationFrame(step);
    }

    if (animationFrame) {
        cancelAnimationFrame(animationFrame);
    }
    animationFrame = requestAnimationFrame(step);
}

// ============================================================================
// Sheet Manipulation
// ============================================================================

/**
 * Sets the sheet position without animation.
 * @param {number} translateY - Position in pixels (0 = fully visible at snap point)
 */
function setSheetPosition(translateY) {
    if (!sheet) return;
    sheet.style.transform = `translateY(${translateY}px)`;
    currentTranslate = translateY;
}

/**
 * Animates the sheet to a snap point.
 * @param {string} snapName - Target snap point
 * @param {boolean} [instant=false] - Skip animation
 */
function snapTo(snapName, instant = false) {
    if (!sheet) return;

    const targetHeight = snapToPixels(snapName);
    const sheetHeight = sheet.offsetHeight;
    // translateY: positive = moved down, negative = moved up
    // When at FULL, translateY should be minimal
    // When at HIDDEN, translateY should be sheetHeight
    const targetTranslate = sheetHeight - targetHeight;

    currentSnap = snapName;

    // Update backdrop
    if (backdrop) {
        if (snapName === 'HIDDEN') {
            backdrop.classList.remove('visible');
            backdrop.style.pointerEvents = 'none';
        } else {
            backdrop.classList.add('visible');
            backdrop.style.pointerEvents = 'auto';
            // Fade backdrop based on sheet position
            const opacity = Math.min(0.5, (SNAP_POINTS[snapName] / 100) * 0.6);
            backdrop.style.opacity = opacity.toString();
        }
    }

    // Update ARIA
    sheet.setAttribute('aria-hidden', snapName === 'HIDDEN' ? 'true' : 'false');

    if (instant) {
        sheet.style.transition = 'none';
        setSheetPosition(targetTranslate);
        // Force reflow
        void sheet.offsetHeight;
        sheet.style.transition = '';
    } else {
        // Use CSS transition for smooth animation
        sheet.style.transition = 'transform 0.4s cubic-bezier(0.25, 0.46, 0.45, 0.94)';
        setSheetPosition(targetTranslate);
        // Clear transition after animation
        setTimeout(() => {
            if (sheet) sheet.style.transition = '';
        }, 400);
    }

    // Dispatch custom event
    sheet.dispatchEvent(new CustomEvent('snapchange', {
        detail: { snap: snapName }
    }));
}

// ============================================================================
// Touch Event Handlers
// ============================================================================

/**
 * Handles touch start on the drag handle or sheet header.
 * @param {TouchEvent} e
 */
function handleTouchStart(e) {
    if (!sheet) return;

    // Only respond to touches on the handle area
    const touch = e.touches[0];
    const target = e.target;

    // Check if touch is on handle or header area
    const isHandle = handle && (target === handle || handle.contains(target));
    const isHeader = target.closest('.bottom-sheet-header');

    if (!isHandle && !isHeader) return;

    isDragging = true;
    startY = touch.clientY;
    startTranslate = getCurrentTranslate();
    lastY = startY;
    lastTime = Date.now();
    velocity = 0;

    // Disable transition during drag
    sheet.style.transition = 'none';

    // Prevent scrolling while dragging
    e.preventDefault();
}

/**
 * Handles touch move during drag.
 * @param {TouchEvent} e
 */
function handleTouchMove(e) {
    if (!isDragging || !sheet) return;

    const touch = e.touches[0];
    const deltaY = touch.clientY - startY;
    const now = Date.now();
    const dt = now - lastTime;

    // Calculate velocity (pixels per millisecond)
    if (dt > 0) {
        velocity = (touch.clientY - lastY) / dt;
    }

    lastY = touch.clientY;
    lastTime = now;

    // Calculate new position with bounds
    let newTranslate = startTranslate + deltaY;
    const sheetHeight = sheet.offsetHeight;

    // Apply rubber-band effect at bounds
    const minTranslate = sheetHeight - snapToPixels('FULL');
    const maxTranslate = sheetHeight; // Fully hidden

    if (newTranslate < minTranslate) {
        // Rubber-band at top (trying to drag above FULL)
        const overflow = minTranslate - newTranslate;
        newTranslate = minTranslate - Math.sqrt(overflow) * 3;
    } else if (newTranslate > maxTranslate) {
        // Rubber-band at bottom (dragging below HIDDEN)
        const overflow = newTranslate - maxTranslate;
        newTranslate = maxTranslate + Math.sqrt(overflow) * 3;
    }

    setSheetPosition(newTranslate);

    // Update backdrop opacity during drag
    if (backdrop) {
        const sheetHeight = sheet.offsetHeight;
        const visibleHeight = sheetHeight - newTranslate;
        const visiblePercent = (visibleHeight / window.innerHeight) * 100;
        const opacity = Math.min(0.5, Math.max(0, visiblePercent / 100 * 0.6));
        backdrop.style.opacity = opacity.toString();
        if (opacity > 0.05) {
            backdrop.classList.add('visible');
        }
    }

    e.preventDefault();
}

/**
 * Handles touch end - snap to nearest point.
 * @param {TouchEvent} e
 */
function handleTouchEnd(e) {
    if (!isDragging || !sheet) return;

    isDragging = false;

    // Calculate current position as height from bottom
    const sheetHeight = sheet.offsetHeight;
    const currentHeight = sheetHeight - currentTranslate;

    // Determine snap point based on position and velocity
    const snapPoint = calculateSnapPoint(currentHeight, velocity);

    // Snap with animation
    snapTo(snapPoint);
}

/**
 * Handles backdrop tap to dismiss.
 * @param {Event} e
 */
function handleBackdropTap(e) {
    if (e.target === backdrop) {
        snapTo('HIDDEN');
    }
}

// ============================================================================
// Public API
// ============================================================================

/**
 * Checks if the device should use the bottom sheet (mobile/tablet).
 * @returns {boolean}
 */
function isMobileDevice() {
    return window.innerWidth <= 768;
}

/**
 * Initializes the bottom sheet with gesture handling.
 * Call this after DOM is ready.
 */
export function initBottomSheet() {
    sheet = document.getElementById('bottom-sheet');
    backdrop = document.getElementById('bottom-sheet-backdrop');
    handle = document.querySelector('.bottom-sheet-handle');
    content = document.querySelector('.bottom-sheet-content');

    if (!sheet) {
        console.warn('Bottom sheet element not found');
        return;
    }

    // Add has-bottom-sheet class to body on mobile to enable CSS rules
    // that hide the old sidebar toggle and show the bottom sheet
    updateBottomSheetMode();
    window.addEventListener('resize', updateBottomSheetMode);

    // Set initial state
    snapTo('HIDDEN', true);

    // Touch events on the sheet (handle area)
    addManagedEventListener(sheet, 'touchstart', handleTouchStart, { passive: false });
    addManagedEventListener(sheet, 'touchmove', handleTouchMove, { passive: false });
    addManagedEventListener(sheet, 'touchend', handleTouchEnd);
    addManagedEventListener(sheet, 'touchcancel', handleTouchEnd);

    // Backdrop tap
    if (backdrop) {
        addManagedEventListener(backdrop, 'click', handleBackdropTap);
    }

    // Close button
    const closeBtn = document.getElementById('bottom-sheet-close');
    if (closeBtn) {
        addManagedEventListener(closeBtn, 'click', () => snapTo('HIDDEN'));
    }

    // Handle resize
    addManagedEventListener(window, 'resize', () => {
        // Re-snap to current position on resize
        snapTo(currentSnap, true);
    });

    console.log('Bottom sheet initialized');
}

/**
 * Updates the bottom sheet mode based on screen size.
 * Adds/removes has-bottom-sheet class on body.
 */
function updateBottomSheetMode() {
    if (isMobileDevice()) {
        document.body.classList.add('has-bottom-sheet');
    } else {
        document.body.classList.remove('has-bottom-sheet');
    }
}

/**
 * Opens the bottom sheet to a specific snap point.
 * @param {string} [snap='HALF'] - Snap point: 'PEEK', 'HALF', or 'FULL'
 */
export function openBottomSheet(snap = 'HALF') {
    if (!sheet) {
        initBottomSheet();
    }
    snapTo(snap);
}

/**
 * Closes the bottom sheet.
 */
export function closeBottomSheet() {
    snapTo('HIDDEN');
}

/**
 * Toggles the bottom sheet between hidden and half.
 */
export function toggleBottomSheet() {
    if (currentSnap === 'HIDDEN') {
        snapTo('HALF');
    } else {
        snapTo('HIDDEN');
    }
}

/**
 * Gets the current snap point.
 * @returns {string} Current snap point name
 */
export function getCurrentSnap() {
    return currentSnap;
}

/**
 * Checks if the bottom sheet is open (not hidden).
 * @returns {boolean}
 */
export function isBottomSheetOpen() {
    return currentSnap !== 'HIDDEN';
}

// ============================================================================
// Bottom Sheet Legends Population
// ============================================================================

/**
 * Updates the file types legend in the bottom sheet.
 * Called when legend data changes.
 * @param {Array<{extension: string, color: string, count: number}>} fileTypes
 */
export function updateBottomSheetFileTypes(fileTypes) {
    const container = document.getElementById('bs-file-types-items');
    const section = document.getElementById('bs-legends-section');

    if (!container) return;

    // Show the legends section if we have data
    if (fileTypes && fileTypes.length > 0 && section) {
        section.classList.remove('hidden');
    }

    // Clear existing items
    container.innerHTML = '';

    if (!fileTypes || fileTypes.length === 0) {
        container.innerHTML = '<span class="bottom-sheet-legend-empty">No files yet</span>';
        return;
    }

    // Add legend items (limit to top 10 for mobile)
    const topTypes = fileTypes.slice(0, 10);
    for (const item of topTypes) {
        const el = document.createElement('div');
        el.className = 'bottom-sheet-legend-item';
        el.innerHTML = `
            <span class="bottom-sheet-legend-color" style="background: ${item.color}"></span>
            <span class="bottom-sheet-legend-ext">.${item.extension}</span>
            <span class="bottom-sheet-legend-count">${item.count}</span>
        `;
        container.appendChild(el);
    }

    // Show "and X more" if truncated
    if (fileTypes.length > 10) {
        const more = document.createElement('span');
        more.className = 'bottom-sheet-legend-more';
        more.textContent = `+${fileTypes.length - 10} more`;
        more.style.cssText = 'font-size: 0.6875rem; color: var(--text-muted); padding: 4px 8px;';
        container.appendChild(more);
    }
}

/**
 * Updates the authors legend in the bottom sheet.
 * Called when authors data changes.
 * @param {Array<{name: string, color: string, commits: number}>} authors
 */
export function updateBottomSheetAuthors(authors) {
    const container = document.getElementById('bs-authors-items');
    const section = document.getElementById('bs-legends-section');

    if (!container) return;

    // Show the legends section if we have data
    if (authors && authors.length > 0 && section) {
        section.classList.remove('hidden');
    }

    // Clear existing items
    container.innerHTML = '';

    if (!authors || authors.length === 0) {
        container.innerHTML = '<span class="bottom-sheet-legend-empty">No authors yet</span>';
        return;
    }

    // Add author items (limit to top 8 for mobile)
    const topAuthors = authors.slice(0, 8);
    for (const author of topAuthors) {
        const el = document.createElement('div');
        el.className = 'bottom-sheet-author-item';
        el.innerHTML = `
            <span class="bottom-sheet-author-color" style="background: ${author.color}"></span>
            <span class="bottom-sheet-author-name">${escapeHtml(author.name)}</span>
            <span class="bottom-sheet-author-commits">${author.commits}</span>
        `;
        container.appendChild(el);
    }

    // Show "and X more" if truncated
    if (authors.length > 8) {
        const more = document.createElement('span');
        more.className = 'bottom-sheet-legend-more';
        more.textContent = `+${authors.length - 8} more`;
        more.style.cssText = 'font-size: 0.6875rem; color: var(--text-muted); padding: 6px 10px;';
        container.appendChild(more);
    }
}

/**
 * Clears the bottom sheet legends (when resetting).
 */
export function clearBottomSheetLegends() {
    const fileTypesContainer = document.getElementById('bs-file-types-items');
    const authorsContainer = document.getElementById('bs-authors-items');
    const section = document.getElementById('bs-legends-section');

    if (fileTypesContainer) fileTypesContainer.innerHTML = '';
    if (authorsContainer) authorsContainer.innerHTML = '';
    if (section) section.classList.add('hidden');
}

/**
 * Simple HTML escape for user content.
 * @param {string} str
 * @returns {string}
 */
function escapeHtml(str) {
    const div = document.createElement('div');
    div.textContent = str;
    return div.innerHTML;
}

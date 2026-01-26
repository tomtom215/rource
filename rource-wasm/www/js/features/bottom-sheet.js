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
import { hapticLight, hapticMedium, HapticPattern, haptic } from '../utils.js';

// ============================================================================
// Constants
// ============================================================================

/** Snap point positions as viewport height percentages (from bottom) */
// L2 FIX: Reduced PEEK (20→15) and HALF (55→40) to give 15% more visualization space
const SNAP_POINTS = {
    HIDDEN: 0,      // Fully hidden
    PEEK: 15,       // Just header + quick actions visible (~15vh = ~120px on typical mobile)
    HALF: 40,       // 40% of screen - shows content without overwhelming visualization
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
let dragStartedInContent = false;
let hasDraggedEnough = false;

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
    // L2 FIX: Adjusted thresholds for new snap points (PEEK=15, HALF=40)
    if (Math.abs(velocity) > VELOCITY_THRESHOLD) {
        if (velocity > 0) {
            // Dragging down (dismissing) - step down one level
            if (positionVh > SNAP_POINTS.HALF + 10) return 'HALF';
            if (positionVh > SNAP_POINTS.PEEK + 3) return 'PEEK';
            return 'HIDDEN';
        } else {
            // Dragging up (expanding) - step up one level
            if (positionVh < SNAP_POINTS.PEEK + 8) return 'PEEK';
            if (positionVh < SNAP_POINTS.HALF + 12) return 'HALF';
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

    // Haptic feedback on snap (if position actually changed)
    if (currentSnap !== snapName && !instant) {
        // Stronger feedback for dismissal, lighter for expansion
        if (snapName === 'HIDDEN') {
            hapticMedium(); // Dismissal confirmation
        } else {
            hapticLight(); // Light snap feedback
        }
    }

    currentSnap = snapName;

    // Update backdrop
    // L10 fix: At PEEK position, allow touches to pass through to canvas
    // This lets users interact with the visualization while quick actions are visible
    if (backdrop) {
        if (snapName === 'HIDDEN') {
            backdrop.classList.remove('visible');
            backdrop.style.pointerEvents = 'none';
        } else if (snapName === 'PEEK') {
            // At PEEK, show subtle backdrop but allow touch pass-through to canvas
            backdrop.classList.add('visible');
            backdrop.style.pointerEvents = 'none';
            backdrop.style.opacity = '0.15'; // Very subtle
        } else {
            // At HALF or FULL, normal backdrop behavior (tap to dismiss)
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
 * Checks if the content is scrolled to the top.
 * @returns {boolean} True if content is at the top
 */
function isContentAtTop() {
    return !content || content.scrollTop <= 0;
}

/**
 * Handles touch start on the drag handle, header, or content (when at top).
 * @param {TouchEvent} e
 */
function handleTouchStart(e) {
    if (!sheet) return;

    const touch = e.touches[0];
    const target = e.target;

    // Check if touch is on handle or header area (always draggable)
    const isHandle = handle && (target === handle || handle.contains(target));
    const isHeader = target.closest('.bottom-sheet-header');

    // Check if touch is on content area AND content is scrolled to top
    // This allows swiping down to dismiss when at the top of content
    const isContent = content && content.contains(target);
    const canDragFromContent = isContent && isContentAtTop();

    // Store whether we started in content area for move handling
    dragStartedInContent = isContent && !isHandle && !isHeader;

    if (!isHandle && !isHeader && !canDragFromContent) {
        // Not on a draggable area - let content scroll normally
        return;
    }

    isDragging = true;
    startY = touch.clientY;
    startTranslate = getCurrentTranslate();
    lastY = startY;
    lastTime = Date.now();
    velocity = 0;

    // Disable transition during drag
    sheet.style.transition = 'none';

    // Only prevent default on handle/header, not content
    // This allows content scrolling to work until we confirm it's a drag
    if (isHandle || isHeader) {
        e.preventDefault();
    }
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

    // If drag started in content area, apply special handling
    if (dragStartedInContent && !hasDraggedEnough) {
        // Check if we've moved enough to determine intent
        if (Math.abs(deltaY) < TOUCH.minSwipeDistance) {
            // Not enough movement yet - don't prevent default, let content scroll
            return;
        }

        // User is dragging UP (negative delta) - they want to scroll content, not move sheet
        if (deltaY < 0) {
            isDragging = false;
            return;
        }

        // User is dragging DOWN (positive delta) - check if content is at top
        if (!isContentAtTop()) {
            // Content has scroll position - let it scroll
            isDragging = false;
            return;
        }

        // Content is at top and user is dragging down - take over the drag
        hasDraggedEnough = true;
    }

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
    // L10: Adjust opacity and pointer-events based on drag position
    if (backdrop) {
        const sheetHeight = sheet.offsetHeight;
        const visibleHeight = sheetHeight - newTranslate;
        const visiblePercent = (visibleHeight / window.innerHeight) * 100;

        // At low visibility (PEEK level ~20%), use subtle backdrop with pass-through
        if (visiblePercent <= SNAP_POINTS.PEEK + 5) {
            const opacity = Math.min(0.15, Math.max(0, visiblePercent / 100 * 0.6));
            backdrop.style.opacity = opacity.toString();
            backdrop.style.pointerEvents = 'none';
        } else {
            // At higher visibility, normal backdrop behavior
            const opacity = Math.min(0.5, Math.max(0, visiblePercent / 100 * 0.6));
            backdrop.style.opacity = opacity.toString();
            backdrop.style.pointerEvents = 'auto';
        }

        if (visiblePercent > 5) {
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
    // Reset content drag tracking
    dragStartedInContent = false;
    hasDraggedEnough = false;

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
 * Detects mobile by checking:
 * - Portrait mode: width <= 768px
 * - Landscape mode: height <= 500px (typical landscape phone height)
 * - Touch capability as additional signal
 * @returns {boolean}
 */
function isMobileDevice() {
    const width = window.innerWidth;
    const height = window.innerHeight;
    const isPortraitMobile = width <= 768;
    const isLandscapeMobile = height <= 500 && width <= 1024;
    const hasTouch = 'ontouchstart' in window || navigator.maxTouchPoints > 0;

    // Mobile if portrait width is small OR landscape height is small (with touch)
    return isPortraitMobile || (isLandscapeMobile && hasTouch);
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

    // Handle orientation changes specifically (more reliable than resize on mobile)
    if (window.screen && window.screen.orientation) {
        window.screen.orientation.addEventListener('change', () => {
            // Small delay to let the viewport update
            setTimeout(updateBottomSheetMode, 100);
        });
    } else {
        // Fallback for older browsers
        window.addEventListener('orientationchange', () => {
            setTimeout(updateBottomSheetMode, 100);
        });
    }

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
 * Checks if the device is in landscape mobile mode.
 * @returns {boolean}
 */
function isLandscapeMobile() {
    const width = window.innerWidth;
    const height = window.innerHeight;
    const isLandscape = width > height;
    const hasTouch = 'ontouchstart' in window || navigator.maxTouchPoints > 0;

    // Landscape mobile: landscape orientation, height <= 500px (typical phone landscape), touch capable
    return isLandscape && height <= 500 && width <= 1024 && hasTouch;
}

/**
 * Updates the bottom sheet mode based on screen size.
 * Adds/removes has-bottom-sheet and landscape classes on body.
 */
function updateBottomSheetMode() {
    const isMobile = isMobileDevice();
    const isLandscape = isLandscapeMobile();

    if (isMobile) {
        document.body.classList.add('has-bottom-sheet');
    } else {
        document.body.classList.remove('has-bottom-sheet');
    }

    // Add/remove landscape class for CSS targeting
    if (isLandscape) {
        document.body.classList.add('landscape-mobile');
    } else {
        document.body.classList.remove('landscape-mobile');
    }

    // If we're open and orientation changed, re-snap to current position
    if (sheet && currentSnap !== 'HIDDEN') {
        snapTo(currentSnap, true);
    }
}

/**
 * Opens the bottom sheet to a specific snap point.
 * L2 FIX: Default changed from HALF to PEEK for better initial experience.
 * @param {string} [snap='PEEK'] - Snap point: 'PEEK', 'HALF', or 'FULL'
 */
export function openBottomSheet(snap = 'PEEK') {
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
 * Toggles the bottom sheet between hidden and peek.
 * L2 FIX: Opens to PEEK instead of HALF for better initial experience.
 * User can swipe up to HALF or FULL for more content.
 */
export function toggleBottomSheet() {
    hapticMedium(); // FAB tap feedback
    if (currentSnap === 'HIDDEN') {
        // L2: Open to PEEK initially - shows quick actions without overwhelming
        // visualization. User can swipe up to expand.
        snapTo('PEEK');
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

/** Default collapsed limits for legends */
const LEGEND_LIMITS = {
    FILE_TYPES: 6,
    AUTHORS: 5,
};

/** Expanded states for legends */
let fileTypesExpanded = false;
let authorsExpanded = false;

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

    // Store full data for expansion toggle
    container.dataset.fullCount = fileTypes.length.toString();

    // Determine how many to show
    const limit = fileTypesExpanded ? fileTypes.length : LEGEND_LIMITS.FILE_TYPES;
    const visibleTypes = fileTypes.slice(0, limit);
    const remaining = fileTypes.length - visibleTypes.length;

    // Add legend items
    for (const item of visibleTypes) {
        const el = document.createElement('div');
        el.className = 'bottom-sheet-legend-item';
        el.innerHTML = `
            <span class="bottom-sheet-legend-color" style="background: ${item.color}"></span>
            <span class="bottom-sheet-legend-ext">.${item.extension}</span>
            <span class="bottom-sheet-legend-count">${item.count}</span>
        `;
        container.appendChild(el);
    }

    // Show expand/collapse button if there are more items
    if (fileTypes.length > LEGEND_LIMITS.FILE_TYPES) {
        const toggleBtn = document.createElement('button');
        toggleBtn.className = 'bottom-sheet-legend-toggle';
        toggleBtn.type = 'button';
        toggleBtn.setAttribute('aria-expanded', fileTypesExpanded.toString());

        if (fileTypesExpanded) {
            toggleBtn.innerHTML = `
                <svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M7.41 15.41L12 10.83l4.59 4.58L18 14l-6-6-6 6z"/>
                </svg>
                Show less
            `;
        } else {
            toggleBtn.innerHTML = `
                <svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M7.41 8.59L12 13.17l4.59-4.58L18 10l-6 6-6-6z"/>
                </svg>
                +${remaining} more
            `;
        }

        toggleBtn.addEventListener('click', () => {
            fileTypesExpanded = !fileTypesExpanded;
            updateBottomSheetFileTypes(fileTypes);
        });

        container.appendChild(toggleBtn);
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

    // Store full data for expansion toggle
    container.dataset.fullCount = authors.length.toString();

    // Determine how many to show
    const limit = authorsExpanded ? authors.length : LEGEND_LIMITS.AUTHORS;
    const visibleAuthors = authors.slice(0, limit);
    const remaining = authors.length - visibleAuthors.length;

    // Add author items
    for (const author of visibleAuthors) {
        const el = document.createElement('div');
        el.className = 'bottom-sheet-author-item';
        el.innerHTML = `
            <span class="bottom-sheet-author-color" style="background: ${author.color}"></span>
            <span class="bottom-sheet-author-name">${escapeHtml(author.name)}</span>
            <span class="bottom-sheet-author-commits">${author.commits}</span>
        `;
        container.appendChild(el);
    }

    // Show expand/collapse button if there are more items
    if (authors.length > LEGEND_LIMITS.AUTHORS) {
        const toggleBtn = document.createElement('button');
        toggleBtn.className = 'bottom-sheet-legend-toggle';
        toggleBtn.type = 'button';
        toggleBtn.setAttribute('aria-expanded', authorsExpanded.toString());

        if (authorsExpanded) {
            toggleBtn.innerHTML = `
                <svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M7.41 15.41L12 10.83l4.59 4.58L18 14l-6-6-6 6z"/>
                </svg>
                Show less
            `;
        } else {
            toggleBtn.innerHTML = `
                <svg width="12" height="12" viewBox="0 0 24 24" fill="currentColor">
                    <path d="M7.41 8.59L12 13.17l4.59-4.58L18 10l-6 6-6-6z"/>
                </svg>
                +${remaining} more
            `;
        }

        toggleBtn.addEventListener('click', () => {
            authorsExpanded = !authorsExpanded;
            updateBottomSheetAuthors(authors);
        });

        container.appendChild(toggleBtn);
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

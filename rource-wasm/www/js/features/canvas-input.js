// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

/**
 * Rource - Canvas Input Handling
 *
 * Handles mouse, touch, and wheel events on the visualization canvas.
 * Single responsibility: user input for camera panning, zooming, and entity dragging.
 */

import { getRource, addManagedEventListener } from '../state.js';
import { safeWasmCall, safeWasmVoid } from '../wasm-api.js';
import { getElement } from '../dom.js';

/**
 * Touch state for pinch-to-zoom.
 */
let touchStartDist = 0;
let lastTouchX = 0;
let lastTouchY = 0;

/**
 * Converts client coordinates to canvas-relative coordinates.
 * @param {HTMLCanvasElement} canvas - The canvas element
 * @param {number} clientX - Client X coordinate
 * @param {number} clientY - Client Y coordinate
 * @returns {{x: number, y: number}} Canvas-relative coordinates
 */
function getCanvasCoords(canvas, clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    return {
        x: clientX - rect.left,
        y: clientY - rect.top
    };
}

/**
 * Handles mouse down event.
 * @param {MouseEvent} e - Mouse event
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleMouseDown(e, canvas) {
    const rource = getRource();
    if (!rource) return;

    const { x, y } = getCanvasCoords(canvas, e.clientX, e.clientY);
    safeWasmVoid('onMouseDown', () => rource.onMouseDown(x, y));
    canvas.style.cursor = 'grabbing';
}

/**
 * Handles mouse move event.
 * @param {MouseEvent} e - Mouse event
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleMouseMove(e, canvas) {
    const rource = getRource();
    if (!rource) return;

    const { x, y } = getCanvasCoords(canvas, e.clientX, e.clientY);
    safeWasmVoid('onMouseMove', () => rource.onMouseMove(x, y));
}

/**
 * Handles mouse up event.
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleMouseUp(canvas) {
    const rource = getRource();
    if (!rource) return;

    safeWasmVoid('onMouseUp', () => rource.onMouseUp());
    canvas.style.cursor = 'grab';
}

/**
 * Handles mouse leave event.
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleMouseLeave(canvas) {
    const rource = getRource();
    if (!rource) return;

    safeWasmVoid('onMouseUp', () => rource.onMouseUp());
    canvas.style.cursor = 'grab';
}

/**
 * Handles wheel event for zooming.
 * @param {WheelEvent} e - Wheel event
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleWheel(e, canvas) {
    const rource = getRource();
    if (!rource) return;

    e.preventDefault();
    const { x, y } = getCanvasCoords(canvas, e.clientX, e.clientY);
    safeWasmVoid('onWheel', () => rource.onWheel(e.deltaY, x, y));
}

/**
 * Handles touch start event.
 * @param {TouchEvent} e - Touch event
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleTouchStart(e, canvas) {
    const rource = getRource();
    if (!rource) return;

    if (e.touches.length === 1) {
        const { x, y } = getCanvasCoords(canvas, e.touches[0].clientX, e.touches[0].clientY);
        lastTouchX = x;
        lastTouchY = y;
        safeWasmVoid('onMouseDown', () => rource.onMouseDown(x, y));
    } else if (e.touches.length === 2) {
        touchStartDist = Math.hypot(
            e.touches[0].clientX - e.touches[1].clientX,
            e.touches[0].clientY - e.touches[1].clientY
        );
    }
}

/**
 * Handles touch move event.
 * @param {TouchEvent} e - Touch event
 * @param {HTMLCanvasElement} canvas - Canvas element
 */
function handleTouchMove(e, canvas) {
    const rource = getRource();
    if (!rource) return;

    e.preventDefault();

    if (e.touches.length === 1) {
        const { x, y } = getCanvasCoords(canvas, e.touches[0].clientX, e.touches[0].clientY);
        safeWasmVoid('onMouseMove', () => rource.onMouseMove(x, y));
        lastTouchX = x;
        lastTouchY = y;
    } else if (e.touches.length === 2) {
        const dist = Math.hypot(
            e.touches[0].clientX - e.touches[1].clientX,
            e.touches[0].clientY - e.touches[1].clientY
        );
        if (touchStartDist > 0) {
            const factor = dist / touchStartDist;
            safeWasmCall('zoom', () => rource.zoom(factor), undefined);
            touchStartDist = dist;
        }
    }
}

/**
 * Handles touch end event.
 */
function handleTouchEnd() {
    const rource = getRource();
    if (!rource) return;

    safeWasmVoid('onMouseUp', () => rource.onMouseUp());
    touchStartDist = 0;
}

/**
 * Initializes canvas input event listeners.
 */
export function initCanvasInput() {
    const canvas = getElement('canvas');
    if (!canvas) return;

    // Mouse events
    addManagedEventListener(canvas, 'mousedown', (e) => handleMouseDown(e, canvas));
    addManagedEventListener(canvas, 'mousemove', (e) => handleMouseMove(e, canvas));
    addManagedEventListener(canvas, 'mouseup', () => handleMouseUp(canvas));
    addManagedEventListener(canvas, 'mouseleave', () => handleMouseLeave(canvas));

    // Wheel events for zooming
    addManagedEventListener(canvas, 'wheel', (e) => handleWheel(e, canvas), { passive: false });

    // Touch events for mobile
    addManagedEventListener(canvas, 'touchstart', (e) => handleTouchStart(e, canvas));
    addManagedEventListener(canvas, 'touchmove', (e) => handleTouchMove(e, canvas), { passive: false });
    addManagedEventListener(canvas, 'touchend', handleTouchEnd);

    // Set default cursor
    canvas.style.cursor = 'grab';
}

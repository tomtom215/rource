/**
 * DOM Event Simulator for Chaos Testing
 *
 * Provides utilities for simulating DOM events in tests.
 */

/**
 * Simulate a mouse click at coordinates
 */
export function simulateClick(element, x, y, options = {}) {
    const event = new MouseEvent('click', {
        bubbles: true,
        cancelable: true,
        clientX: x,
        clientY: y,
        button: options.button || 0,
        shiftKey: options.shiftKey || false,
        ctrlKey: options.ctrlKey || false,
        altKey: options.altKey || false,
        metaKey: options.metaKey || false,
    });
    element.dispatchEvent(event);
}

/**
 * Simulate a mouse drag
 */
export async function simulateDrag(element, startX, startY, endX, endY, steps = 10) {
    // Mouse down
    element.dispatchEvent(new MouseEvent('mousedown', {
        bubbles: true,
        clientX: startX,
        clientY: startY,
    }));

    // Mouse move in steps
    for (let i = 1; i <= steps; i++) {
        const x = startX + (endX - startX) * (i / steps);
        const y = startY + (endY - startY) * (i / steps);

        element.dispatchEvent(new MouseEvent('mousemove', {
            bubbles: true,
            clientX: x,
            clientY: y,
        }));

        await new Promise(resolve => setTimeout(resolve, 10));
    }

    // Mouse up
    element.dispatchEvent(new MouseEvent('mouseup', {
        bubbles: true,
        clientX: endX,
        clientY: endY,
    }));
}

/**
 * Simulate a wheel event
 */
export function simulateWheel(element, deltaX, deltaY, x, y) {
    const event = new WheelEvent('wheel', {
        bubbles: true,
        cancelable: true,
        deltaX,
        deltaY,
        deltaMode: 0,
        clientX: x,
        clientY: y,
    });
    element.dispatchEvent(event);
}

/**
 * Simulate a key press
 */
export function simulateKeyPress(element, key, options = {}) {
    const keydownEvent = new KeyboardEvent('keydown', {
        bubbles: true,
        cancelable: true,
        key,
        code: options.code || key,
        shiftKey: options.shiftKey || false,
        ctrlKey: options.ctrlKey || false,
        altKey: options.altKey || false,
        metaKey: options.metaKey || false,
    });

    const keyupEvent = new KeyboardEvent('keyup', {
        bubbles: true,
        cancelable: true,
        key,
        code: options.code || key,
    });

    element.dispatchEvent(keydownEvent);
    element.dispatchEvent(keyupEvent);
}

/**
 * Simulate a touch event
 */
export function simulateTouch(element, type, touches) {
    const touchList = touches.map((t, i) => ({
        identifier: i,
        clientX: t.x,
        clientY: t.y,
        target: element,
    }));

    const event = new TouchEvent(type, {
        bubbles: true,
        cancelable: true,
        touches: touchList,
        targetTouches: touchList,
        changedTouches: touchList,
    });

    element.dispatchEvent(event);
}

/**
 * Simulate a pinch zoom gesture
 */
export async function simulatePinchZoom(element, centerX, centerY, startDistance, endDistance, steps = 10) {
    const halfStart = startDistance / 2;
    const halfEnd = endDistance / 2;

    // Touch start with two fingers
    simulateTouch(element, 'touchstart', [
        { x: centerX - halfStart, y: centerY },
        { x: centerX + halfStart, y: centerY },
    ]);

    // Move fingers apart/together
    for (let i = 1; i <= steps; i++) {
        const half = halfStart + (halfEnd - halfStart) * (i / steps);
        simulateTouch(element, 'touchmove', [
            { x: centerX - half, y: centerY },
            { x: centerX + half, y: centerY },
        ]);
        await new Promise(resolve => setTimeout(resolve, 10));
    }

    // Touch end
    simulateTouch(element, 'touchend', []);
}

/**
 * Simulate window resize
 */
export function simulateResize(width, height) {
    // Note: Actually resizing the window is not possible in most environments
    // This dispatches the resize event
    window.dispatchEvent(new Event('resize'));
}

/**
 * Simulate focus/blur
 */
export function simulateFocus(element) {
    element.dispatchEvent(new FocusEvent('focus'));
}

export function simulateBlur(element) {
    element.dispatchEvent(new FocusEvent('blur'));
}

/**
 * Wait for next animation frame
 */
export function nextFrame() {
    return new Promise(resolve => requestAnimationFrame(resolve));
}

/**
 * Wait for multiple animation frames
 */
export async function waitFrames(count) {
    for (let i = 0; i < count; i++) {
        await nextFrame();
    }
}

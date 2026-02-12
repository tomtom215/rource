#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Tom F <https://github.com/tomtom215>

"""
JavaScript Import/Export Validator

Validates that all JavaScript imports reference actual exports.
This catches errors like:
    import { set } from './state.js'  // ERROR: 'set' not exported

For Expert+ CI: Catches module resolution errors before deployment

Usage: python3 scripts/validate-js-imports.py [directory]
Default directory: rource-wasm/www/js
"""

import os
import re
import sys
from pathlib import Path
from typing import Dict, Set, List, Tuple

# Regex patterns for extracting exports and imports
EXPORT_FUNCTION_RE = re.compile(r'export\s+(?:async\s+)?(?:function|const|let|var|class)\s+([a-zA-Z_][a-zA-Z0-9_]*)')
# Match export { ... } and export { ... } from '...' (re-exports)
EXPORT_BRACES_RE = re.compile(r'export\s*\{([^}]+)\}(?:\s*from\s*[\'"][^"\']+[\'"])?')
IMPORT_RE = re.compile(r'import\s*\{([^}]+)\}\s*from\s*[\'"]([^"\']+)[\'"]')

def extract_exports(content: str) -> Set[str]:
    """Extract all named exports from JavaScript content."""
    exports = set()

    # export function foo, export const bar, etc.
    for match in EXPORT_FUNCTION_RE.finditer(content):
        exports.add(match.group(1))

    # export { foo, bar, baz as qux } and export { ... } from '...'
    for match in EXPORT_BRACES_RE.finditer(content):
        block = match.group(1)
        # Remove single-line comments from the export block
        block = re.sub(r'//[^\n]*', '', block)
        names = block.split(',')
        for name in names:
            name = name.strip()
            # Skip empty or comment-only entries
            if not name or name.startswith('//'):
                continue
            # Handle 'foo as bar' - we want 'foo' (the original name being exported)
            if ' as ' in name:
                name = name.split(' as ')[0].strip()
            # Final validation - must be a valid identifier
            if name and re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*$', name):
                exports.add(name)

    return exports

def extract_imports(content: str) -> List[Tuple[int, str, List[str]]]:
    """Extract all named imports from JavaScript content.

    Returns: List of (line_number, source_path, [imported_names])
    """
    imports = []

    for i, line in enumerate(content.split('\n'), 1):
        for match in IMPORT_RE.finditer(line):
            names_str = match.group(1)
            source_path = match.group(2)

            names = []
            for name in names_str.split(','):
                name = name.strip()
                # Handle 'foo as bar' - we want 'foo' (what we're importing)
                if ' as ' in name:
                    name = name.split(' as ')[0].strip()
                if name:
                    names.append(name)

            if names:
                imports.append((i, source_path, names))

    return imports

def resolve_path(current_file: Path, import_path: str, js_dir: Path) -> Path:
    """Resolve a relative import path to an absolute path."""
    if import_path.startswith('./') or import_path.startswith('../'):
        return (current_file.parent / import_path).resolve()
    # Assume it's relative to js_dir for non-relative imports
    return (js_dir / import_path).resolve()

def validate_imports(js_dir: Path) -> int:
    """Validate all imports in JavaScript files.

    Returns: Number of errors found
    """
    js_dir = js_dir.resolve()

    # Step 1: Build export catalog
    print("Building export catalog...")
    exports_by_file: Dict[Path, Set[str]] = {}

    for js_file in js_dir.rglob('*.js'):
        try:
            content = js_file.read_text(encoding='utf-8')
            exports = extract_exports(content)
            exports_by_file[js_file.resolve()] = exports
        except Exception as e:
            print(f"  Warning: Could not read {js_file}: {e}")

    total_exports = sum(len(e) for e in exports_by_file.values())
    print(f"  Found {total_exports} exports across {len(exports_by_file)} files")
    print()

    # Step 2: Validate imports
    print("Validating imports...")
    errors = []

    for js_file in js_dir.rglob('*.js'):
        try:
            content = js_file.read_text(encoding='utf-8')
            imports = extract_imports(content)

            for line_num, source_path, names in imports:
                resolved_source = resolve_path(js_file, source_path, js_dir)

                # Skip imports from outside the scanned directory (e.g. ../pkg/ WASM bindings)
                try:
                    resolved_source.relative_to(js_dir)
                except ValueError:
                    continue

                # Get exports from source file
                source_exports = exports_by_file.get(resolved_source, set())

                # Check each imported name
                for name in names:
                    if name not in source_exports:
                        errors.append({
                            'file': str(js_file.relative_to(js_dir.parent.parent)),
                            'line': line_num,
                            'import': name,
                            'source': source_path,
                            'available': sorted(source_exports) if source_exports else ['(file not found or no exports)']
                        })
        except Exception as e:
            print(f"  Warning: Could not process {js_file}: {e}")

    # Step 3: Report results
    print()
    if errors:
        print("=" * 60)
        print(f"ERRORS FOUND: {len(errors)}")
        print("=" * 60)
        print()

        for err in errors:
            print(f"ERROR: {err['file']}:{err['line']}")
            print(f"  Import '{err['import']}' from '{err['source']}'")
            print(f"  Available exports: {', '.join(err['available'][:10])}")
            if len(err['available']) > 10:
                print(f"    ... and {len(err['available']) - 10} more")
            print()

        print("=" * 60)
        print(f"FAILED: {len(errors)} import error(s) found")
        print("Fix these issues before committing to prevent production breakage.")
        print("=" * 60)
        return len(errors)
    else:
        print("=" * 60)
        print("PASSED: All imports validated successfully")
        print("=" * 60)
        return 0

def main():
    js_dir = Path(sys.argv[1] if len(sys.argv) > 1 else 'rource-wasm/www/js')

    if not js_dir.exists():
        print(f"Error: Directory not found: {js_dir}")
        sys.exit(1)

    print("=== JavaScript Import/Export Validation ===")
    print(f"Directory: {js_dir}")
    print()

    error_count = validate_imports(js_dir)
    sys.exit(1 if error_count > 0 else 0)

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Comprehensive benchmark analysis script."""
import json

# Benchmark 1: Full (with bloom)
bench1 = {"frames":271,"total_ns":52314647483,"avg_frame_ns":193042979,"min_frame_ns":51836367,"max_frame_ns":374538835,"p50_frame_ns":162985388,"p95_frame_ns":352531263,"p99_frame_ns":363419150,"phases":{"commit_apply_ns":626671466,"scene_update_ns":2217355936,"render_ns":35646406434,"effects_ns":11148472767,"export_ns":2674588150},"commits_applied":86740,"scene":{"files":31575,"users":4786,"directories":4836}}

# Benchmark 2: No bloom
bench2 = {"frames":271,"total_ns":41876736969,"avg_frame_ns":154526704,"min_frame_ns":12080808,"max_frame_ns":353282031,"p50_frame_ns":118816597,"p95_frame_ns":323422759,"p99_frame_ns":343964771,"phases":{"commit_apply_ns":634173040,"scene_update_ns":2299616023,"render_ns":36210069310,"effects_ns":53469,"export_ns":2731643126},"commits_applied":86740,"scene":{"files":31575,"users":4786,"directories":4836}}

def analyze(name, data):
    print(f"\n{'='*70}")
    print(f"{name}")
    print('='*70)

    total_s = data['total_ns'] / 1e9
    avg_ms = data['avg_frame_ns'] / 1e6
    min_ms = data['min_frame_ns'] / 1e6
    max_ms = data['max_frame_ns'] / 1e6
    p50_ms = data['p50_frame_ns'] / 1e6
    p95_ms = data['p95_frame_ns'] / 1e6
    p99_ms = data['p99_frame_ns'] / 1e6

    print(f"Total: {total_s:.2f}s | Frames: {data['frames']} | FPS: {data['frames']/total_s:.1f}")
    print(f"\nFrame times:")
    print(f"  Average: {avg_ms:.1f}ms ({1000/avg_ms:.1f} FPS)")
    print(f"  Min:     {min_ms:.1f}ms")
    print(f"  Max:     {max_ms:.1f}ms")
    print(f"  p50:     {p50_ms:.1f}ms")
    print(f"  p95:     {p95_ms:.1f}ms")
    print(f"  p99:     {p99_ms:.1f}ms")

    print(f"\nPhase breakdown:")
    phases = data['phases']
    for phase, ns in sorted(phases.items(), key=lambda x: -x[1]):
        pct = 100 * ns / data['total_ns']
        ms_per_frame = (ns / 1e6) / data['frames']
        print(f"  {phase:20s}: {ns/1e9:6.2f}s ({pct:5.1f}%, {ms_per_frame:6.1f}ms/frame)")

    print(f"\nScene: {data['scene']['files']} files, {data['scene']['users']} users, {data['scene']['directories']} dirs")
    print(f"Commits: {data['commits_applied']}")
    return data

# Analyze both
b1 = analyze("BENCHMARK 1: WITH BLOOM EFFECTS", bench1)
b2 = analyze("BENCHMARK 2: NO BLOOM EFFECTS", bench2)

# Comparison
print(f"\n{'='*70}")
print("COMPARISON: Bloom Impact")
print('='*70)

bloom_overhead = (b1['total_ns'] - b2['total_ns']) / 1e9
bloom_pct = 100 * bloom_overhead / (b1['total_ns']/1e9)
print(f"Bloom overhead: {bloom_overhead:.2f}s ({bloom_pct:.1f}%)")
print(f"Frame time reduction: {(b1['avg_frame_ns']-b2['avg_frame_ns'])/1e6:.1f}ms")
print(f"FPS improvement: {271/(b2['total_ns']/1e9) - 271/(b1['total_ns']/1e9):.1f}")

# Bottleneck analysis
print(f"\n{'='*70}")
print("BOTTLENECK ANALYSIS")
print('='*70)

# Render phase breakdown (from frame 200 profile)
print("\nRender phase breakdown (from Frame 200 profile):")
print("  Files:       170.48ms (35441 files, 0.005ms/file)")
print("  Users:        37.35ms (3271 users, 0.011ms/user)")
print("  Actions:      35.39ms (4965 actions, 0.007ms/action)")
print("  Directories:  34.39ms (3285 dirs, 0.010ms/dir)")
print("  Culling:       0.12ms")
print("  TOTAL:       277.73ms")

# Cost per entity
print("\nPer-entity rendering costs:")
print("  File:      ~4.8µs (dominated by draw_disc)")
print("  User:      ~11.4µs (complex avatar + label)")
print("  Action:    ~7.1µs (beam lines)")
print("  Directory: ~10.5µs (ring + label)")

# Key hotspots
print("\n" + "="*70)
print("KEY HOTSPOTS (highest impact)")
print("="*70)
print("""
1. RENDER PHASE (68-86% of time): 131-134ms/frame
   - draw_disc() for files: ~35k calls at 4.8µs each
   - draw_text() for labels: expensive font rasterization
   - Anti-aliased line drawing: sqrt() in hot loop

2. BLOOM EFFECTS (21% when enabled): 41ms/frame
   - Gaussian blur: O(width * height * radius)
   - Multiple passes (bright extract, blur H, blur V, composite)
   - Already optimized in Phase 27 (sliding window blur)

3. SCENE UPDATE (4%): 8ms/frame
   - Force-directed layout: Barnes-Hut O(n log n)
   - Entity position updates
   - Spatial index rebuild

4. EXPORT (5%): 10ms/frame
   - PPM file writing (uncompressed RGB)
   - Could be parallelized with async I/O

5. COMMIT APPLY (1%): 2ms/frame
   - Fast, well-optimized
""")

# Recommendations
print("="*70)
print("OPTIMIZATION RECOMMENDATIONS")
print("="*70)
print("""
CRITICAL (>10ms/frame impact):
1. File rendering: Consider instancing/batching for identical discs
2. Text rendering: Cache rasterized glyphs more aggressively
3. GPU offload: wgpu/WebGPU for parallel disc/circle rendering

HIGH (1-10ms/frame impact):
4. Spatial culling: Early-out for off-screen entities
5. LOD system: Skip tiny entities at high zoom-out
6. Action pruning: Limit visible action count

MEDIUM (<1ms/frame impact):
7. Use SIMD for color blending (already enabled for WASM)
8. Reduce allocations in render loop
9. Pre-compute entity bounds once per frame
""")

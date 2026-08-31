# Array-class verification: MINI_DEPTH sweep over the ten machines

**Date:** 2026-08-30 · **Code:** `qgkit/bb6/d5_generic.py` ·
sweep driver appended to `experiments/outputs/arrayclass_ladder_sweep.jsonl`
(70 rows: 10 machines x MINI_DEPTH in {6, 8, 12, 16, 24, 40, 10^9},
2M-step learn / 2M-step held-out each, fail-closed at every rung).

The prior single-setting run (2026-08-27, MINI_DEPTH=8) left the ten
non-rank-1 array-class machines at fixed rungs. The one free knob in the
generic pipeline is the mini-arrival depth threshold; this sweep measures
how far the ladder climbs when that knob is tuned per machine. No new
segmenter and no parametric rules were granted; every number below is the
unmodified fail-closed pipeline at a different threshold.

## Best setting per machine

Best = maximum held-out exact rate, tie-broken by tiled fraction.
Horizon 4M steps per run (2M train, 2M validate).

| machine | best depth | tiled | held-out exact | conflicts | rung |
|---|---|---|---|---|---|
| `1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB` | 6 or 8 (identical) | 99.8% | 82.4% (74,443/90,318) | 308 | CANDIDATE |
| `1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC` | 24 | 38.7% | **99.77%** (440/441) | 5 | LAW-EXACT |
| `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB` | 24 | 56.3% | **100.00%** (395/395) | **0** | LAW-EXACT |
| `1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---` | 40 (best with any validation) | 1.4% | 0/9 | 45 | ARCH-VARIANT |
| `1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE` | 12 (only nonzero tiling) | 0.6% | 0/0 | 0 | ARCH-VARIANT |
| `1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD` | 12 | 6.6% | 3.9% (9/234) | 92 | TWO-SIDED |
| `1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE` | 12 | 6.6% | 2.6% (6/229) | 92 | TWO-SIDED |
| `1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---` | 6 | 32.8% | 0.7% (9/1,344) | 505 | TWO-SIDED |
| `1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF` | 8 | 13.5% | 0/420 | 47 | TWO-SIDED |
| `1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC` | 12 | 10.7% | 0/412 | 222 | TWO-SIDED |

## What the sweep changed versus the single-setting run

1. **Machine 3 (`1RB0LF_0RC1RD…`) is now conflict-free and perfect
   where tiled.** At MINI_DEPTH=24 the literal calculus learns with
   zero rule conflicts and reproduces every one of 395 held-out
   segments exactly (word, step count, offset, next arrival kind);
   MINI_DEPTH=40 confirms at 370/370. The prior run at depth 8 had
   29 conflicts and 98.55%. The tiled fraction stays near 56%, so the
   verdict remains LAW-EXACT rather than CANDIDATE, but the law itself
   is now clean: everything the segmenter extracts obeys a
   deterministic literal rule table (80 ctx rules, 17 tails).
2. **Machine 2 (`1RB---_1LC0LD…`) sharpens to 99.77%** (440/441 at
   depth 24, confirmed 426/427 at depth 40) with conflicts down from
   37 to 5. Same story: the transducer law is essentially exact; the
   40% tiling ceiling is a segmentation failure, not a law failure.
3. **The depth response is non-monotone and band-structured.** For
   machines 2 and 3, depths 12 and 16 are catastrophic (roughly 1,000
   conflicts, 0% held-out) while 8 and 24 are clean. This matches the
   dip-family anatomy from the 2026-08-27 ladder document: excursion
   depths cluster in arithmetic families (3+6k, 5+6k), and a threshold
   landing inside a family splits one parametric event into
   conflicting literal rules. Depth 24 sits above the low families and
   cleanly excludes unit dips.
4. **Machine 1 (`1RB0LF_1RC---…`) is already at its sweep optimum.**
   Depths 6 and 8 give identical results (99.75% tiled, 82.42%
   held-out); any depth of 12 or more destroys segmentation outright
   (231 or fewer segments in 4M steps versus 180,159). Its remaining
   17.6% held-out gap is parametric (the 3+6k / 5+6k dip ladder),
   not a threshold issue; it still needs its own parametric families,
   exactly as rank-1 did.
5. **Machines 4 and 5 are threshold-insensitive.** Machine 4 never
   exceeds 1.4% tiling at any finite depth (its dip spectrum is
   continuous); machine 5 never exceeds 0.6%. The degenerate setting
   MINI_DEPTH=10^9 (full arrivals only) tiles 87.5% of machine 4's 24
   giant segments but yields zero validation data at this horizon.
   Both stay ARCH-VARIANT.
6. **No two-sided machine crosses any gate at any depth.** The best
   held-out figure among the five is 3.9% (machine 6 at depth 12).
   Machine 8 at MINI_DEPTH=10^9 tiles 89.9% of its 907 full-sweep
   segments, but 0 of 263 held-out segments validate: its one-sided
   projection is architecturally regular yet not literally learnable,
   consistent with the far end injecting unseen context into each
   return sweep.

## Two-sided diagnostics (400k raw steps each)

For each of the five two-sided machines: lo/hi record-advance counts,
burst structure of same-end advances, and end-to-end traversal pattern
(an end switch = the head touching the current extreme opposite to the
last extreme touched).

- `1RB1LC_1RC---…`: extents -420/+750; 420 lo vs 750 hi advances in
  108 bursts (mean burst 7.8 left / 13.9 right, max 61); 107 end
  switches, traversals strictly alternate ends with excursion gaps
  growing to about 24k steps by t=400k. Burst lengths follow a
  reproducible pattern (…R33 L16 R11 L6 R11 L10 R22 L22…).
- `1RB0RA_1RC0RF…`: extents -450/+710; 450 lo vs 710 hi advances in
  96 bursts (max burst 98 left); 95 end switches, gaps to about 21k
  steps. Its burst sequence is identical to `1RB1LC…`'s
  (…R33 L16 R11 L6 R11 L10 R22 L22 R11 L10 R33 L22 R11…): the two
  machines share the same meta-dynamics at this horizon.
- `1RB1RA_1LC0RA…`: extents -410/+453; 410 lo vs 453 hi advances in
  119 bursts (max 80 right); 120 end switches, one excursion of 76,559
  steps before t=400k, the least regular burst pattern of the five.
- `1RB0RD_1RC1LE…`: extents -508/+421; 508 lo vs 421 hi advances in
  132 bursts (max 44 left, 15 right); 131 end switches, gaps to 41k
  steps, left end dominant.
- `1RB1LD_1LC---…`: extents -504/+399; 504 lo vs 399 hi advances in
  106 bursts (max 68 left, 25 right); 105 end switches, one 73,440-step
  excursion, left end dominant.

Common shape: both extremes advance persistently (neither end freezes),
advances arrive in bursts of 5 to 100 same-end records, and full
traversals alternate ends throughout, with excursion lengths growing
roughly linearly in elapsed time. This is the alternating-frontier
structure the planned bidirectional segmenter assumes: each burst at one
end is a candidate one-sided segment run, and the alternation gives the
natural meta-arrival for stitching the two frontiers.

## Honest scope

Horizons: 4M steps per (machine, depth) cell, 2M train / 2M validate;
diagnostics at 400k raw steps. "Tiled" is the fraction of extracted
segments passing exact input/output/step-count tiling; "held-out exact"
counts only full-configuration reproduction (word, dt, offset, next
kind). The sweep tunes exactly one scalar threshold; no machine received
parametric rules or a modified segmenter. Verdict rungs are unchanged in
category for all ten machines; the movement is within-rung (machines 2
and 3 now law-exact at 99.77% and 100.00% where tiled, machine 3 with
zero conflicts). CANDIDATE = passes the 90% architecture gate but not
held-out exactness; LAW-EXACT = held-out exact where tiled but below the
architecture gate; ARCH-VARIANT = one-sided but essentially untiled at
every threshold; TWO-SIDED = needs the bidirectional formalism.

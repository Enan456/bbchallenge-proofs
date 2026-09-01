# Bidirectional ladder for the five two-sided array-class machines

**Date:** 2026-08-31 · **Code:** `qgkit/bb6/d5_bidir.py` ·
results in `experiments/outputs/d5_bidir_full.json` (main run) and
`experiments/outputs/d5_bidir_split.json` (micro-rule diagnostic).
Horizon 4M steps per machine, rules learned on segments starting
before 2M steps, held-out validation on segments starting in 2M to 4M,
fail-closed at every rung.

The five TWO-SIDED machines from the 2026-08-30 verification never
crossed any gate under the one-sided pipeline. This run builds the
bidirectional segmenter that their alternating-frontier anatomy calls
for and pushes the d5_generic certification ladder through it.

## The segmenter

A boundary is an arrival at either extreme: a direction-change turn at
a position at or beyond the current record extreme on that side. The
segmenter has no tunable threshold; there is no MINI_DEPTH analog.
Between consecutive boundaries exactly two sub-segment kinds occur.

- **X (cross):** boundaries on opposite ends. One full traversal
  sweep; every cell between the extremes is rewritten.
- **B (burst):** boundaries on the same end. One record advance
  inside a burst; the excursion keeps an identity prefix below its
  floor (the deepest return position).

A full traversal in the sense of the 2026-08-30 diagnostics is one X
followed by the run of Bs at its destination end; the configuration is
the whole word between extremes plus the active end, and consecutive
traversals alternate ends. The alternation held without exception on
all five machines across the full horizon.

Each sub-segment is tiled by the d5_generic max-turn unit walk in an
oriented frame that always reads left to right with the arrival end on
the right; the mirror cases reverse the cell string. X is the
degenerate case with floor 0 and the far turn at the entry boundary.
Two exactness repairs were needed relative to the verbatim d5_generic
walk, both forced by measured turn geometry.

1. **Suffix-minimum trailing windows.** The two-sided sweeps make
   nested backtracks: a cross first shoots deep, returns almost to its
   origin, then marches out with bounded backtracks and occasional
   deep dips. Next-minimum trailing windows (the d5_generic rule) are
   then non-monotone and the emission tiling breaks; under the
   original rule only 42 to 67 percent of sub-segments tiled. The
   final writer of a cell is instead governed by the deepest future
   return, so the trailing window of a leading turn is the suffix
   minimum over all later return positions. These are monotone by
   construction and attribute nested backtracks exactly.
2. **Floor at the deepest return.** B floors are the minimum position
   over the whole excursion, not the first sufficiently deep return.

Every sub-segment is verified by exact telescoping: consumed spans
concatenate to the input word, emitted windows concatenate to the
output word, and unit step counts sum to the segment step count, with
the identity prefix checked below the floor. Any failure is counted
and sampled, never absorbed.

## Ladder results

Sub-segment columns count sub-segments; the traversal columns count an
X together with its following B run, exact only if every member
reproduced exactly (word, step count, arrival, head offset, next
kind). Validation of B sub-segments receives the floor and incoming
head offset from extraction, exactly as d5_generic minis did; the
shoot cost is derived as head-to-floor distance plus a learned
deviation stored in the head rule.

| machine | subsegs (X+B) | tiled | conflicts | ctx | tails | held-out sub | held-out traversal |
|---|---|---|---|---|---|---|---|
| `1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD` | 1,112 (143+969) | **100.0%** | 3,153 | 271 | 145 | 3/324 (0.9%) | 0/6 |
| `1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE` | 1,128 (131+997) | **100.0%** | 3,124 | 285 | 143 | 2/321 (0.6%) | 0/4 |
| `1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---` | 1,276 (192+1,084) | **100.0%** | 1,744 | 244 | 384 | 32/372 (8.6%) | 1/33 (3.0%) |
| `1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF` | 1,090 (233+857) | **100.0%** | 2,714 | 672 | 191 | 0/314 (0.0%) | 0/24 |
| `1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC` | 1,101 (185+916) | **100.0%** | 2,673 | 706 | 195 | 0/320 (0.0%) | 0/20 |

The architecture rung is now fully passed: with the correct
segmentation and window rule, every extracted sub-segment on every
machine tiles exactly. This is the first pipeline under which the five
two-sided machines reach 100 percent tiling; the best any of them
managed one-sided was 33 percent. The law rung fails: the literal
calculus does not generalize, for reasons that are now precisely
localized (below).

## Twin verification

The first two machines were flagged as twins by their identical burst
sequences. The bidirectional streams confirm and sharpen this. The
traversal streams align at a shift of 12 traversals (the first machine
has 12 extra early traversals from its transient). At the 4M horizon,
131 traversal pairs align; 129 of them (98.5 percent) have identical
burst-run structure (same starting end, same number of record advances
in the destination burst). The word lengths at aligned crossings
differ by exactly 52 cells in 127 of 131 pairs, the first machine
always longer.

Aligned words are byte-identical on the interior: in every aligned
pair, from either traversal direction, the disagreement is confined
to at most 19 cells at the left extreme (median 15 to 17), on top of
the constant 52-cell block that only the first machine carries there. The learned interior rules coincide under a
state bijection: matching context rules by frame, lookahead and
effect yields the relabeling A1 to C1, D0 to F0, D1 to F1 with 420
consistent assignments against 6 clashes, and the label-free unit
alphabets share 182 of 240 distinct units (Jaccard 0.758, measured at
the 1M-step learning horizon).

Verdict: one law, two realizations. The two machines run the same
segment-level dynamics, the same burst meta-sequence and the same
interior transducer rules up to renaming states; the realizations
differ by a bounded gadget at the left frontier, a 52-cell block plus
a cap of at most 19 cells that the twins format differently.

## Residual failure classes

The held-out failures decompose cleanly; counts below are for the
first machine, the others are proportionate.

1. **Long literal units (dominant; no-head 177, no-ctx 106,
   cons-mismatch 26 of 321 failures).** Turns are sparse in these
   sweeps: 42 to 62 percent of extracted units consume more cells
   than the 20-cell lookahead, with straight legs of 60 to 250 cells.
   A literal rule whose consumed span grows with the word never
   recurs on held-out data. Concrete example: the B advance at
   t=2,006,214 (left end, word length 2,220, floor 1,072, 4,204
   steps) fails no-head because its head rule key is the literal span
   from the floor to the first leading turn; the floor window
   `#.####.#.#...` was seen in training only with other extents.
2. **Emission finality is not locally decidable (structural).** The
   obvious repair for class 1 is to split long straight legs into
   one-cell cruise micro-rules labeled by the machine state at each
   leading-edge crossing; leg straightness makes the split exact
   (consecutive turns bound straight legs, so depth equals half of
   step count minus span). This was implemented (`D5_SPLIT=1`) and it
   tiles exactly, but learning it produces 70k to 126k rule
   conflicts and no held-out gain. The conflict breakdown pins the
   reason: about 85 percent are cruise-emission conflicts, the same
   machine state and 20-cell context forced to emit either the
   written cell or nothing depending on whether a future backtrack
   dips below that cell. Emission finality depends on the depth of
   future excursions, which is unbounded lookahead; no
   bounded-lookahead literal transducer can assign these emissions
   consistently. The exact law needs parametric units carrying the
   backtrack depth as a variable, the same shape of extension that
   the rank-1 trisection calculus needed for its dip families.
3. **Parametric shoots.** Ninety percent of B excursions descend to
   their floor along a non-straight path, so the shoot cost deviates
   from the head-to-floor distance. The deviation is stored per head
   rule and conflicts when depth families collide on one key; this
   accounts for most of the 1,700 to 3,200 learning conflicts in the
   main run.
4. **Next-kind nonlocality (small; 6 of 321).** Whether a burst
   continues or ends is stored in tail rules and occasionally
   conflicts, since the answer depends on content away from the tail
   window. The rank-1 machine had a derived law for this; none is
   attempted here.

March regressions (a later leading turn at or below a previous one)
occur in 29 to 61 percent of sub-segments; the walk then closes the
segment with a literal tail, which stays exact but memorizes. This is
a symptom of class 1, not a separate failure.

## Honest scope

Horizons: 4M steps per machine, learn below 2M, validate on 2M to 4M;
the traversal gaps grow to tens of thousands of steps, so the held-out
window contains only 314 to 372 sub-segments (4 to 33 traversals) per
machine. "Tiled" means exact input, output and step-count telescoping
of the extracted unit decomposition, checked fail-closed per
sub-segment; with suffix-minimum windows this check is passed by
construction whenever the decomposition exists, so the architectural
content of the 100 percent figure is that the segmentation, the
floors, the identity prefixes and the alternation are everywhere
consistent, not that the units are learnable. Held-out validation of B
sub-segments takes the floor and the incoming head offset from
extraction, as the d5_generic mini validation did. The twin
relabeling was measured at the 1M-step learning horizon; the stream
alignment and word comparisons at the full 4M horizon. No parametric
rules were granted anywhere; every failure above is counted, sampled
and left standing.

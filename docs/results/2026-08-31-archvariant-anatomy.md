# Architecture-variant anatomy: both resisters are word-level fixed-dimension candidates

**Date:** 2026-08-31 · **Machines:**

- A: `1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---` (right-grower)
- B: `1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE` (left-grower,
  mirrored before analysis by swapping L and R in every transition)

Neither halts through 2x10^7 raw steps. All statements below are
empirical, extracted from full-config captures at fresh-right-extreme
records over 2M steps and validated fail-closed against 20M.

## Why the standard segmenter fails on both

At records the tapes are near-alternating: symbol-level RLE block
counts grow linearly with tape width (machine A reaches 900+ blocks
by 200k steps, machine B similarly). No bounded record shape family
exists at symbol granularity, which is exactly what the tiler and
MINI_DEPTH sweeps measure. Under a period-2 word alphabet the picture
inverts completely: both tapes decompose into runs `(01)^k` separated
by short wall words, and the number of runs is bounded. The
architecture variance is representational, not dynamical.

## Machine A

**Record anchor.** State-B fresh right extremes; 3,588 records at
20M steps.

**Shape family.** At every settled record the tape is

```
1 00110 (0100110)^q  ( (01)^{k_i} 00110 )^{n-1}  (01)^{k_n} 0
```

with n at most 19 through 13M steps and at most 18 after. The header
is itself a stack storing the power q. One singleton wall in the
active zone alternates between 0 and 1 (a mod-2 phase bit). Total
description: about 20 integers plus one phase bit. The counter count
does not grow; the tape width (7,197 cells at 20M) lives in the
counter values and in q, which climbs from 1 to 404 after a regime
shift near 13M steps where the header begins absorbing the wake.

**Macro law (epoch calculus, per record transition).**

- Drain at depth 2: while k[-2] > 2, (k[-2], k[-1]) gains (-1, +2).
- Drain at depth d >= 3: while k[-d] > 2, (k[-d], k[-d+1], k[-1])
  gains (-1, +3, -1); the phase bit left of the refill target
  toggles each record.
- Death: the drained counter reaches 2 and merges into the edge
  (+2), followed by a short edge episode (edge deltas +3, +2, -1
  with the wall word cycling 00110010, 0011, 00, 100110) and a
  birth: the next counter in donates 1 and a fresh 3 is inserted at
  position -2.
- Cascade: successive deaths push the drain depth deeper; the
  deepest dips reach the header and exchange whole counters with it
  (values 3 and 11 in the early wake, 17 and 33 late), changing n
  by 1 and q by 1 in opposite directions.

Observed drain-depth spectrum at 20M (depth: count): 2: 1419,
3: 533, 4: 262, 5: 252, 6: 110, 7: 82, 8: 120, 9: 38, then thinning
to depth 17. This is the continuous dip spectrum the finder reported
at the raw level.

**Validation.** The composite grammar (front header exchange composed
with one back template: drain, refill, edge, death, birth) explains
3,483 of 3,587 record transitions (97.1 percent). Of the 104
residuals, 63 lie in the first 1M steps (startup transient) and 14
in the 12M-13M window (the regime shift); the rest are isolated
header-touch composites. No residual after 13.1M steps.

## Machine B (mirrored)

**Record anchor.** State-C fresh right extremes; 5,365 records at
20M steps. Turn density 0.0046 per step: each record transition is
one long left excursion and return, which is the sparse-turn glide
the finder saw.

**Shape family.** At every settled record the tape is

```
10  ( (01)^{k_i} 0 )^n
```

single-0 walls, with the two ends carrying phase words from a
bounded vocabulary (10, 100, 110, 0010, 10010, 0010010, 110010).
The counter count n reaches 33 during the first 2M steps and then
settles at 31 for the remaining 18M. Tape width 10,909 at 20M lives
entirely in the counter values. About 31 integers plus edge phases.

**Macro law (sweep calculus, per record transition).**

- Sweep to depth d: k[-1] gains +2 and the counters above it
  alternate, k[-2] loses 1, k[-3] gains 1, k[-4] loses 1, and so on
  to depth d. Even and odd depths strictly alternate in pairs
  (2j, 2j+1); the odd sweep pushes its deepest decrement one
  position deeper.
- Epoch: a fixed depth pair repeats, draining the even-offset
  counters by 1 per pair, until one of them reaches 2. The epoch
  closes with a death or rebirth episode from a bounded vocabulary
  (death: the 2 merges +2 into its right neighbor; birth: a fresh 3
  appended at the right edge with k[-2] donating 1; composites with
  a partial return sweep), after which sweeping resumes at a new
  depth pair.
- Front: the leading counter loses 1 per full-depth sweep, dies at
  2 into the header litter, and is occasionally re-emitted.

Observed sweep-depth spectrum at 20M, in pairs with near-equal
counts: (2, 3): 1398, 1345; (4, 5): 497, 479; (6, 7): 228, 220;
(8, 9): 128, 126; (10, 11): 128, 123; thinning to depth 26.

**Validation.** The composite grammar (sweep, return sweep, edge,
birth, death, front absorb or emit, and their compositions) explains
5,260 of 5,364 record transitions (98.1 percent). Of the 104
residuals, 78 lie in the first 1M steps; only 13 occur after 2M in
the remaining 18M steps, all mid-array death composites where a 2
sitting away from the edge is eliminated during a deep sweep.

## Honest verdict

Both machines are fixed-dimension candidates, not true unbounded
array machines. The resistance to the standard segmenter is a
granularity artifact: the natural blocks have period 2, so
symbol-run segmentation sees an unbounded shape while (01)-run
segmentation sees roughly 20 integers (A) or 31 integers (B) with
conditional laws of Dvisetu type, drain or sweep epochs punctuated
by death and birth at exhaustion value 2 and boundary exchange with
a header stack.

What is derived and what is not: the primitive transition alphabets
are exact on 97.1 and 98.1 percent of all observed record
transitions at 20M and on 100 percent (A, post 13.1M) and 99.6
percent (B, 3,217 of 3,230 post 2M) of the settled regimes. Not yet derived: the
deterministic selector for the post-death depth (both machines), the
sub-law of the rare header-exchange composites (A), and the mid-array
death composites (B). The n bound itself (19, then 18 for A; 33,
then 31 for B) is empirical, with no invariant yet forcing it.

## Recommended next tool

Add a period-p run-length transducer layer in front of the segmenter
and OrbitFinder (p = 2 suffices for both machines): segment on
`(01)`-runs, treat the short wall words and edge words as a finite
separator alphabet, and hand the resulting integer tuples to the
existing conditional-law machinery. The epoch calculi above are the
seed laws. Machine A additionally needs the header power q treated
as a first-class counter, since the late regime routes all wake
growth through it.

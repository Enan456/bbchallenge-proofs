# Dip-aware segmenter for the two nested-dip law-exact machines

**Date:** 2026-08-31 · **Code:** `qgkit/bb6/d5_generic2.py` (modified
copy of `d5_generic.py`; the original is untouched) ·
Protocol: 2M-step learn / 2M-step held-out (steps 2M to 4M),
fail-closed at every rung, as in the 2026-08-30 sweep.

Machines (both LAW-EXACT in the 2026-08-30 verification):

- **A** `1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC`
  (baseline MINI_DEPTH=24: 38.7% tiled, 99.77% held-out, 5 conflicts)
- **B** `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB`
  (baseline MINI_DEPTH=24: 56.3% tiled, 100.00% held-out, 0 conflicts)

## Diagnosis: what actually fails at MINI_DEPTH=24

A failure-cause classifier over the fixed-depth extraction (2M steps)
gives:

| machine | ok | idprefix | tiling_nonmono |
|---|---|---|---|
| A | 1,002 | 1,716 | 72 |
| B | 937 | 654 | 45 |

The discriminator is exact. For every ok segment the first m-turn at
threshold depth coincides with the segment's true minimum position
(floor gap 0 in 999 of 999 A minis, 934 of 934 B minis). Every
idprefix failure has a positive gap between that first deep dip and
the true minimum:

- A gaps: `3:1646, 6:4, 10:4, 14:4, 18:20, 22:18, 28..66: 21`
- B gaps: `3:602, 6:4, 10:4, 14:4, 18:16, 22:14, 28..64: 10`

Anatomy of a failing segment (A, t=7763, mini, width 130): the
arrival plunge reaches depth 37, then a descending staircase of unit
dips (5, 3, 4, 7, 5, 13, 5, 9, 13 cells deep) continues to the true
floor 34 cells lower; the fixed-depth floor sits above it and cells
below get rewritten, so the identity-prefix check fails. The
tiling_nonmono residue comes from rebuild dips mid-cascade: a
straight drop of 9 to 21 cells whose cascade is rebuilt from below
the launch maximum, breaking the strictly ascending maxima chain.

## Dip families measured

Dip depth here is the length of the straight leftward run from a
local maximum to the next turn. Histograms over 1M steps:

- Depth 1 dominates (about 244k occurrences per 1M steps on both
  machines): the frontier zigzag.
- Depth 4 is the only even depth that occurs (49 in A, 83 in B).
- Every odd depth occurs, on both machines: the families 3+6k and
  5+6k named in the 2026-08-27 ladder document are present, but so
  is 1+6k (7, 13, 19, 25, ...). Unit dips populate all three odd
  residue classes.
- The deep tails do thin into period-6 arithmetic families. Machine
  B beyond depth 283 keeps only depths congruent to 1 mod 6 (283,
  289, ..., 799) plus stragglers of the other residues up to 561.
  Machine A keeps all odd residues with period-6 modulation, plus
  isolated spikes at plunge depths of the current width epoch (125,
  259, 347 at this horizon).

Consequence: because unit dips cover every odd residue class, a
depth-membership test (d = 3+6k or d = 5+6k) cannot separate unit
dips from arrival plunges. Measured directly, the trigger plunge
depths of segments that tile and of segments that fail overlap
completely, and the floor positions of both populations are spread
over the whole tape. The planned family-membership classifier is
therefore not implementable as specified; the segmenter adapts by
keying on trajectory geometry instead of depth arithmetic.

## The dip-aware rule (implemented in d5_generic2.py)

Arrival triggering is unchanged (straight plunge of at least
MINI_DEPTH=24 below the preceding maximum, or a new leftward
record). Extraction changes in three ways:

1. **True-minimum floor.** The segment floor is the earliest m-turn
   attaining the segment's minimum position, not the first m-turn at
   threshold depth. The identity-prefix check then guards the truly
   untouched prefix and passes whenever it should.
2. **Shoot surplus table.** The shoot from the arrival maximum to
   the true floor is a plunge plus a staircase, so it takes the
   geometric distance plus a surplus (observed values 0, 8, 16, 32,
   40, 48, 218). The surplus is a literal function of the 48-cell
   tape window above the floor: keyed by a 20-cell window it is
   ambiguous for 2,699 of 2,718 A segments (971 of 1,591 B), by a
   32-cell window for 50 (42), by a 48-cell window for 0 (0).
   DipCalc learns it in a fourth rule table
   (kind, arrival, 48-cell window) and replays it at validation,
   fail-closed on unseen windows. 35 (A) and 34 (B) shoot rules
   suffice for 4M steps.
3. **Resume at record maxima.** When the maxima chain breaks
   (a rebuild dip), the walk skips non-record maxima and resumes at
   the next record maximum, folding the rebuild into the following
   event's consumed span. Descending trails still fail closed
   (trail_order), as does a cascade that collapses into a memorized
   tail chunk longer than TAIL_CAP=64 at the law operating point.

Two mechanisms were built, measured, and rejected (kept in the
module behind flags, off by default):

- A rebuild trigger (mini-arrival at the launch maximum of any
  structured dip, MIN_AGE-gated) commits arrivals whose input
  snapshots are mid-excursion tape states; their event rules collide
  with the ordinary vocabulary under the 20-cell window (545 ctx
  conflicts from a handful of splits, held-out collapse). A
  chain-restart variant fails the same way. Full support for nested
  rebuilds needs a phase-separated (recursive) vocabulary, not a
  threshold rule.
- Suffix-minimum trails with full record-maxima folding tile 100%
  of segments trivially but destroy learnability (about 10k
  conflicts, 0% held-out): the folded chunks are position-parametric
  and not literal.

## Results (2M learn / 2M held-out, steps 2M to 4M)

Law operating point (TAIL_CAP=64, the certification setting):

| machine | tiled before | tiled after | held-out before | held-out after | conflicts |
|---|---|---|---|---|---|
| A | 38.7% | **45.1%** (1,685/3,736) | 99.77% (440/441) | **100.00% (452/452)** | 5 → 1 |
| B | 56.3% | **63.0%** (1,490/2,366) | 100.00% (395/395) | **100.00% (406/406)** | 0 → 0 |

Coverage operating point (no tail cap, architecture test):

| machine | tiled | held-out exact | failure mode of the rest |
|---|---|---|---|
| A | **97.5%** (3,642/3,736) | 68.1% (643/944) | all no_rule (unseen tail literals) |
| B | **97.2%** (2,299/2,366) | 55.8% (406/728) | all no_rule (unseen tail literals) |

Reading: the dip-aware extraction now tiles 97% of segments exactly
(input word, output word, step count all verified), against 39% and
56% before, so the architecture gate is passed and the tiling target
is met. The transducer law on the cleanly segmented population is
now perfect: 100.00% held-out on both machines, machine A's single
missed segment at the baseline included, with conflicts down to 1
and 0. The coverage surplus consists of segments whose tail (the
frontier rebuild choreography at the segment's end, with nested dips
of depth 7, 13, 19, ... growing with width) is extracted and
verified but stored as one literal chunk; those chunks recur across
widths only occasionally (191 of 492 validated for A, 0 of 322 for
B), and every miss is a conservative no_rule, never a wrong
prediction.

## Remaining failures verbatim

- trail_order: 94 segments in A (of 3,736), 67 in B (of 2,366).
  First instances are the startup transient (A: t0 = 1, 45, 237;
  B: t0 = 7, 81, 157); at the 2M horizon 35 (A) and 16 (B) occur
  after step 100k, and exactly one more arrives per machine in the
  entire 2M to 4M held-out window. These are the deep nested
  rebuilds whose trails descend.
- Coverage-point validation failures are no_rule on long-tail
  segments, first at t = 2,481,111 / 2,486,699 / 2,492,311 (A) and
  t = 2,001,281 / 2,002,775 / 2,002,951 (B); tail literals reach
  length 225 (A) and 1,921 (B) by step 2M.
- No mismatch (wrong word, step count, offset, or next-arrival
  kind) occurs at either operating point in the full 2M-segment
  held-out window.

## Honest scope

Horizon 4M steps per machine, single seed, the standard blank-tape
orbit. "Tiled" is the fraction of extracted segments passing the
exact input/output/step-count tiling identities; "held-out exact"
counts full-configuration reproduction (word, dt, offset, next
arrival kind) on segments arriving after step 2M, with the floor
supplied from extraction exactly as in the baseline pipeline. The
trigger threshold is untouched; the dip families motivated but did
not survive as a classifier, and the measured replacement (floor
geometry, 48-cell shoot windows, record-maxima resume) is machine
independent. The residual 2.5% (trail_order) and the memorized
long tails are the remaining distance to CANDIDATE status; closing
them needs parametric family rules for the frontier rebuild
choreography, the same step rank-1 required.

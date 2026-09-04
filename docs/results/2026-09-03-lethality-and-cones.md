# Lethality formulas and raw halt-cones: sharpening the converse

**Date:** 2026-09-03 · **Code:** `docs/results/ah_lethality_oddc.c`,
`docs/results/ah_lethality_evenc.py`, `docs/results/d3_cone_depth30.py`
· cross-reference `docs/results/ah_cone.py`

Two closures already reduce their machines to a single abstract-orbit
conjecture: Antihydra to `SafeOrbitA` and dossier-3 to `SafeMetaOrbit`.
This note works the converse side. It extends the Antihydra dying-family
lethality formula, resolves the even-c gap that the parity note left
open, and re-derives the dossier-3 raw halt-cone to depth 30. The cone
work turns up a correction: the depth-24 incompatibility as stated in
the two-ended note is a heuristic that overclaims, and the sound
statement is an orbit alignment rather than a shape incompatibility.

## Part A: Antihydra's lethality formula

### A.1 The odd-c formula, verified to c = 9,999

The realizable dying family of Antihydra is `(1, 2, c)`. The parity note
reports that for odd c the raw machine, run on the materialized tape
`1^1 0 1^2 0 1^c` (state B, head on the fresh frontier, the `Realizes`
grammar), halts in exactly `(3c^2 + 44c + 125)/4` raw steps, verified at
c = 1 through 79 and spot-checked to c = 999.

Direct raw simulation now extends this to every odd c from 1 to 9,999
(all 5,000 odd values). Each `(1, 2, c)` is materialized and the raw
machine is run to its undefined transition (state F reading 0). The step
count is compared against `(3c^2 + 44c + 125)/4`.

- Mismatches: 0.
- Largest case: c = 9,999 halts at 75,095,021 raw steps, equal to the
  formula.
- Total work: 125,275,155,000 raw steps, in about 176 seconds of compute
  (`ah_lethality_oddc.c`, a fixed-array raw simulator; the head span
  stays under 2c, so the tape window is small even at c = 9,999).

The formula is a clean quadratic in c with a fixed second difference.
The per-step increment is `f(c+2) - f(c) = 3c + 25`: extending the c
block by two cells adds `3c + 25` raw steps to the halting run. This is
the arithmetic an induction in steps of 2 would carry.

### A.2 The even-c gap, resolved

The parity note flags the even-c family as an open gap: even c >= 4 does
not raw-halt within 2 x 10^7 steps even though `(1, 2, even)` is
abstractly dying, and the one even straggler `(1, 2, 2)` halts at 15,536.
The mechanism is now fully characterized (`ah_lethality_evenc.py`).

The abstract map gives `astep(1, 2, c) = none` for every c, because a
drop with counter a = 1 sits below the grammar floor (drops require
a >= 2). Abstract death here is loss of certification, not a raw halt.
Run on the raw machine, the tape `1^1 0 1^2 0 1^c` resolves by the parity
of c:

- **odd c**: the a = 1 block runs directly into the undefined transition.
  This is a genuine halt, in `(3c^2 + 44c + 125)/4` steps, with no
  re-entry into the grammar. This is the realizable dying family of A.1.
- **even c**: the a = 1 block folds and the raw machine re-materializes a
  LIVE grammar state. The re-entry is exactly `(2, (3c + 14)/2, 2)`,
  confirmed against the raw machine at c = 2, 4, 6, 8, 10 (the re-entry
  is read back off the tape through the `Realizes` grammar and matches
  the formula). The counter is bumped to a = 2, a survivor-eligible
  value.

So `(1, 2, even)` is not a realization of a dying state at all. From the
re-entry the raw orbit follows ordinary Antihydra dynamics, and its true
raw fate is exactly the Antihydra fate of the derived seed
`(2, (3c + 14)/2, 2)`. That orbit genuinely halts only if it later
reaches a boundary `(1, 2, c')` with c' ODD, the only genuinely halting
boundary; every `(1, 2, even)` boundary it crosses is itself another
re-entry. Folding those re-entries (`ah_lethality_evenc.py`, validated
against direct raw runs where they terminate within the tested horizon)
gives the true fate:

| even c | true raw fate | detail |
|---|---|---|
| 2 | halts (raw step 15,536) | orbit reaches odd `(1,2,101)` after 84 folds |
| 14 | halts (raw step 6,657) | reaches odd `(1,2,65)` |
| 16 | halts (raw step 12,785,384) | reaches odd `(1,2,3071)` |
| 6, 8, 12 | halts far beyond 2 x 10^7 | odd terminal after ~10^4 renewals |
| 4, 10, 18, 20, 50, 100, 1000 | survives | no death in 5 x 10^7 renewals |

The direct raw machine confirms the fold on every case it can reach:
c = 2, 14, 16 halt at the stated step counts; c = 4 and c = 10 do not
halt within 5 x 10^7 raw steps.

The resolution of the gap is therefore that even c is not a uniform
escape. It splits into two populations, governed by the Antihydra
conjecture on the derived seed `(2, (3c + 14)/2, 2)`: cases whose derived
orbit reaches an odd boundary (these halt, some far beyond any tested
horizon, which is why the parity note read them as escapes) and cases
whose derived orbit survives (these never halt, conjecturally). The
survivors show counters growing without bound (a in the tens, m and c in
the tens of millions after 5 x 10^7 renewals), the signature of a genuine
Antihydra survivor. The parity of c is the switch between a direct halt
and a re-entry, and the even-c abstract death is an artifact of the
grammar's a >= 2 floor.

### A.3 Lean sketch for the odd-c formula

A fixed odd c is provable by evaluation: with `materialize (1, 2, c)` as
a concrete `Config`, `stepN ((3*c^2 + 44*c + 125)/4) c` reduces to the
halting configuration and `stepN` of one fewer is non-halting, both by
`decide` or `native_decide` on the concrete run.

The general statement is

```
theorem oddc_halts (c : Nat) (hodd : Odd c) :
    RawHaltsIn (materialize 1 2 c) ((3*c^2 + 44*c + 125)/4)
```

The natural proof is induction on c in steps of 2. The step lemma relates
the run of `materialize 1 2 (c+2)` to that of `materialize 1 2 c` by the
fixed increment `3c + 25`: the two extra cells of the c block are
processed by a fixed-window segment that adds `3c + 25` raw steps and
leaves the remainder of the run unchanged. The induction structure is
clean arithmetic; the work is the segment-transport lemma for the two
extra cells, in the same style as the episode-transport lemmas of the
main closures.

## Part B: the dossier-3 raw halt-cone to depth 30

### B.1 The cone, re-derived and extended

Dossier-3 halts only in state C reading 0. Backward BFS over predecessor
constraint patterns (`d3_cone_depth30.py`, the method of the two-ended
note and `cone_sweep.py`) gives the family counts by depth:

```
1, 1, 1, 1, 1, 3, 3, 5, 3, 3, 5, 7, 7, 13, 11, 13, 17, 23, 29, 43,
46, 60, 75, 107, 134, 191, 221, 310, 401, 585, 756
```

The depth-24 count is 134, matching the two-ended note. Depth 30 has 756
families. The growth constant over depths 20 to 30 is 1.3231 per raw
step.

The "three 0s within a six-cell window" property of the note reproduces
and persists: every family at depths 4 through 30 has at least three 0s
within some six-cell window.

### B.2 The incompatibility as stated is a heuristic that overclaims

The two-ended note concludes from that window property that no certified
spawn-entry shape lies within 24 raw steps of the halt. A dossier-3 spawn
entry is a `holeTape`: state E, head at the spawn edge r, the 1-field
`[r+1, l]` to the right of the head, and two or three interior holes,
with everything at and to the left of the head equal to 0. Aligning the
spawn head to a cone family's head and enforcing the `holeTape` guards
gives an exact satisfiability test, the same style of test the parity
note applied to Antihydra's seven residual families.

The exact test refutes the literal statement. Eleven wide `holeTape`
shapes genuinely halt within 30 raw steps, at depths 6, 12, 18, 19, and
25, each confirmed by forward simulation. A concrete witness at depth 19
is the field `[4, 1000]` with holes at 7 and 50 (state E, head at 3),
which reaches state C reading 0 in exactly 19 raw steps; its abstract
state satisfies the productive spawn guard, and widening or moving the
far hole does not change the run, because the head never travels that
far.

The diagnosis is precise. The window property counts all 0s in a window,
including the spawn's own exterior 0s at and to the left of the head,
which every spawn entry carries. That is why the heuristic marks 100
percent of families incompatible at every depth. The eleven genuine
halters all have three or more 0s in a six-cell window, yet all eleven
have at most two INTERIOR zeros (zeros flanked by 1s on both sides). The
interior-zero count is the correct criterion, exactly the one the parity
note used for Antihydra: a two-hole spawn realizes at most two interior
holes, so a family with three or more interior zeros is genuinely
excluded, while a family with two or fewer must be checked exactly. The
two-ended note used the window count in place of the interior-zero count,
and that is the source of the overclaim.

### B.3 The sound statement is orbit alignment

A separation-based repair fails, because the certified orbit's own
starting spawn entry `s0 = <false, 17, 11, -39, -40>` has a hole at the
spawn edge (separation 1). The orbit is not protected by keeping holes
far from the edge.

What holds is an alignment. Running the raw machine forward from the
realization of `s0` (state E, head -40, field `[-39, 17]` minus holes
{11, -39}) for 100,000 raw steps and checking the configuration at every
step against every family of the full depth-0 to depth-30 cone gives 0
alignments. The certified orbit stays more than 30 raw steps from the
halt throughout. This is a genuine time margin at the raw level, and it
complements the value margin (distance at least 4 above the fatal
diagonal) of the earlier note.

The correct reading is that the raw-cone incompatibility for dossier-3 is
a property of the orbit, downstream of `SafeMetaOrbit`, not an
independent fact about `holeTape` shapes. Arbitrary `holeTape` shapes are
not all more than 30 steps from the halt; the orbit's shapes are.

### B.4 Lean sketch

The cone is a finite object: a `Finset` of constraint patterns
`(state, head, list of (offset, bit))`, seeded at the halt and closed
under `preds` to depth 30, which the generators can emit and check by
`decide`. Two lemmas can be stated over it.

The naive shape lemma, "no `holeTape` configuration halts within 30 raw
steps," should not be stated: B.2 gives an explicit counterexample.

The sound lemma is a bounded forward-safety statement about the orbit:

```
theorem orbit_time_margin (n : Nat) (c : Config)
    (hr : Realizes (metaOrbit n) c) :
    ∀ k ≤ 30, stepN k c ≠ haltConfig
```

which is a finite case analysis at each orbit step and follows from
`SafeMetaOrbit` together with episode transport. It records the margin
without asserting more than the orbit provides.

## Cross-reference: Antihydra's raw cone (depth 30)

Antihydra's raw halt-cone is a second, cleaner instance
(`ah_cone.py`, reproduced here). Depth 30 carries 42,295 families,
growth constant 1.4713 per raw step. The record incompatibility uses the
interior-zero criterion directly: of 9,653 state-B families, 9,646 demand
at least three interior zeros, which a `Realizes` tape (exactly two
interior zeros, the two block separators) cannot supply; the remaining 7
are checked exactly against every record shape with a, m, c < 40 and all
7 fail. No record configuration is within 30 raw steps of the Antihydra
halt.

Antihydra therefore used the correct interior-zero methodology from the
start, while dossier-3's two-ended note used the rawer window count. The
recommendation is to upgrade dossier-3 to the same exact test, at which
point its honest converse-side result is the orbit-alignment time margin
of B.3, not a shape incompatibility.

## Honest scope

The odd-c formula is verified by direct raw simulation for every odd c
from 1 to 9,999; the induction to all odd c is sketched, not carried in
Lean. The even-c fate rests on the Antihydra conjecture applied to the
derived seeds `(2, (3c + 14)/2, 2)`: the halting cases are confirmed by
raw simulation where they terminate within the tested horizon (up to
2 x 10^8 raw steps), and the survivor cases are exact abstract iteration
to 5 x 10^7 renewals, not proofs of non-halting. The dossier-3 cone is
exact to depth 30; the eleven within-30 `holeTape` halters are exact and
forward-verified; the orbit-alignment result is machine-checked over
100,000 raw steps from `s0` against the depth-30 cone, in python, not
Lean. The exact spawn test uses the productive spawn guards and a
field-window bound of 3,000 cells, which the depth-30 constraint windows
sit well inside.

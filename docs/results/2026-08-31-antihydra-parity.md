# Antihydra at evidential parity: game, seeds, and the two-ended cone

**Date:** 2026-08-31 · **Code:** `qgkit/bb6/halting_game_ah.py`,
`docs/results/ah_almost_all.py`, `docs/results/ah_cone.py`

Antihydra (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) has its Lean
conditional closure in `busy-beaver-core/BusyBeaverCore/
AntihydraRawTM.lean`: `safeOrbitA_nonhalting` reduces non-halting from
the blank tape to `SafeOrbitA`, the statement that the abstract orbit
`aorbit` of the triple map `astep` never dies. This note brings the
machine to the same evidential standing as dossier-2/3: the halting
game, the almost-all-seeds analysis, and the two-ended cone.

## 0. The mirror and its validation

The python mirror copies `astep` verbatim: for (a, m, c), if m >= 3
then (a, m-2, c+3) (hydra); if m = 2 then (a-1, c+3, 2) when a >= 2
and death otherwise (drop); if m = 1 then (a+2, c+2, 2) (merge);
m = 0 is dead. Seed (2, 7, 2). States are materialized through the
`Realizes` grammar: solid blocks 1^a 0 1^m 0 1^c anchored at p, head
on the fresh frontier p + 3 + m + c, control state B, blank
elsewhere.

Validation against the raw machine, before any use:

- the transition table parsed from the machine string equals the Lean
  `instr` table entry by entry;
- 62 raw steps from blank land exactly on the certified anchor:
  state B, head 6, tape equal to the (2, 7, 2) realization at
  p = -6 (`startup_run` + `realizes_start`);
- 10,001 consecutive abstract records (10^4 applications of the
  mirror, with the per-rule raw costs 2c+11 / 2c+16 / 2a+2c+22 and
  anchor deltas 0 / -1 / -1 from `qgkit/bb6/dragon/predictor.py`)
  were checked against 51,854,692 raw steps: at every predicted
  record index the raw state, head, full tape window, and a global
  ones-count agreed exactly. Zero mismatches.

The game script re-runs the anchor check and the first 1,000 records
(about 700,000 raw steps) at import.

## 1. The halting game (`qgkit/bb6/halting_game_ah.py`)

Game G(K, r) on the claim "the machine halts within K abstract
steps". States are the hydra triples; the law check is one `astep`
evaluation; the terminal check materializes the claimed dying state
through `Realizes` and runs the raw machine, which must actually
halt.

A lethality split, measured before the game: the realizable dying
family is (1, 2, c) (the grammar demands a, m, c >= 1, so m = 0 and
a = 0 states have no tape realization). For odd c the raw machine
halts in exactly (3c^2 + 44c + 125)/4 steps (formula verified at
c = 1 through 79 and spot-checked at c = 9, 21, 99, 999). For even
c >= 4 the run escapes the broken grammar and does not halt within
2 x 10^7 raw steps (tested at c = 4, 6, 8, 10); the one even
straggler (1, 2, 2) halts at 15,536. Abstract death is loss of
certification, not in itself a halt; forgers therefore forge
raw-verified lethal terminals, and the terminal check enforces the
actual halt in every play.

Measured play at K = 100,000 abstract steps (22 volleys; the final
record's tape realization spans about 100,000 cells and sits at raw
step 5,091,340,016 by the certified cost model, validated to record
10^4):

- the true orbit contains zero dying states, so honest provers
  cannot name a halt index over the whole horizon; the minimum
  counter at any drop event is 6, against the death requirement
  a <= 1;
- forged terminals: 41 dying states, all raw-verified halting, halt
  times 43 / 1,743 / 15,536 raw steps (min / median / max);
- seam forgers (true orbit spliced to a lethal terminal at a random
  index, one law seam by construction):

| r (law checks) | accept rate (trials) | bound (1-1/K)^r |
|---|---|---|
| 64 | 1.000 (2000) | 0.9994 |
| 1,024 | 0.979 (1000) | 0.9898 |
| 16,384 | 0.755 (200) | 0.8489 |
| 262,144 | 0.000 (30) | 0.0727 |
| 1,048,576 | 0.000 (10) | 0.0000 |

Observed rates sit at or below the single-seam bound because a
splice generically breaks the law on both of its sides (astep of the
dying state is undefined, so the check at the forged index also
fails), giving an effective catch rate near 2/K; a forger seaming at
the final index would attain the bound. At r = 2^18 and r = 2^20 no
forgery survived any trial.

## 2. Almost all seeds (`docs/results/ah_almost_all.py`)

Seed space: triples (a, m, c), volley-compressed exact iteration,
survival declared at counter a >= 60 (residual model hazard below
4 x 10^-13, justified by the hazard measurement below).

Exact enumeration:

| box | seeds | died | fraction | latest death (volley) |
|---|---|---|---|---|
| [2,4)^3 | 8 | 4 | 0.5000 | 23 |
| [4,8)^3 | 64 | 15 | 0.2344 | 32 |
| [8,16)^3 | 512 | 10 | 0.0195 | 31 |
| [16,32)^3 | 4,096 | 0 | 0 | - |
| [32,64)^3 | 32,768 | 0 | 0 | - |
| [1,8]^3 | 512 | 141 | 0.2754 | 32 |
| [1,16]^3 | 4,096 | 590 | 0.1440 | 32 |
| [1,32]^3 | 32,768 | 2,171 | 0.0663 | 32 |

The scaling differs from dossier-2/3 in an instructive way. There,
death density in shifted boxes decayed like 12/X. Here shifted boxes
are already death-free from X = 16 (exact, 36,864 seeds); all deaths
live in a bounded counter slab, and the cumulative density
0.0663 = 2.12/32 follows the same 1/X law only because the slab's
share of the box shrinks linearly.

The death mechanism is one-dimensional: the counter a moves -1 per
drop and +2 per merge and dies only at a drop with a <= 1. With fair
volley parities this is gambler's ruin with steps -1/+2, whose ruin
root solves r^3 - 2r + 1 = 0, giving r = (sqrt(5) - 1)/2 = 0.618,
the inverse golden ratio. Measured a-marginal (exact over
(m, c) in [1,48]^2 per counter value): dying fraction 0.635 at
a = 1, per-unit decay ratio 0.63 to 0.84 through a = 11 (model
0.618), then a deterministic cutoff: zero deaths for a >= 14 in the
tested window. The parity sequence of the deterministic map does not
sustain the long drop runs the model still allows. Deaths are
early-game only on every tested horizon: among 2,868 deaths from
10^5 random seeds in [1,64]^3, the death-volley quantiles are
0 / 3 / 22 / 30 at 10 / 50 / 90 / 99 percent and the latest death
anywhere is volley 32.

Drift, measured over 145,329 volleys from 500 random seeds: merge
fraction 0.4908, E[delta a] = +0.472 per volley, mean log-growth of
the block size m per volley 0.4079 against log(3/2) = 0.4055. The
walk's bias is +1/2 per volley on the counter and a factor 3/2 per
volley in size. The Borel-Cantelli estimate follows: after the orbit
reaches counter a, the remaining hazard is at most about r^(a-1)
summed along a linearly growing a, a geometric tail.

The certified seed (2, 7, 2) is not a typical survivor of the
opening: its model death probability is r^2 = 0.382, and the orbit's
minimum counter at a drop is 6 (attained at volley 3, horizon 300
volleys). Antihydra survived a 38 percent heuristic early-game
hazard, unlike the dossier-2/3 seeds, which start far from their
fatal diagonal. After the opening it is an overwhelmingly typical
survivor: a(30) = 20, a(300) = 161, residual hazard sum from volley
30 onward 1.3 x 10^-3 and from volley 300 onward below 10^-33.

## 3. The two-ended cone (`docs/results/ah_cone.py`)

### The abstract cone grows linearly: branching constant 1

The states dying within k steps of `astep` form exact preimage
families (a, m, c-spec) with c either a constant or free: the fatal
set is the m = 0 plane (no preimages; `astep` never outputs m = 0)
plus the two lines (0, 2, c) and (1, 2, c); hydra pullback maps
(a, m, cs) to (a, m+2, cs-3), and the c = 2 slice pulls back through
drop to (a+1, 2, m-3) and through merge, when a >= 2, to
(a-2, 1, m-2). The family BFS was validated exhaustively against
forward iteration on [0,13)^3: 2,197 states, zero mismatches in
minimal death depth.

Counts by depth, 0 to 60:

```
3, 2, 3, 3, 4, 4, 6, 5, 5, 6, 6, 8, 9, 10, 8, 8, 10, 11, 11, 12,
10, 12, 13, 13, 14, 14, 14, 15, 15, 16, 16, 18, 20, 19, 20, 20, 20,
21, 21, 20, 20, 22, 23, 23, 24, 22, 24, 25, 25, 26, 26, 29, 29, 29,
30, 30, 32, 34, 31, 32, 32
```

L(100) = 52, L(200) = 102, L(400) = 202. No integer linear
recurrence of order 1 through 6 fits any tested tail (exact rational
solving, windows from depths 0, 50, 100, 200, 300; orders through 12
also fail from depth 300). The growth is polynomial: L(k) = 0.498k
plus O(1) on depths 200 to 400, per-depth ratio 1.0034 over that
range and falling as 1 + O(1/k). The growth constant is 1 and the
total cone through depth k holds about k^2/4 families.

The mechanism is visible. Two free-c spines (a = 0 and a = 1, m
climbing by 2) immigrate one constant-c drop chain per depth; each
chain descends c by 3 per depth and can branch only when it lands on
c = 2, which happens for a third of chains, and the merge branch
additionally demands a >= 2, which the backward dynamics (a falls by
2 per merge pullback) rarely sustains. Measured branch events
average 1.30 per depth across depths 200 to 400, independent of
depth: subcritical branching with constant immigration and
lengthening chains, hence a linear front. The counter's forward
drift of +1/2 per volley acts backwards as an absorbing constraint
that throttles the death tree.

This is the third data point for the standing branching-constant
prediction, and it breaks the pattern in a definite direction:
dossier-3's abstract cone is a Fibonacci tree at the golden ratio
phi = 1.618 (the no-TT constraint); the rank-1 array-class machine
branches 2-adically in train lengths; Antihydra's constant is
exactly 1, a polynomially thin cone. The golden ratio does not
disappear from Antihydra; it migrates from the cone to the hazard,
as the ruin root 1/phi of the seed analysis in section 2. Where
dossier-3 pays phi^k in backward families and 1/X in seed density,
Antihydra pays k/2 in backward families and r^a in seed hazard: a
thin cone forces an exponentially safe bulk, and both regimes
satisfy the same Borel-Cantelli bookkeeping.

### The raw cone, and depth-30 incompatibility

Backward BFS over predecessor constraint patterns from the halting
transition (state F reading 0, the unique undefined entry; F is
entered only through E reading 0, per `into_F_only_from_E0`).
Family counts, depth 0 to 30:

```
1, 1, 1, 1, 1, 2, 3, 5, 8, 11, 17, 26, 39, 57, 87, 129, 190, 279,
413, 606, 890, 1308, 1923, 2829, 4161, 6124, 9012, 13263, 19522,
28737, 42295
```

Growth constant 1.4713 per raw step (depths 20 to 30). The
depth-30 frontier by control state: C 13,987, B 9,653, A 7,983,
D 7,719, F 1,803, E 1,150.

Alignment against the certified record shapes: a `Realizes` tape has
exactly two interior zeros (the block separators), everything right
of the head blank. Of the 42,295 depth-30 families, 32,642 are in a
control state other than B and cannot be records; 9,646 of the 9,653
state-B families demand at least three zeros each flanked by
constrained ones on both sides; the remaining 7 were checked exactly
against every record shape with a, m, c < 40 (their constraint
windows span at most 31 cells, so the bound is exhaustive) and all 7
fail, each demanding a 1 at or right of the head where the grammar
is blank. No record configuration is within 30 raw steps of the
halt: a time margin at the raw level, complementing the value margin
(counter distance 5 above the death requirement) at the abstract
level.

## Honest scope

The mirror is validated to 10^4 abstract records / 51,854,692 raw
steps with full-tape agreement; beyond that the cost model and map
are extrapolation certified by the Lean transport theorems, not by
execution here. Game soundness is empirical over K = 10^5 abstract
steps and inherits its unconditional form exactly from the
`SafeOrbitA` conjecture; the fate of even-c dying states beyond
2 x 10^7 raw steps is open (abstract death is loss of certification,
not a proven halt, which is the honest delta between `astep = none`
and the community's halting statement). Seed enumeration is exact to
[32,64)^3 and to counter 24 in the a-marginal with (m, c) <= 48;
the a >= 14 cutoff is an observation inside that window, not a
theorem. The linear law for the abstract cone is observed exactly to
depth 400 and the validation box is [0,13)^3; linearity at all
depths is unproven. The raw-cone incompatibility covers record
configurations only (the machine's intermediate configurations do
not carry the grammar), is machine-checked arithmetic in python, not
Lean, and its horizons are depth 30 backwards and shapes a, m, c
< 40 for the 7 exact checks.

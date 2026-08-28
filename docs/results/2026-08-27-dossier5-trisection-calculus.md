# The trisection calculus: an exact word-rewrite system for the rank-1 array-class machine

**Date:** 2026-08-27 · **Machine:**
`1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC` · **Code:**
`qgkit/bb6/d5_calculus.py` (v1), `d5_calculus2.py` (v2, the
calculus), `d5_closure2.py` (closure protocol) ·
**Test:** `tests/bb6/test_d5_trisection_calculus.py`

## What was built

Dossier-5 roadmap step 1 asked for a fail-closed word-rewrite
calculus for the top array-class machine: every tape configuration at
a canonical event expressed as a word, every transition between
events reproduced exactly — shapes and step counts — with any
unexplained event aborting the pipeline. That calculus now exists and
validates exactly.

## The machine's true anatomy

Instrumenting head turning points revealed a structure invisible at
the entry-vector level:

1. **Arrivals.** The canonical event is an *arrival*: a right-turn of
   the head at the right end of the written region, confirmed by the
   leftward excursion that follows. The tape at an arrival is a
   **head-form word**: 1-blocks of length 1, 2, or 3 separated by
   single 0s (with bounded `..`/`...` gap relics near the head end).
2. **Segments.** Between arrivals the head makes one *sweep*: a
   straight leftward shoot (cost = exactly its length in steps),
   then a rightward zigzag pass whose turning points advance
   monotonically. The pass is a **sequential transducer**: it consumes
   the word far-end-first in bounded windows (≤ 7 cells) and emits the
   next word behind its trailing edge.
3. **Two kinds of arrival.** A *full* arrival's shoot reaches the far
   end and claims exactly one fresh cell (the left extreme grows by 1
   per full sweep). A *mini* arrival's shoot stops mid-word — always
   at the `.` immediately left of a `##` cursor block that the
   previous pass's tail deposited. Mini segments re-process only the
   region right of the cursor; the prefix is verified identical.
   The dual representation: at far-end turns the same tape reads as
   single 1s with gaps in {1,3} — head-form and far-form are exact
   duals, and the pass converts between them.

## The complete rule set

Interior transducer rules (consumed cells → emitted cells, exact step
cost), learned and then frozen:

| rule | consumes | emits | steps | mode |
|---|---|---|---|---|
| B-copy | `#.` | `#.` | 12 | B |
| B-absorb | `#.###.` | `#.` | 8 | B |
| B-cursor | `##` | `#.` | 12 | B → D |
| D-insert | `#.` | `#.###.` | 12 | D |
| D-regroup(k) | `#.#.(###.#.)^k#.` | `(#.###.)^{k+1}` | 8+6k | D |

D-regroup is one parametric family (k = 0 is the plain regroup;
observed up to k = 4). Boundary structure:

- **Shoot**: cost = head offset (full) or head offset − floor (mini),
  exactly, every segment.
- **Heads**: one full-arrival head rule (`..` at the fresh far end,
  1 step); two mini-arrival head rules that consume the cursor
  (`.##.###.`, `.##.#.#.`).
- **Tails** (head-end boundary): two parametric families — the
  **trisection tail** `###.#. MIX #.` → `#.#.#. MIX' #.#` (each `###`
  in MIX becomes `#...`; dt = 5, rel = 3), which is the machine's
  namesake block-trisection, and the **C1 tail** `.X` → `#.#..X`
  (dt = 8, rel = 3) — plus six bounded literal tails.
- **Derived laws** (no stored rules): the mini floor is the rightmost
  `.##.` below the head; the next arrival's kind is *mini* iff the
  output word retains a cursor `.##.` below the head position.

Decision structure: the next rule is a deterministic function of the
previous rule label and a 20-cell lookahead; the learner verifies
single-valuedness of every context and the validator rejects any
segment not tiled exactly by the rules — input tiling, output tiling,
and step-count telescoping are all checked per segment.

The interior alphabet says what the dynamics is: a **two-phase
odometer on {1,3}-words**. In B-phase the pass copies 1-blocks and
absorbs each `(1,3)` pair into `1`; consuming the cursor `2` flips it
into D-phase, which re-emits 3s (`1 → 1,3`) and regroups
`1,1,(3,1)^k,1 → (1,3)^{k+1}`. The 3s function as carries being
transported toward the head end; the cursor marks the carry boundary;
mini segments are restarts at the cursor.

## Validation (fail-closed, exact)

Protocol: learn rule tables on a training horizon; freeze; then every
segment of a held-out horizon must be reproduced *exactly* — output
word, arrival type, step count, head offset, and next kind — and
consecutive configurations must chain (`s_in(k+1)` = `s_out(k)` plus
one fresh far cell for full arrivals, offset and kind carried).

- Self-validation, 8M raw steps: **785/785 segments exact**, 0
  excluded, 0 chain violations.
- Repo test (`tests/bb6`): learn 2M → frozen validation 2M–4M:
  exact on every held-out segment, zero novel contexts.
- Long-horizon closure (learn 40M → frozen validation to 200M):
  **2,180 / 2,186 held-out segments exact (99.73%)**, 0 extraction
  failures, 0 chain violations across all 3,956 segments. Final
  tables: 3 head rules, 186 contexts, 6 literal tails. The six
  failures split cleanly: three *novel decision contexts* (20-cell
  windows never seen in training, all in gap-relic-dense regions —
  the fail-closed design flagged them and predicted nothing) and
  three *context-aliasing mismatches* (a learned 20-cell window
  matched but the true behavior differed — every one caught by the
  exact word/dt/offset comparison; step-count errors ≤ 90 in
  ~75,000, word errors localized to the relic region). Failure
  rate: one per ~364 segments / ~27M raw steps, confined to relic
  arrangements near the head end.
- **Reseed differentials** (the strongest check): configurations
  *predicted* by the calculus 5–139 segments beyond any raw
  history were materialized as literal tapes and run on the actual
  machine — every one reproduced the predicted word, arrival,
  step count (e.g. dt = 22,865), head offset, and kind exactly,
  across both arrival kinds.
- **Fail-closed orbit extension**: iterating the calculus alone
  (40M tables) ran 1,258 segments — to predicted raw
  t ≈ 117.3M — before declining to predict at a novel context, as
  designed.
- v1 benchmark (single-kind segmentation, re-passes as literal
  tails, learn 40M → 200M): 2,120/2,127 (99.67%). Its extra
  failure and larger tail table are exactly the re-pass boundary
  leak that the v2 mini-segmentation closes; the shared residue is
  the relic-window limitation above.

## Why this matters

The four certified machines (Antihydra, dossier-1/2/3) all reduced to
fixed-dimension integer maps. This machine's state is an unboundedly
growing word — the array class — and the calculus above is the first
exact, fail-closed reduction of such a machine in this program: raw
dynamics → word dynamics with exact costs, mechanical enough to
compile into the Lean `ArrayShape` layer (episode theorems quantified
over block lists) the way the D2/D3 interaction calculus compiled
into holeTape episodes.

Steps 2–4 of the roadmap now have their substrate: the substitution
layer (the odometer on {1,3}-words), its death tree, and the
conditional closure `SafeWordOrbit → ¬RawHalts`.

## Honest scope

The calculus is empirical-exact, not yet certified: rules were
*learned* from raw runs, then *frozen and validated* on disjoint
horizons — the same discipline that preceded the D2/D3 Lean
compilation, and the tables are sized for compilation (a dozen
parametric rules + bounded literals). Horizons are what we ran:
200M raw steps (≈ 4,000 segments, words to ~24,000 cells). The
startup segment is anchored concretely, as in D2/D3.

The known limitation is quantified, not hidden: the *rule set*
(interior + parametric boundary rules) has been stable since the
first 800k steps, but the *decision function* is keyed by literal
20-cell lookahead windows, and in gap-relic-dense regions that
window is occasionally insufficient — one deviation per ~364
segments at the 40M-learn point, every one caught (never silently
absorbed) by the exact validators. Closing this last gap means
replacing the literal window table with the true finite-state
form of the transducer's decision function (equivalently: widening
context adaptively where relics cluster) — bounded work, and the
natural first move of the step-3 episode compiler.

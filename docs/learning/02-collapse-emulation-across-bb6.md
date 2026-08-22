# Set 2 — The bbchallenge program: emulating collapse-like behavior across BB(6)

**Files today:** the remainder of `AntihydraRawTM.lean` (sweeps, rule
trajectories, abstract orbit, main theorem) and of `Dossier1RawTM.lean`
(likewise, with a deeper chain-state hierarchy); the empirical side lives in
`qgkit/bb6/vcollatz/` and `experiments/stage745–755`.

## The observation that drives everything

Simulate any of the hard BB(6) holdouts and watch its *records* (frontier
configurations where the machine reaches fresh tape): the tape at a record is
not arbitrary. It is a small number of solid blocks of `1`s separated by
single-`0` gaps, and the block-length vector evolves by a small set of exact
arithmetic rules — grow-by-3 here, shrink-by-2 there, occasionally a
**collapse**: a block empties, the pattern reorganizes, and a value that was
accumulating gets consumed. This is "Collatz-like" or **collapse-like**
behavior, and the stage745 sweep showed it is not an Antihydra quirk — it is
the *dominant phenotype of the whole open set*: 1,006 of 1,094 holdouts show
growing-dimension record structure, 51 show compact-growth (cryptid-shaped)
structure, and exactly 2 admit literal 1-D mod-2 generalized-Collatz
projections (Dvisetu and one peer).

"Emulation" means we do not merely observe this: we fit an **exact macro
system** (`qgkit/bb6/vcollatz/macro.py`) — rules of the form "from record
shape X, exactly f(k) raw steps lead to record shape Y" with rational affine
value maps and guards — and require **100% exact replay** of the raw machine,
in and out of sample, over 10⁸ steps, fail-closed. Stage753 then discharges
per-rule obligations (template uniformity, exact/guarded affine event counts,
fresh-value synthetic replays): 13/13 for Antihydra, 33/33 for dossier-1.
That is strong evidence, but evidence only. Set 2's Lean layer is what turns
the emulation into theorems.

## The Lean emulation, bottom-up (Antihydra as the worked example)

1. **Sweeps** (`sweep_A`, `sweep_C`, `sweep_E`): the three self-looping
   transitions rewrite `1` over `1`, so a head crossing a block of `n` ones
   leaves the tape literally unchanged — a clean induction. These are the
   atoms every macro rule decomposes into.
2. **Rule trajectories** — the heart of the file. Each empirical macro rule
   becomes a theorem giving the *exact* raw trajectory for *all* block
   values, plus a safety certificate for its own duration:
   - `hydra_step`: from record `(a, m, c)` with `m ≥ 3`, exactly `2c + 11`
     raw steps to record `(a, m−2, c+3)`. The counter `a` is untouched —
     ~96% of the dynamics.
   - `drop_step` (`m = 2`): `2c + 15` steps; the counter *loses* a cell.
   - `merge_chain` (`m = 1`): `2n + 2k + 22` steps; the counter *gains two*.
   Each theorem's second half is an `ESafeSeg` certificate: every time state
   `E` probes a `0` during the rule, its left neighbour provably holds a `1`
   — the probes are enumerated one by one in the proof (e.g. "THE probe" at
   step 5 of the hydra core). This is where "the machine cannot halt during
   this rule" is established, not just "the rule computes the right thing."
3. **The abstract orbit.** `AState = (a, m, c)` with
   `astep : AState → Option AState` implementing exactly the three rules;
   `aorbit` iterates from the startup state `⟨2, 7, 2⟩` (reached from blank
   in a machine-checked 62-step startup, `startup_run`/`startup_safe`,
   verified by the executable `checkSafe` decision procedure).
   `astep` returns `none` precisely at the value patterns whose absence is
   the **Antihydra conjecture**: `SafeOrbitA := ∀ k, aorbit k ≠ none`
   (equivalently: the counter never runs out when the drop rule fires).
4. **Transport + dispatch.** `Realizes s cfg` says a concrete configuration's
   tape spells out the abstract state as the block grammar
   (blank · a-block · 0 · m-block · 0 · c-block · head-on-frontier · blank).
   The `transport_*` lemmas push `Realizes` through each rule; the dispatcher
   `orbit_segment` case-splits on `astep` and shows: under `SafeOrbitA`,
   every realized configuration advances, safely, to another realized
   configuration. The segment-induction keystone
   (`eprobe_safe_of_segments`) then stitches infinitely many safe segments
   into `EProbeSafe blankStart`, and Set 1's contract finishes the job:

   **`safeOrbitA_nonhalting : SafeOrbitA → ¬ RawHalts blankStart`** —
   axiom-clean, no sorry.

Dossier-1 is the same architecture with a richer abstract state
(`AState.top N | AState.lvl (L : List Nat) b c` — a *stack* of chain values,
with `unsnoc`/`lastInc2`/`collapseTarget` implementing genuine collapse
cascades) and seven transport rules instead of three; its conjecture
`SafeOrbit` encodes a recursive Collatz checkpoint law (odd `n → (3n+7)/2`,
even recurses). Result: `safeOrbit_nonhalting : SafeOrbit → ¬ RawHalts
blankStart`.

## What this does and does not claim

- **Proven:** every dynamical fact about these two machines — halt
  localization, all record transitions for all block values, startup, tape
  grammar, the full closure induction. Non-halting is formally *reduced* to
  one arithmetic statement per machine about the abstract orbit alone.
- **Not proven:** the arithmetic conjectures themselves. For Antihydra this
  is (a form of) the community's Antihydra conjecture — believed true on
  random-walk/drift grounds, with no known proof technique. Nothing in this
  repo decides any machine.
- **Across the board:** the same record-emulation machinery classified the
  full official open set (1,158 machines, 0 errors; after the 2026-08-04
  correction, 6 solid + 1 weak exact-macro PASS). The Lean closure has been
  carried end-to-end for two machines; the per-machine cost of adding more is
  exactly why Set 1 consolidation and the Set 3 geometry program exist.

# bbchallenge-proofs

Self-contained packaging of the BB(6) / bbchallenge proof program developed in
the private `Quantum_Geometry` research repo (branch `codex/latest-main-2026-07-11`,
commits `48d0448d..f85738e4`, 2026-07-28 → 2026-07-29). This repo is consumed by
`Quantum_Geometry` as a git submodule and is the unit intended for eventual
sharing with the bbchallenge community.

**Status: nothing here decides any machine.** The Lean layer is machine-checked
and axiom-clean; the macro systems and obligation discharges are exact,
fail-closed statements about bounded observed traces — empirical evidence, not
proofs of non-halting.

## Headline results

- **Full official open-set classification (1,158 machines, 0 errors):**
  9 initially gated as `PASS_EXACT_MACRO_SYSTEM` / 35 `PARTIAL` / 1,114
  `NOT_FITTABLE_HIGH_DIM`. **Corrected 2026-08-04:** two of those nine are
  refuted (their rules break at ~2e8 steps) and one is weakly validated —
  the original gate did not require a minimum number of out-of-sample
  transitions, which slow-record machines could pass vacuously. The
  defensible count is **6 solid + 1 weak**; the gate now enforces
  `MIN_OOS = 50`. See the correction section in `docs/results/`.
- **Antihydra reduces to 13 halt-avoidance obligations — and all 13 are
  mechanically discharged** (stage753: template uniformity, exact/guarded
  affine event counts, fresh-value synthetic replays at 100M steps).
  Antihydra's non-halting argument is structurally complete empirically;
  the remaining burden is the Lean raw-to-macro closure induction.
- **Dossier-1's non-halting is now formally reduced to one arithmetic
  conjecture.** `safeOrbit_nonhalting : SafeOrbit → ¬ RawHalts blankStart`
  is machine-checked and axiom-clean; every dynamical fact about the
  machine (halt localization, all seven record transitions for all block
  values, the 35-step startup, the tape grammar, the segment induction)
  is proved. `SafeOrbit` is a statement about the abstract orbit alone.
- **Dossier-1** (`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`): exact macro
  system (36 rules + 7 literals, 100% replay in/out-of-sample over 100M steps),
  recursive Collatz checkpoint law (odd `n → (3n+7)/2`, even recurses), all 33
  (rule, window) obligations mechanically discharged (uniformity + 59/59
  fresh-value synthetic replays), and a Lean-checked reduction of non-halting
  to the single contract `CProbeSafe blankStart`.
- Only **2** machines in the whole open set admit exact 1-D mod-2
  generalized-Collatz projections: Dvisetu
  (`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB`) and one peer
  (`1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`).

## Layout

- `lean/` — standalone Lake package (`lake build` inside `lean/`; core-only,
  no mathlib), all axiom-clean (`propext`, `Quot.sound`), no sorry.
  - `BBChallenge/Dossier1RawTM.lean`: halt ⟺ F reads 0; F entered only via
    `C0`; any halt passes through a reachable C-probe of a `00` pattern;
    `CProbeSafe blankStart → ¬RawHalts blankStart`.
  - `BBChallenge/AntihydraRawTM.lean`: the Antihydra mirror — halt ⟺ F
    reads 0; F entered only via `E0` (write 1, move left); any halt passes
    through a reachable E-probe of `00` on the left;
    `EProbeSafe blankStart → ¬RawHalts blankStart` — precisely the contract
    stage753 discharged. Plus `sweep_A`/`sweep_C`/`sweep_E`, the symbolic
    block-crossing lemmas that are the atoms of the closure induction.
  The remaining proof burden per machine is the raw-to-macro closure
  induction deriving the probe-safety contract from the discharged macro
  obligations (DvisetuRawTM-style).
- `qgkit/bb6/vcollatz/` — `classify.py` (sound decider chain + abstraction
  classes; demotes the 2026-07-18-falsified `certify_bouncer` verdicts) and
  `macro.py` (machine-agnostic exact macro-system fitter: constant-delta →
  exact rational affine with guards → parity refinement → flagged literals;
  fail-closed exact replay).
- `experiments/` — the stage pipeline:
  - `stage745` mass classification sweep · `stage746` 50M-step dossiers
  - `stage747` dossier-1 exact macro system (PASS)
  - `stage748` F-entry halt-window census · `stage749` rule↔window alignment
    (33 obligations) · `stage750` obligation discharger (33/33)
  - `stage751` full open-set observatory (fit + exact replay, resumable,
    sharded) · `stage752` generalized halt-localization (ranked obligation
    queue: Antihydra 13, then 24, 26, 33, 51, 54, 68)
  - `stage753` generalized obligation discharger — Antihydra 13/13 and
    dossier-1 33/33 ALL_DISCHARGED_UNIFORM; 176/269 overall; faithful
    record reconstruction certified by per-rule literal self-checks
- `experiments/outputs/` — full outputs for stages 747–750 and 752; stage751
  `summary.json` plus the 9 PASS machine records (the full 30 MB per-machine
  set lives in the parent repo); the official open-set list
  (`BB6_open_1158_2026-07-29.txt`) and the earlier 1094 holdout snapshot.
- `docs/submissions/` — draft bbchallenge wiki candidate pages (dossier-1
  deliberately unnamed; **do not submit before checking the live registry and
  asking on the forum/Discord about unpublished verdicts**).
- `docs/results/` — the cumulative results document.

## Reproduction

Python side (needs `numpy`, `tqdm`; run from repo root):

```sh
python experiments/stage747_dossier1_macro_system.py   # exact macro fit + verify
python experiments/stage751_open_set_observatory.py --input experiments/outputs/BB6_open_1158_2026-07-29.txt
```

Lean side:

```sh
cd lean && lake build
```

`#print axioms` at the bottom of `Dossier1RawTM.lean` must report only
`[propext, Quot.sound]`.

## Provenance

Files are verbatim copies from `Quantum_Geometry` at the commits above (the
Lean module keeps its original `QIG.Dossier1RawTM` namespace). The parent
repo remains the working tree; this repo is the packaged, shareable artifact.

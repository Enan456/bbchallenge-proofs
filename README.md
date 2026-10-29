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

## October 2026 update: what is proven, and the overlap with Google DeepMind

This repository was private from its creation (2026-08-03) until 2026-10-22.
It is published now because Google DeepMind's *At the Limits of Computability*
(arXiv:2610.22603, 2026-10-15) and its companion repo
[`google-deepmind/cryptids`](https://github.com/google-deepmind/cryptids)
formalize Collatz-like reductions for 53 BB(6) holdouts, seven of which are
machines this repo had already closed conditionally in Lean — including three
of the eleven the paper presents as novel (our dossier-2, dossier-3 and
dossier-7, committed 2026-08-25 and 2026-09-03). Neither side saw the other's
work. Full comparison and a 2×10⁷-step cross-verification of both
formalizations on the four shared new machines:
[`docs/results/2026-10-22-gdm-cross-verification.md`](docs/results/2026-10-22-gdm-cross-verification.md)
(harness `qgkit/bb6/gdm_cross/`, tests `tests/bb6/test_gdm_cross.py`). That
document also tabulates validation horizons side by side: the paper reports a
5×10⁶-step detection pass and 128k-step transition checks; the mirror-pair
conjectures here were validated against 10⁹ raw steps and 10⁸ renewal-map
iterations, the left-growers against 2×10⁷ raw steps with every record exact.

**What is kernel-checked here** (`cd busy-beaver-core && lake build`, 119 jobs,
every theorem reports axioms `[propext, Quot.sound]`, no `sorry`, no Mathlib —
verified 2026-10-21 on Lean `v4.30.0`):

- **115 conditional closures** of BB(6) holdouts from the 1,094-machine
  snapshot, each of the form `Safe_X → ¬ RawHalts blankStart`
  (`busy-beaver-core/BusyBeaverCore/*RawTM.lean`). `Safe_X` is an explicit,
  executable, fail-closed abstract orbit (five integers for dossier-2/3, a
  hydra triple for Antihydra, a `(state, word)` record orbit for the
  left-growing ladder machines); every dynamical fact about the machine —
  halt localization, the episode/record transitions for all block values,
  startup anchors, the transport from abstract orbit to raw tape — is proven.
  Eighteen of these are the hand-built, named closures of
  `docs/submissions/cryptid-names.md`; the other 97 were generated on
  2026-09-04 by `qgkit/bb6/rawstep_generator.py` from the same certified
  template and are individually differential-tested (`tests/bb6/test_d*_theorems.py`).
- **Bridges to the community's statements**: the standard-format machine
  code parses to our transition tables (`packages/dossier1/Bridge/Format.lean`),
  the Rocq-style zipper tape is bisimilar to our functional tape
  (`Bridge/Bisimulation.lean`), and Antihydra's orbit conjecture is proven
  equivalent to the wiki's 1-D hydra statement (`hydraSafe_iff_safeOrbitA`).
- **Unconditional negatives** (bounded, stated as such): no congruence
  invariant to modulus 384 and no rotation rigidity for the dossier-2/3
  renewal map; zero invariant-decidable machines across the cohort
  (`docs/results/2026-09-03-state-and-gaps.md`).

**What is not proven**: every `Safe_X` conjecture is open, so no machine is
decided. The converse direction (`¬Halts → Safe_X`) is established only
empirically (the halting game, `docs/results/2026-08-30-halting-game.md`);
Google's reductions carry it as a theorem (`IsHalt ↔ CollatzHalts`), ours
carry halt-localization and parser parity that theirs do not. Upgrading our
four shared closures to an `iff` is the next Lean step.

## Headline results

- **Full official open-set classification (1,158 machines, 0 errors):**
  9 initially gated as `PASS_EXACT_MACRO_SYSTEM` / 35 `PARTIAL` / 1,114
  `NOT_FITTABLE_HIGH_DIM`. **Corrected 2026-08-04:** two of those nine are
  refuted (their rules break at ~2e8 steps) and one is weakly validated —
  the original gate did not require a minimum number of out-of-sample
  transitions, which slow-record machines could pass vacuously. The
  defensible count is **6 solid + 1 weak**; the gate now enforces
  `MIN_OOS = 50`. See the correction section in `docs/results/`.
- **Antihydra's non-halting is formally reduced to the Antihydra
  conjecture.** `safeOrbitA_nonhalting : SafeOrbitA → ¬ RawHalts blankStart`
  is machine-checked and axiom-clean; all three of its transitions
  (counter frozen / −1 / +2) are proven for all block values, and
  `SafeOrbitA` is a statement about the abstract triple orbit alone.
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

- `packages/` — the Lean package split on top of `busy-beaver-core/` (see
  `packages/README.md` and `docs/learning/`): `packages/dossier1/` (the
  certified bridge layer — standard-format parser parity, the incision
  boundary-only-checking theorem `eventSafe_iff_safeOrbitA`, and the 1-D
  hydra bridge `hydraSafe_nonhalting`; plus the `trace` differential-test
  executable) and `packages/flying-dragon/` (exact geometric charts; never
  imported by the certified packages).  `scripts/check_lean.sh` builds all
  three packages under the axiom gate.
- `busy-beaver-core/` — standalone Lake package (`lake build` inside `busy-beaver-core/`; core-only,
  no mathlib), all axiom-clean (`propext`, `Quot.sound`), no sorry.
  - `BusyBeaverCore/Dossier1RawTM.lean`: halt ⟺ F reads 0; F entered only via
    `C0`; any halt passes through a reachable C-probe of a `00` pattern;
    `CProbeSafe blankStart → ¬RawHalts blankStart`.
  - `BusyBeaverCore/AntihydraRawTM.lean`: the Antihydra mirror — halt ⟺ F
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

## Standing on the shoulders of giants: Rocq parity and the proof alongside the decider

This project deliberately builds on — and stays checkable against — the
bbchallenge community's foundations. BB(5) = 47,176,870 was settled in
**Rocq** (Coq-BB5), and Rocq remains the community's reference system;
the official BB(6) open-set list, the standard machine text format, and
the wiki's cryptid analyses (including the Antihydra hydra recurrence our
bridge theorem targets) are all community work this repo consumes rather
than reinvents.

Rather than porting Rocq code, we rebuilt the same raw TM semantics
natively in core Lean and then made parity with that tradition
*checkable at three independent levels*:

1. **Parser parity (kernel-checked):** the published standard-format codes,
   parsed by an in-Lean parser, provably equal our hand-written transition
   tables (`Bridge/Format.lean`, axioms `[propext]`, with corrupted-code
   negative controls) — the formal object is the community's machine.
2. **Differential execution:** the proved `step`, run executably, is
   byte-identical over thousands of steps against an independent reference
   simulator (`tests/lean_parity/`).
3. **Semantic bisimulation (theorem):** the Rocq tradition's zipper tape
   (`left × current × right`) is proven step-for-step equivalent to our
   functional `Int → Bool` tape — `zipper_halts_iff : ZHalts zBlank ↔
   RawHalts blankStart` (`Bridge/Bisimulation.lean`), so any halting
   argument in either representation is an argument in the other.

The proofs were **developed alongside the decider pipeline, not after
it**: the `qgkit` decider chain and exact macro-system fitter surfaced
each machine's record rules empirically (fail-closed, 100% replay), the
stage750/753 obligation dischargers said exactly which statements needed
proving, and the Lean layer then certified those statements for all block
values — with the empirical layer demoted to evidence the moment the
theorem landed. Each side checks the other: the deciders found the
structure, the proofs fixed it, and the differential traces tie the two
together.

## Reproduction

Python side (needs `numpy`, `tqdm`; run from repo root):

```sh
python experiments/stage747_dossier1_macro_system.py   # exact macro fit + verify
python experiments/stage751_open_set_observatory.py --input experiments/outputs/BB6_open_1158_2026-07-29.txt
```

Lean side:

```sh
cd busy-beaver-core && lake build
```

`#print axioms` at the bottom of `Dossier1RawTM.lean` must report only
`[propext, Quot.sound]`.

## Provenance

Files are verbatim copies from `Quantum_Geometry` at the commits above (the
Lean module keeps its original `QIG.Dossier1RawTM` namespace). The parent
repo remains the working tree; this repo is the packaged, shareable artifact.

# Plan: wiring grammar principles into the hurler/catcher decider

**Date:** 2026-09-10. **Goal.** Upgrade the hurler/catcher decider for the
cryptid/renewal cohort (~122 machines, Antihydra-class) so that the
*non-halting-between-catches* step is a **theorem derived from an extracted
per-machine catch grammar**, not an observation up to `N` steps. The grammar is
the piece that turns a sound *simulator* into a sound *decider*: it is what
makes the quadratic fuel bound provable and what draws the honest line between
what a certificate can deliver (conditional closure, classification) and the
Collatz-hard wall (unconditional per-orbit halting).

Design principle throughout: **fail-closed and additive.** Every stage either
emits a machine-checked obligation or refuses; nothing weakens the existing 18
certified corridors, which serve as positive controls, and the known-open
machines (Antihydra) serve as negative controls.

## The pipeline each machine flows through

```
raw TM ──▶ (1) hurler/catcher emulation  ──▶ start/end macro-state  [have]
        ──▶ (2) extract catch grammar     ──▶ SFT / regular language  [NEW]
        ──▶ (3) prove grammar complete     ──▶ "no other transitions"  [NEW]
        ──▶ (4) non-intermittency lemma    ──▶ neutral runs bounded     [NEW]
        ──▶ (5) fuel bound as a theorem     ──▶ gap ≤ quadratic          [upgrade]
        ──▶ (6) affine renewal fit + 𝒟     ──▶ halt ⟺ orbit meets 𝒟   [have: OrbitFinder]
        ──▶ (7) verdict + Lean bundle       ──▶ Safe→¬Halt / class       [upgrade]
```

Stages 2–4 are the new grammar layer; 5 and 7 are upgrades of existing steps
to *consume* it.

## Phase 0 — interfaces and verdict schema (0.5 wk)
- Fix the **catch-alphabet**: the finite set of catcher-outcome macro-symbols a
  machine emits (for the renewal map these are `T,C,F`; general machines get an
  extracted alphabet from the emulation).
- Fix the **verdict schema** the decider may emit, and forbid the one it may
  not:
  - `UNCOND_NONHALT` (only if a finite certificate excludes 𝒟 — rare in this
    cohort, kept for easy machines),
  - `COND_CLOSURE` (`Safe_orbit → ¬Halt`, the realistic target),
  - `CLASS_ONLY` (classified, not closed),
  - `REFUSE` (grammar/fuel/localization obligation failed — fail-closed).
  - **Hard guard:** the schema makes `UNCOND_NONHALT` on a machine whose 𝒟 is
    not finitely excluded *unrepresentable*, so the Collatz-hard wall cannot be
    crossed by a bug. Negative control: Antihydra must resolve to `COND_CLOSURE`.
- Deliverable: `decider/schema.py` + a JSON record per machine; unit tests.

## Phase 1 — extract the catch grammar, and prove it complete (1.5 wk)
The grammar is the symbolic dynamics of the catcher-outcome sequence: a subshift
of finite type (adjacency on the catch-alphabet). Two sub-steps, the second is
the soundness crux.
- **1a Extract (Python, fail-closed).** From the emulation, record observed
  length-2 (later length-`n`) catch transitions → candidate adjacency matrix
  `A`. Report the language and its Markov structure.
- **1b Prove complete (the real work).** Observed ≠ admissible. Prove that `A`
  lists *every* possible transition, by the parity/structural argument that the
  renewal map's grammar lemma uses (identities in the parities of the macro-step
  outputs), reduced to a **finite check on the transition table**. Output a
  Lean-checkable `grammar_complete` lemma: `∀` reachable catch symbol `s`, the
  successor set is exactly `A[s]`. If the check does not close, `REFUSE`.
- Deliverable: `decider/grammar_extract.py`; Lean template
  `GrammarComplete.lean` instantiated per machine; validated by reproducing the
  `T→{C,F}, C→T, F→{C,F}, TT-forbidden` grammar for dossier-2/3.

## Phase 2 — non-intermittency from the grammar (1.5 wk)
This is the generalization of "`TT` forbidden," and it is what certifies the
fuel bound.
- Tag each catch symbol **neutral** (its affine macro-map has `|det| = 1`, no
  scale growth — the parabolic/`T` analog) or **expanding** (`|det| > 1`).
- Prove from `grammar_complete` that **neutral symbols cannot form unbounded
  runs**: there is `L` with every length-`L` admissible word containing an
  expanding symbol. For the renewal map `L = 2` (`TT` forbidden ⟹ every other
  step expands). General machines: compute `L` as the longest neutral path in
  `A` (finite; if `A` admits a neutral cycle, the machine is genuinely
  intermittent and out of scope → `REFUSE`).
- Deliverable: Lean `no_intermittency` lemma (`neutral_run_len ≤ L`), from the
  finite adjacency `A`. Validate: `inf|(G^L)'| > 1` matches the manuscript's
  `inf|(G²)'| = 3` for the renewal map.

## Phase 3 — the fuel bound as a theorem (1 wk)
Upgrade the existing gap-tracking from "observed ≤ `64(len+64)²` up to 20M
steps" to a proof.
- From `no_intermittency` (Phase 2) + the per-symbol affine maps, the
  record-to-record step gap is bounded by the accumulated affine growth over a
  window guaranteed to expand every `L` steps ⟹ eventual uniform expansion ⟹
  the gap obeys the quadratic fuel form. Emit `fuel_bound` as a Lean lemma with
  the explicit constant.
- If the gap form needed is super-quadratic (Phase 0 audit's "fuel unsound"
  case), `REFUSE` with the measured growth rather than force it.
- Deliverable: Lean `fuel_bound` lemma; cross-check against the audit engine's
  measured gaps for all 18 corridors.

## Phase 4 — halt-localization and the conditional closure (1.5 wk)
Reuse the existing corridor machinery; make the grammar feed it.
- **Localize:** prove `halt ⟺ the catcher reads the probe symbol ⟺ orbit meets
  𝒟`, i.e. the undefined transition is reachable only via the probe (the
  one-cell / two-cell predicate the audit already computes).
- **Fit 𝒟:** `OrbitFinder` gives the affine renewal map and `𝒟`; reuse.
- **Transport:** assemble `Safe_orbit → ¬RawHalts(blankStart)`, axiom-clean, in
  the `*RawTM.lean` shape. The grammar + fuel + localization are exactly the
  hypotheses that make the transport theorem go through.
- Deliverable: per-machine `Transport.lean`; verdict `COND_CLOSURE`.

## Phase 5 — classification and the aggregate hand-off (1 wk)
- From the grammar + affine-map signatures, tag each machine:
  **random-walk class** (Antihydra, dossier-1 — 𝒟 is a biased offset-walk
  threshold), **renewal/chaotic class** (dossier-2/3 — invariant-free), **counter
  /array class** (rank-1, shift-overflow). The grammar's neutral/expanding
  pattern and the `det` sequence separate these.
- For the renewal class, emit the fuel/scale-growth data (`Λ`, the per-return
  log-growth) as the **input to the density/almost-all argument** — the
  aggregate route that decides the statistics where per-orbit is Collatz-hard.
- Deliverable: `classification.jsonl` over the ~122; the renewal-class subset
  annotated with its density-argument inputs.

## Phase 6 — validation and scale-out (1 wk)
- **Positive controls:** the pipeline must re-derive `grammar_complete`,
  `no_intermittency`, `fuel_bound`, localization for all **18 certified
  corridors** — same verdicts, green Lean build at `{propext, Quot.sound}`.
- **Negative controls:** Antihydra and dossier-2/3 must emit `COND_CLOSURE`,
  never `UNCOND_NONHALT`; any unconditional verdict on them is a soundness bug
  and blocks the build.
- **Fail-closed replay:** 100% replay of record rules on the ~122 (as the
  existing engine).
- **Coverage report:** how many of the ~122 reach `COND_CLOSURE` vs `CLASS_ONLY`
  vs `REFUSE`, with the refusal reason (grammar incomplete / neutral cycle /
  fuel unsound / localization failed) named — no silent drops.

## What this explicitly does NOT do (the honest boundary)
The grammar layer proves everything *up to* "does the affine orbit avoid 𝒟."
It does not, and cannot, decide that for the core cohort: dossier-2/3 are
invariant-free to modulus 384, the sound invariant search returned zero, and
Antihydra is provably open. So the ceiling of this plan is **sound conditional
closure + classification + density-argument inputs**, not unconditional
per-machine decisions. The schema's hard guard (Phase 0) enforces that ceiling
structurally. Unconditional closure of any single machine in this cohort remains
Collatz-hard and out of scope.

## Sequencing and effort
Phases are mostly serial (each consumes the previous); Phases 1 and 5 can start
in parallel with the Python extractors while the Lean templates for 2–4 are
written. Rough total ~8 weeks of focused work, front-loaded on Phases 1–3 (the
grammar → non-intermittency → fuel chain, which is the soundness upgrade and the
whole point). The fastest de-risking step is Phase 1b on dossier-2/3, where the
target grammar is already known and proven, so the extractor + completeness
template can be validated against a known answer before touching new machines.

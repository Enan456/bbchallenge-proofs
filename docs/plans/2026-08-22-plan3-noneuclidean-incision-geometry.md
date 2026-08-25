# Plan 3 — Non-Euclidean incision geometry: boundary-only halting detection

> **Execution status (2026-08-22):** Tasks 1–2 DONE
> (`packages/bbchallenge/Bridge/Incision.lean`: `astep_eq_none_iff`,
> `volley`, `eventSafe_iff_safeOrbitA`, `eventSafe_nonhalting` — all at
> `[propext, Quot.sound]`).  Task 3 DONE (`qgkit/bb6/geometry/`, 6/6 tests
> incl. the Lean `eorbit 0` cross-check).  Task 4 DONE at reduced scope
> (`experiments/stage756_incision_atlas.py` over the 9 stage753-queue
> machines — the 51-machine stage745 cohort is not shipped in this repo;
> headline: 16 events ≙ first 10⁸ raw steps, min death margin 4 over 20k
> events, family profiles visible; raw charts need log-scaling before
> invariant hunting).  Task 5 partial (`packages/extensions/` with exact
> charts; invariant-region attempts not started).  Task 6 open.
>
> **CONDITIONAL CLOSURE, dossier-2/3 (2026-08-24):** COMPLETE — both
> machines reduced end-to-end to `SafeMetaOrbit → ¬ RawHalts blankStart`
> at [propext, Quot.sound]: interaction-calculus atoms, cat_run/sweep
> inductions, seven episode theorems each, concrete startup anchors
> (235 / 2044 steps), abstract five-integer orbit + transport + keystone.
> The remaining conjecture is a deterministic Euclid/Collatz-hybrid
> avoidance statement, validated to 10^8 abstract episodes; the excluded
> bands are provably lethal. See
> docs/results/2026-08-24-dossier23-conditional-closure.md.
>
> **Orbit certification, dossier-2/3 (earlier):** foundation layer
> DONE in busy-beaver-core — segment-safety algebra (CSafeSeg/BSafeSeg +
> compose/strong/no-probe), the segment-induction keystones, prefix
> gluing, executable checkSafe deciders with soundness, and the
> tape-preserving sweep atoms (D↔F rightward for dossier-2, E↔F leftward
> for dossier-3), all at [propext, Quot.sound]. Remaining for full
> certification, per machine: sweep-pair inductions, rule-trajectory
> theorems for the stage757 spec rules (the mixed-guard 4-block families
> are the genuinely new part), a Realizes/ChainAt-style grammar,
> transports, an abstract orbit + conjecture, and the dispatcher — the
> Antihydra-scale climb, now with certified scaffolding and exact
> empirical blueprints (outputs/stage757/specs.json) in place.

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking. **Per user preference, code
> implementation is routed through the Codex rescue agent
> (`codex:codex-rescue`), not general-purpose subagents.**

**Goal:** Implement the program of
`docs/learning/03-noneuclidean-incision-geometry.md`: characterize *where*
incision events (orbit-death opportunities / halt windows) occur for
collapse-like BB(6) machines, prove in Lean that checking **only at those
boundaries** is sound and complete, plot the incision sets in non-Euclidean
(log / simplex / hyperbolic) coordinates across the compact-growth cohort,
and — where the empirics reveal a provable safety margin — attempt invariant-
region proofs.

**Architecture:** Three layers with a strict dependency direction (geometry
never flows into the trust base):
1. `lean/BBChallenge/Incision/` — **core-only** Lean: boundary
   decomposition, closed-form volley (event-skip) lemmas, event-process
   equivalence. Same axiom bar as Sets 1–2.
2. `qgkit/bb6/geometry/` — Python empirics: event extraction, charts,
   metrics, figures. Stage scripts `stage756+` (last used: 755).
3. `lean-geometry/` — a **separate Lake package** (may use mathlib) for
   chart formalization and invariant-region attempts. Never imported by
   `lean/`.

**Global constraints (repo-wide rules apply):**
- Honest labeling: geometric figures and margins are *empirical structure*
  unless proven in Lean; no non-halting language attaches to any plot.
- tqdm on every long-running loop; sweeps resumable via JSONL skip-scan.
- Commit prefixes `feat(bb6):` / `docs(bb6):`; Lean changes keep
  `#print axioms` at `[propext, Quot.sound]` for everything under `lean/`.

---

### Task 1: Boundary decomposition of `astep` (core Lean)

**Files:**
- Create: `lean/BBChallenge/Incision/Antihydra.lean`

**Steps:**
- [ ] Define the decidable predicates on `AState`, transcribed from `astep`
      exactly (hydra needs `3 ≤ m`, merge fires at `m = 1`, drop at `m = 2`
      requires `2 ≤ a`): `Dead s ↔ s.m = 0 ∨ (s.m = 2 ∧ s.a ≤ 1)` and
      `Boundary s ↔ s.m ≤ 2`.
- [ ] Prove `astep_isSome_iff : (astep s).isSome ↔ ¬ Dead s` and
      `astep_hydra_of_interior : 3 ≤ s.m → astep s = some ⟨s.a, s.m − 2, s.c + 3⟩`.
- [ ] Prove `SafeOrbitA ↔ ∀ k s, aorbit k = some s → ¬ Dead s` (the
      conjecture is exactly death-set avoidance).

### Task 2: Volley lemma — certified event-skipping (core Lean)

**Files:**
- Modify: `lean/BBChallenge/Incision/Antihydra.lean`

**Steps:**
- [ ] Define `volley : AState → AState` in closed form: from `(a, m, c)`
      with `m ≥ 3`, applying `j = ⌊(m−1)/2⌋ − (parity adjustment)` hydra
      steps lands on the boundary state `(a, m − 2j, c + 3j)` with
      `m − 2j ∈ {1, 2}`; prove `aorbitN j s = some (volley s)` by induction
      on `j` using `astep_hydra_of_interior`.
- [ ] Define the **event process** `estep : AState → Option AState` =
      boundary rule (drop/merge) followed by `volley`, and `eorbit` from the
      first boundary state after `⟨2, 7, 2⟩`.
- [ ] Prove the equivalence theorem:
      `SafeOrbitA ↔ ∀ k, eorbit k ≠ none` — soundness *and* completeness of
      boundary-only checking. This is the theorem the efficiency claim
      rests on.
- [ ] Corollary chained with Set 2:
      `(∀ k, eorbit k ≠ none) → ¬ RawHalts blankStart`.

### Task 3: Event extraction + charts in Python

**Files:**
- Create: `qgkit/bb6/geometry/events.py`, `qgkit/bb6/geometry/charts.py`
- Test: `tests/bb6/test_geometry_events.py`

**Steps:**
- [ ] `extract_events(code, n_events, ...)`: run the *abstract* orbit where
      an exact emulation exists (Antihydra, dossier-1, the stage751 PASS
      machines); fall back to record-level simulation
      (`simulate_records`-style) for the other compact-growth machines.
      Emit per-event rows: index, rule label, pre/post state vector,
      distance-to-death, inter-event raw-step count.
- [ ] Cross-validate against Lean: for Antihydra, the first 1,000 events
      must match `eorbit` exactly (mirror of plan 1's differential-testing
      discipline).
- [ ] `charts.py`: the three embeddings — `log_chart` (componentwise
      `log(1+x)`), `simplex_chart` (projective normalization), and
      `h2_chart` (upper-half-plane: scale ↦ height) — pure functions,
      unit-tested on hand-computed points.

### Task 4: The incision atlas (stage756)

**Files:**
- Create: `experiments/stage756_incision_atlas.py`
- Output: `experiments/outputs/stage756/` (JSONL + PNGs + `atlas.md`)

**Steps:**
- [ ] For Antihydra + dossier-1 + the 51 stage745 compact-growth machines:
      extract ≥10⁴ events (resumable), embed in all three charts, render
      per-machine figures (incision point cloud, distance-to-death vs event
      index, return-time histogram).
- [ ] Metrics per machine: empirical drift and variance of
      distance-to-death, min distance observed, boundedness/escape verdict
      of the normalized cloud, raw-steps-per-event ratio (the measured
      speedup of boundary-only checking).
- [ ] Family comparison: overlay figures within the stage745 delta-rule
      families (e.g. the three `(−2, 3)` machines) and report whether the
      incision figures coincide — the first falsifiable test of the
      geometric hypothesis.
- [ ] Results doc `docs/results/2026-08-XX-incision-atlas.md` with the
      honest-scope section mandatory.

### Task 5: Geometry package + invariant-region attempts (exploratory)

**Files:**
- Create: `lean-geometry/` (new Lake package; mathlib allowed)

**Steps:**
- [ ] Formalize the rational charts (`ℚ`-valued; avoid `ℝ` unless an
      invariance proof genuinely needs it) and the pushforward of `estep`
      through them.
- [ ] From the atlas, shortlist machines whose event cloud shows a candidate
      invariant region `R` at positive distance from the death face
      (Antihydra-class machines are expected to show drift-to-safety only
      *probabilistically* — those are explicitly out of scope for proofs).
- [ ] For each shortlisted machine: state `estep`-invariance of `R` in Lean
      and attempt the proof; any success yields, via Task 2's corollary and
      the Set 2 reduction, an **unconditional** non-halting theorem — which
      would then flow into plan 2's submission pipeline as its own result.
- [ ] Log failures honestly in the results doc; a null result (no provable
      invariant anywhere) is a publishable finding about the cohort.

### Task 6: Feed the speedup back into the discharge pipeline

**Steps:**
- [ ] Where Task 2-style volley lemmas exist, switch the stage753-style
      obligation replays to boundary-event replay (same checks, evaluated
      only at incisions), keeping a raw-replay sample as a control.
- [ ] Measure and report the wall-clock ratio vs the current 10⁸-raw-step
      replays; target: obligations at 10⁹+ raw-step equivalent horizons at
      current cost.

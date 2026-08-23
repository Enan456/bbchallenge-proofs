# Plan 1 — Validate Lean ↔ Rocq parity for the raw TM layer

> **Execution status (2026-08-22):** Task 1 DONE (`packages/bbchallenge/
> Bridge/Format.lean`; certified over `List Char` to keep `[propext]` —
> `String.toList` pulls `Classical.choice`).  Task 2 DONE (`Trace.lean` +
> `tests/lean_parity/`, 4/4 green; deviation: the Python reference is a
> self-contained ~30-line stepper in the test file rather than qgkit — a
> cleaner independence claim).  Task 5 script DONE (`scripts/check_lean.sh`,
> gate OK); CI workflow pending repo publication.  Task 4 DONE (2026-08-23:
> `packages/dossier1/Bridge/Bisimulation.lean` — zipper-tape semantics
> proven step-for-step equivalent to the functional tape;
> `zipper_halts_iff` at `[propext, Quot.sound]`; README gained the
> shoulders-of-giants commentary). Task 3 (pinned Coq-BB5 written
> correspondence) remains open.

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking. **Per user preference, code
> implementation is routed through the Codex rescue agent
> (`codex:codex-rescue`), not general-purpose subagents.**

**Goal:** Establish, with machine-checked and differential evidence, that the
Lean raw-TM layer (Set 1, `docs/learning/01-lean-raw-tm-foundations.md`) is
faithful to the traditional busy-beaver formalization the bbchallenge
community proves in Rocq (Coq-BB5 lineage) — so that a reviewer can accept
`safeOrbitA_nonhalting` / `safeOrbit_nonhalting` as statements about the
*real* machines, not about a private variant.

**Architecture:** Three independent evidence layers, cheapest first:
(1) an in-Lean parser from bbchallenge standard-format code strings to our
transition tables, with `decide`-proved equality against the hand-written
tables; (2) differential trace testing between Lean's `stepN` (made
executable) and the independent Python simulator in `qgkit/`; (3) a written
semantic correspondence against the pinned Rocq definitions, with a stretch
goal of a mechanized bisimulation. New Lean code goes in
`lean/BBChallenge/Parity/`; Python tests in `tests/lean_parity/`.

**Trust rule:** nothing in this plan may weaken the existing axiom story —
`#print axioms` on the two main theorems must keep reporting exactly
`[propext, Quot.sound]` after every task.

---

### Task 1: Standard-format parser + `decide` table equality (in Lean)

The hand-transcribed `instr` tables are the single trust-critical
transcription in the repo. Remove that trust requirement mechanically.

**Files:**
- Create: `lean/BBChallenge/Parity/Format.lean`
- Modify: `lean/BBChallenge.lean` (import)

**Steps:**
- [ ] Implement `parseMachine : String → Option (State → Bool → Option Instr)`
      for the standard format (`_`-separated per-state pairs, `---` = undefined,
      e.g. `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`). Pure, total, core-only.
- [ ] Prove by `decide` (tables are finite):
      `parseMachine antihydraCode = some AntihydraRawTM.instr` and
      `parseMachine dossier1Code = some Dossier1RawTM.instr`.
- [ ] Negative control: a deliberately corrupted code string parses to a table
      provably ≠ `instr` (guards against a vacuously-true parser).
- [ ] `lake build` green; `#print axioms` on both parity theorems reports
      `[propext, Quot.sound]` (`decide` may add `Classical.choice`-free
      `ofReduceBool` if `native_decide` is used — do NOT use `native_decide`).

### Task 2: Executable Lean traces + differential test vs `qgkit`

**Files:**
- Create: `lean/BBChallenge/Parity/Trace.lean` (+ a `lean_exe` target in
  `lean/lakefile.toml` printing `step,state,head,window` lines)
- Create: `tests/lean_parity/test_trace_parity.py`

**Steps:**
- [ ] Lean executable: run `stepN` from `blankStart` for N steps (N=100,000
      per machine), emitting at each step the state, head position, and the
      tape window `[head−16, head+16]` in a stable text format.
- [ ] Python reference: drive the existing `qgkit` simulator (same machines,
      same convention as `simulate_records`) and emit the identical format.
- [ ] Pytest: byte-compare the two traces for both machines, plus two known
      halters (e.g. `1RB1LB_1LA---` BB(2)) checking the halt step matches
      exactly.
- [ ] Also cross-check the two Lean-proved anchor facts empirically:
      Antihydra startup `stepN 62 blankStart` record and dossier-1's 35-step
      startup appear at the same steps in the Python trace.

### Task 3: Written correspondence with the Rocq (Coq-BB5) definitions

**Files:**
- Create: `docs/results/2026-08-XX-lean-rocq-correspondence.md`

**Steps:**
- [ ] Pin the reference: exact repo/commit of the community Rocq development
      consulted (Coq-BB5 / busycoq lineage), quoting its `TM`, step, and
      halting definitions verbatim.
- [ ] Correspondence table: our `Config`/`step`/`RawHalts` vs theirs —
      including representation deltas (functional `Int → Bool` tape vs
      zipper tape; `Option`-monadic step vs relational step) and why each
      delta is semantics-preserving.
- [ ] State precisely what parity does and does not cover (we match the
      *machine semantics*; we do not claim any correspondence for their
      decider infrastructure).

### Task 4 (stretch): Mechanized bisimulation against a zipper-tape model

- [ ] Model a Rocq-style zipper-tape semantics (`left list, current, right
      list` with default blanks) inside Lean, core-only.
- [ ] Define the abstraction map to `Int → Bool` tapes and prove step
      bisimulation: the two semantics simulate each other step-for-step, and
      halting agrees. This makes the parity claim a theorem instead of a
      document.

### Task 5: CI gate

**Files:**
- Create: `scripts/check_lean.sh`; optionally `.github/workflows/ci.yml`

**Steps:**
- [ ] Script: `cd lean && lake build` then fail unless every `#print axioms`
      line in the build log is exactly `[propext, Quot.sound]`; run the
      parity pytest.
- [ ] Wire into CI if/when the repo goes public (plan 2 dependency).

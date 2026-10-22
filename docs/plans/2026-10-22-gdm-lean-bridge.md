# Plan — Lean bridge to Google DeepMind's cryptids reductions (4 colliding machines)

**Goal.** For each of dossier-2, dossier-3, dossier-7, dossier-27, a
kernel-checked theorem connecting this repo's closure to DeepMind's
acceleration, plus a human-readable explanation of the machine. Target
statement per machine (names per our file / their file):

```
theorem bridge : SafeMetaOrbit → ¬ CollatzHalts gdm.next gdm.start
```

derived as `safe*_nonhalting` (ours) ∘ `isHalt_iff_raw` (new) ∘
`isHalt_iff_acceleration` (theirs). The converse is NOT in scope; say so in
every doc that mentions the bridge.

**Ground rules for the loop.**
- One task per iteration. Read this file, take the first unchecked box,
  finish it, verify, tick it, commit with a message starting `bridge(bb6):`,
  push over HTTPS (`git -c credential.helper='!gh auth git-credential' push
  https://github.com/Enan456/bbchallenge-proofs.git main`; SSH port 22 times
  out on this network), then stop.
- Verification before ticking: `lake build` of the package touched must
  succeed, and every new theorem must `#print axioms` to a subset of
  `[propext, Classical.choice, Quot.sound]`. No `sorry` anywhere tracked.
- If a task turns out blocked, do not skip ahead silently: write the blocker
  under "Blockers" below, tick nothing, commit the note, stop.
- Explanations (tasks 8–11) are written in plain language for a reader who
  knows what a Turing machine is and nothing else; cite the Lean names, never
  paste Lean.
- Do not post anything to Discord, the forum, or the wiki, and do not open
  PRs upstream. Those are the author's calls.

## Tasks

### Phase 0 — toolchain spike
- [x] **T1.** Install `leanprover/lean4:v4.35.0-rc4` via elan. Copy
  `busy-beaver-core/` to a scratch dir, set its `lean-toolchain` to 4.35.0-rc4,
  run `lake build`. Record in "Spike log" whether the 119-job core build
  passes unchanged on 4.35 and, if not, the first error. Do not modify the
  real `busy-beaver-core/` yet.
- [ ] **T2.** Create `packages/gdm-bridge/` (Lean 4.35.0-rc4) with a
  `lakefile.toml` requiring (a) `google-deepmind/cryptids` from GitHub at the
  commit of PR #9 (2026-10-20) and (b) `busy-beaver-core` by path
  (`../../busy-beaver-core`; if T1 showed 4.35 breaks the core, fix the core
  on 4.35 first, in place, keeping 4.30 compatibility if possible, and note
  it). `lake exe cache get`, then `lake build` a `Smoke.lean` that imports
  both `BusyBeaver.BB6.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD` and
  `BusyBeaverCore.Dossier2RawTM` and states nothing. Record build time and
  Mathlib cache size in "Spike log".

### Phase 1 — dossier-2 bridge
- [ ] **T3.** `packages/gdm-bridge/GdmBridge/Dossier2/Machine.lean`: prove
  that their `machine` (from `load_rle_machine%`) and our `instr` table agree
  as functions `State × Bool → Option (State × Bool × Dir)` under an explicit
  bijection `Fin 6 ≃ QIG.Dossier2RawTM.State` and `Fin 2 ≃ Bool`. Reuse
  `packages/dossier1/Bridge/Format.lean`'s parser-parity approach where it
  helps.
- [ ] **T4.** `.../Dossier2/Bisim.lean`: a translation `toCfg : Config →
  BusyBeaver.Cfg (Fin 2) (Fin 6)` (our `Int → Bool` tape to Mathlib's
  `Turing.Tape` zipper, head at the zipper focus) and the step lemma
  `toCfg_step : (step c).map toCfg = BusyBeaver.step target (toCfg c)`.
  Mirror the structure of `packages/dossier1/Bridge/Bisimulation.lean`.
- [ ] **T5.** `.../Dossier2/Halting.lean`: `isHalt_iff_raw :
  BusyBeaver.IsHalt target ↔ RawHalts blankStart`, by induction on the
  step count from `toCfg blankStart = init []`.
- [ ] **T6.** `.../Dossier2/Bridge.lean`: `bridge_d2 : SafeMetaOrbit → ¬
  BusyBeaver.CollatzHalts next start`, from
  `dossier2_nonhalting_of_safeMetaOrbit`, `isHalt_iff_raw`, and their
  `isHalt_iff_acceleration`. `#print axioms bridge_d2`. Add a test in
  `tests/lean_parity/` that runs their `next` and our `metaStep` (via the
  existing Python ports) and checks the composed statement is at least
  consistent for 10⁶ raw steps (it already is; the test pins it).

### Phase 2 — replicate
- [ ] **T7.** Factor T3–T5 into a machine-generic `GdmBridge/Generic.lean`
  (parameterised by the two transition tables and the bijection), then
  instantiate `bridge_d3`, `bridge_d7`, `bridge_d27`. The word-engine
  machines (d7, d27) use `SafeD7Orbit` / `SafeD27Orbit` in place of
  `SafeMetaOrbit`. All four must `#print axioms` clean.

### Phase 3 — explain (the part that matters)
- [ ] **T8.** `docs/explanations/dossier-2.md`: what the tape looks like in
  the recurring phase, what the five integers of our `MetaState` measure,
  what Google's three counters `C(a,b,c)` measure, how the two sampling
  points relate (we sample at `D`-state spawn entries, they sample at
  `E>` configurations), what the fatal set is in both pictures and why the
  machine halts within tens of steps once it is entered, and what is known
  to NOT work (no congruence invariant to mod 384, no rotation rigidity;
  cite `docs/results/2026-08-26-renewal-map-analysis.md`). End with the one
  open question stated in plain words.
- [ ] **T9.** `docs/explanations/dossier-3.md`: same, written as "the mirror
  of dossier-2" with the differences made explicit, and a note on why
  Google's `next` here skips thousands of canonical configurations (what a
  "sweep cascade" is on this tape).
- [ ] **T10.** `docs/explanations/dossier-7.md`: the ladder picture, what a
  record (fresh left extreme) is, what Google's `C/M/L` families are in that
  picture, the `d ∈ {3,6}` identity, and the fatal `L(0,2k,d)` case.
- [ ] **T11.** `docs/explanations/dossier-27.md`: the `U4 = 1100` block
  stack, Google's five families, why their `R2` rule triples the stack (so
  abstract steps are rare), the 66-vs-169 docstring note, and our record
  orbit's view of the same growth.
- [ ] **T12.** Update `README.md` "October 2026 update" with the four bridge
  theorems and links to `docs/explanations/`, and update
  `docs/results/2026-10-22-gdm-cross-verification.md` "Non-claims" to say the
  one-directional Lean bridge now exists.

## Spike log

- **T1 (2026-10-22).** Toolchain `leanprover/lean4:v4.35.0-rc4` (exact
  version exists; installed via elan alongside 4.30.0). Copied
  `busy-beaver-core/` (minus `.lake/`) to a scratch dir, set
  `lean-toolchain` to 4.35.0-rc4, ran `lake build` from cold. **Passed
  unchanged**: `Build completed successfully (119 jobs)`, exit 0, wall time
  741 s (~12.4 min; the three big `Dossier{1,2,3}RawTM` files dominate).
  Zero errors. 121 deprecation warnings, all of one kind: `if_pos` (68) and
  `if_neg` (53) are deprecated in 4.35 in favour of `ite_eq_left` /
  `ite_eq_right`, across `Dossier2RawTM.lean` (47), `Dossier3RawTM.lean`
  (47), `Dossier1RawTM.lean` (17), `AntihydraRawTM.lean` (10). Every
  `#print axioms` still reports `[propext, Quot.sound]`. Consequence for T2:
  the core can be required by path from a 4.35 package with no source
  changes; the `if_pos`/`if_neg` rename is cosmetic and can be done later
  (or left, since 4.30 compatibility is wanted). Real `busy-beaver-core/`
  untouched.

## Blockers

(none yet)

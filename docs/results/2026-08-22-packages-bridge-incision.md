# Packages split, parity layer, incision theorem, hydra bridge (2026-08-22)

**Scope:** execution of the core tasks of plans 1–3
(`docs/plans/2026-08-22-plan*.md`) in the new `packages/` architecture.
The pre-existing trust base (`lean/`) is byte-untouched.

## New Lean packages

```
packages/bbchallenge   (requires ../lean; core-only)
  Bridge/Format.lean      parser + table-equality theorems
  Bridge/Incision.lean    death set, volley, event-process equivalence
  Bridge/Conjecture.lean  the 1-D hydra bridge
  Trace.lean              differential-trace executable
packages/extensions    (requires packages/bbchallenge; core-only so far)
  Extensions/Charts.lean  exact chart definitions (simplex, log2, ℍ²-surrogate)
```

`scripts/check_lean.sh` builds all three packages and enforces the axiom
gate: **every theorem is at `[propext, Quot.sound]` or below** (the parser
theorems are at `[propext]` alone), with the single documented exception of
the two quarantined `*_code_chars` String-display lemmas
(`Classical.choice` via `String.toList` internals).  Gate status: **OK**.
No sorry anywhere.

## Headline theorems (all machine-checked today)

1. **Parser parity** (`Bridge/Format.lean`): `parse_ok` — the bbchallenge
   standard-format codes of Antihydra and dossier-1, parsed by a total
   in-Lean parser, equal the hand-written `instr` tables (by kernel
   `decide` over `List Char`; corrupted-code negative controls;
   `instr_unique` via encoding injectivity).  The one trust-critical
   transcription of the development is now mechanically checked.
2. **The incision theorem** (`Bridge/Incision.lean`):
   `eventSafe_iff_safeOrbitA` — the Antihydra abstract orbit sampled only
   at *incision events* (boundary states `m ≤ 2`, one event per counter
   movement, intervening hydra volleys collapsed by the closed-form
   `volley`) dies **iff** the full orbit dies.  Boundary-only checking is
   certified sound *and* complete; `eventSafe_nonhalting` chains it to the
   machine.
3. **The hydra bridge** (`Bridge/Conjecture.lean`):
   `hydraSafe_iff_safeOrbitA` and `hydraSafe_nonhalting` — the orbit
   conjecture is *equivalent* to the 1-D system in the community's own
   shape: `b ↦ b + ⌊b/2⌋` from `b = 12 = H(8)`, heads counter from 2, `+2`
   on even / `−1` on odd.  The conjugacy is `b = m + 2·(c−2)/3 + 5` with
   machine counter `a` = hydra heads, proved step-for-step (`relHA_step`).
   Documented honest delta vs the BusyBeaverWiki statement (fetched and
   pinned today): our death fires at heads `≤ 1` where the wiki's fires at
   `= 0` — the tape grammar needs a non-empty counter block, so `HydraSafe`
   is possibly strictly stronger; closing that one boundary case is
   follow-up work.

## Differential validation (plan 1, task 2)

`packages/bbchallenge`'s `trace` executable runs the *proved* `step`
semantics; `tests/lean_parity/` re-implements standard-format semantics
independently (~30 lines, no shared code) and byte-compares: **2,000-step
traces identical for both machines**; the proved startup anchors (Antihydra
step 62 → `B@6`, dossier-1 step 35 → `E@5`) hold in the independent trace;
BB(2) halter control passes.  4/4 tests green.

## stage756 — the incision atlas (plan 3, tasks 3–4)

`qgkit/bb6/geometry/` + `experiments/stage756_incision_atlas.py`; outputs in
`experiments/outputs/stage756/`.  6/6 module tests green (including the
cross-check that Python event 0 equals the Lean `eorbit 0 = ⟨2, 1, 11⟩`,
`b = 12`, and that reconstructed events satisfy the Lean boundary
invariants `m ∈ {1,2}`, `c ≡ 2 (mod 3)`).

Exact certified mode (Antihydra, 20,000 events):

- rules: 9,972 merges / 10,028 drops; heads counter 2 → 9,919 with clean
  ≈ +0.5/event drift (the theoretical random-walk expectation);
- **min death margin 4** — after startup the orbit never comes within 4
  units of the death condition in 20k events;
- **acceleration measured:** the first 10⁸ raw steps are covered by just
  **16 incision events**; the full 20k events are raw-step-equivalent to
  ≈ 10^7046 steps.  Boundary-only checking is not an optimization, it is a
  different regime.

Record-heuristic mode (9 stage753-queue machines, 200k steps): all
non-halting within budget; family structure visible — three machines share
a dims-tail ≈ 3.47–3.49 near-collapse profile and two share 7.25, matching
the delta-rule families flagged in stage745.

Chart finding (honest): in the raw simplex / ℍ²-surrogate charts the orbit
degenerates toward the `c`-vertex (as `c ~ 1.5^k` dwarfs everything);
the informative margin coordinate is the heads counter.  Log-scaled simplex
charts are the needed refinement before any invariant-region hunting
(plan 3, task 5).

## Repairs and environment

- `qgkit/bb6/vcollatz/__init__.py` shipped broken in this packaged repo
  (imports `.reversible`, not copied from the parent); now guarded.  5
  remaining failures in `tests/bb6/test_vcollatz_classify.py` are the same
  packaging gap (`qgkit.bb6.bbchallenge` decider chain not copied) — they
  predate today and are *not* regressions; noted for plan 2 repo hardening.
- Toolchain installed from scratch (elan 4.2.3, Lean `v4.30.0-rc2` per the
  repo pin); `lean/` baseline builds in ~15 s, axioms clean.
- Python venv `.venv` (system-site numpy/tqdm + pytest, matplotlib).

## Lessons recorded

- `omega` given a *positive* compound (∧/∨) goal emits proofs using
  `Classical.choice`; feeding it atomic goals (split via `constructor`,
  `congr 1`, explicit `Or.inl`) keeps `[propext, Quot.sound]`.
- `String.toList` transitively references `Classical.choice`; certified
  `decide` statements should be over `List Char` literals.

## Honest scope

Nothing here decides any machine.  The new theorems are reductions and
equivalences; the atlas is bounded empirical structure; `HydraSafe` remains
an open conjecture.

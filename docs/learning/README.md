# Learning docs — the three-set architecture

This folder explains the Lean proof program as three consolidated sets, each
with its own trust story and its own plan in `docs/plans/`:

| Set | Doc | What it is | Status |
|---|---|---|---|
| 1 | [01-lean-raw-tm-foundations.md](01-lean-raw-tm-foundations.md) | The traditional busy-beaver formal layer: raw TM semantics in core Lean, mirroring the Rocq (Coq-BB5) tradition the bbchallenge community proves in | Built (duplicated per machine; consolidation planned) |
| 2 | [02-collapse-emulation-across-bb6.md](02-collapse-emulation-across-bb6.md) | The bbchallenge program: exact macro emulation of collapse-like record dynamics across the BB(6) open set, and the machine-checked reductions built on it | Two machines reduced end-to-end (Antihydra, dossier-1) |
| 3 | [03-noneuclidean-incision-geometry.md](03-noneuclidean-incision-geometry.md) | The proposed geometric layer: plotting where "incision" (orbit-death / halt-opportunity) events occur in a non-Euclidean coordinate system, and checking only at those boundaries | Research program — not yet started |

Corresponding action plans:

1. `docs/plans/2026-08-22-plan1-lean-rocq-parity.md` — validate parity of the
   Lean layer with the Rocq tradition.
2. `docs/plans/2026-08-22-plan2-bbchallenge-submission.md` — package and
   submit what is already proven.
3. `docs/plans/2026-08-22-plan3-noneuclidean-incision-geometry.md` — build the
   geometric incision-detection layer.

## Execution artifacts (2026-08-22)

The core tasks of all three plans are implemented in the `packages/` split
(see `packages/README.md`):

- **Plan 1**: `packages/dossier1/Bridge/Format.lean` (parser +
  `decide`-proved table equality, axioms `[propext]`), the `trace`
  executable + `tests/lean_parity/` differential tests (4/4 passing).
- **Plan 2**: `packages/dossier1/Bridge/Conjecture.lean` — the bridge
  `hydraSafe_iff_safeOrbitA` / `hydraSafe_nonhalting` to the community's 1-D
  hydra recurrence; `docs/submissions/statement-of-claims.md`.
- **Plan 3**: `packages/dossier1/Bridge/Incision.lean` — the certified
  boundary-only-checking theorem `eventSafe_iff_safeOrbitA`;
  `packages/flying-dragon/` (exact charts); `qgkit/bb6/geometry/` +
  `experiments/stage756_incision_atlas.py` (the empirical atlas).
- Gate: `scripts/check_lean.sh` (build + axiom check for all three
  packages).  Results: `docs/results/2026-08-22-packages-bridge-incision.md`.

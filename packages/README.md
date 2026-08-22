# packages/ — the Lean package split

Three-package architecture (see `docs/learning/README.md` for the map):

| package | trust bar | depends on | contents |
|---|---|---|---|
| `../lean` | `[propext, Quot.sound]`, core-only | — | Sets 1–2: raw TM semantics + the machine reductions (`safeOrbitA_nonhalting`, `safeOrbit_nonhalting`).  **Untouched by everything below.** |
| `bbchallenge/` | `[propext, Quot.sound]`, core-only | `../lean` | the certified bridge layer: `Bridge/Format.lean` (standard-format parser, `decide`-proved equal to the hand-written tables), `Bridge/Incision.lean` (death set, volley, `eventSafe_iff_safeOrbitA`), `Bridge/Conjecture.lean` (the 1-D hydra bridge: `hydraSafe_nonhalting`), and the `trace` differential-test executable |
| `extensions/` | `[propext]` so far; may adopt mathlib later | `bbchallenge/` | Set 3 geometry: exact chart definitions mirrored by `qgkit/bb6/geometry`.  Never imported by the certified packages |

Build everything with the axiom gate:

```sh
scripts/check_lean.sh
```

Known, documented exception: the two `*_code_chars` display lemmas in
`Bridge/Format.lean` additionally report `Classical.choice` (via
`String.toList` internals); the certified statements are over `List Char`
literals and stay clean.

Differential parity test (Lean `step` vs an independent Python stepper):

```sh
cd packages/bbchallenge && lake build trace
python3 -m pytest tests/lean_parity/ -v   # from the repo root
```

## Palomar registry entries

`bbchallenge/Palomar/` packages the three headline results as
[Palomar](https://palomar-registry.org/) Challenge/Solution pairs (one entry
per `comparator-*.json`; per-entry metadata under `palomar-meta/`), each
Challenge self-contained over Lean core and each Solution proving it by
transport from the certified development.  Local pre-flight:

```sh
./.venv/bin/python scripts/check_palomar.py
```

Status: mechanically submission-ready; blocked on a root LICENSE choice,
a push to the public remote, and owner sign-off.  See
`docs/results/2026-08-22-palomar-validation.md`.

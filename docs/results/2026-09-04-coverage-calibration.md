# Coverage calibration: the true closable hit-rate of the raw-step generator

**Date:** 2026-09-04 · **Harness:** `qgkit/bb6/coverage_calibration.py` ·
**Generator under test:** `qgkit/bb6/rawstep_generator.py` ·
**Gate:** the generator's own in-memory differential — the 20-million raw-step
exact fail-closed record-mirror check, identical surgery to the emitted
`dossier{N}_mirror.py`.

Everything below is a **measurement** of the generator's mechanical behaviour
on a reproducible sample. Nothing here is a proof, and no closure is claimed:
a PASS means the generator emitted its seven artifacts and its own
differential gate held over the horizon — the Lean kernel is what would
ultimately certify each machine. No machine halted.

## Question

`experiments/outputs/audit_openset.jsonl` marks **795** holdouts
`verdict == "ENGINE_READY"`. Only ~109 are actually closed (the generated
raw-step dossiers plus a few hand-built / named machines). Of the untouched
engine-ready machines, what fraction does the generator actually close
*cleanly*?

## Method

1. Loaded the 795 `ENGINE_READY` rows.
2. Excluded already-closed machines by cross-referencing TM codes found in the
   committed `qgkit/bb6/dossier*_mirror.py`, `packages/dossier1/**` and
   `busy-beaver-core/BusyBeaverCore/*RawTM.lean`. This maps **73** closed codes
   — a best-effort floor, not the full ~109 (the unmapped ~36 are hand-built /
   named machines whose codes did not appear in a parseable form; they are
   themselves closeable, so their presence in the pool does not bias the
   *closeability* rate, only the "untouched" label). This leaves **722** rows
   in the pool.
3. Deterministic, reproducible sample: **every 15th** row of the pool in fixed
   file order → **49 machines**. (No RNG; re-running reproduces the same
   sample.)
4. For each machine: derived orientation from the audit `record_side`, ran the
   generator **end-to-end** (`emit_all` → all seven artifacts written to a
   scratch dir, never into `packages/` or `busy-beaver-core/`), then ran the
   generator's differential gate at a **20,000,000** raw-step horizon (exact
   record-by-record agreement between the raw machine and the fail-closed word
   orbit, state `P` never reads its fatal cell, quadratic fuel never
   exhausted). A per-machine 120 s wall-clock cap guards against a slow
   machine stalling the sweep.

## Result

| verdict | count | share |
|---|---|---|
| **PASS** (clean, full 20M horizon) | **47** | **95.9%** |
| PASS_TIMEOUT (no failure within 120 s, partial horizon) | 1 | 2.0% |
| SKIP_SPLITDOOR (generator declined — exotic corridor) | 1 | 2.0% |
| FAIL (any gate tripped) | 0 | 0.0% |
| **HALTS** | **0** | **0.0%** |

**True clean hit-rate: 47 / 49 = 95.9%.**

- **0 halts.** No machine reached its fatal probe in 20M steps; no `raw halt` /
  `probe unsafe` assertion fired anywhere in the sample.
- **0 FAILs.** No orbit death, no fuel exhaustion, no record mismatch. The
  47 clean passes each agreed exactly on every record over 20M raw steps; the
  worst-case quadratic-fuel fraction observed was **0.844 < 1.0** (one machine
  ran close to the fuel ceiling but never hit it), median record count ~4,500,
  up to 12,334 records.
- The 47 passes are evenly spread across the generator's design space:
  24 right-growers / 23 left-growers; 26 `general` (two-sided) / 21
  `specialized` (one-sided) variants. The push-button engine is not carrying
  only one corner of the corpus.

### The one SKIP

`1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD` — probe `C0`, entered by two doors
`B0` (pop, L) and `F0` (push, R). The two doors share **neither** a direction
**nor** a source state, so `gen_corridor` raises `NotImplementedError` by
design rather than emit an unvalidated corridor lemma. This is the
"split-door corridor" case the task anticipated: a genuine, honest decline,
not a failure — the closure keystone does not even need the corridor lemma, so
such a machine is hand-authorable, just not push-button.

### The one PASS_TIMEOUT

`1RB1RF_0RC1RD_1LC1LA_0LE1RE_1RA0RB_---0LC` — probe `F0`, single door `A1`
(pop, R). The differential produced **no failure of any kind** but did not
finish the full 20M horizon within the 120 s cap (its per-record word-fuel
replay is heavier). It is a very likely PASS whose full-horizon confirmation
just needs more wall-clock; it is deliberately **not** counted in the 95.9%
clean rate. Counting it as "no failure observed" would give 48/49 = 98.0%.

## Extrapolation (with caveat)

Point estimate of the clean closable fraction: **95.9%**.
Wilson 95% score interval (n = 49, k = 47): **[86.3%, 98.9%]**.

Applied to the **~686** truly-untouched engine-ready machines (795 − ~109):

- **Point estimate: ~658 clean closures** (686 × 0.959).
- **95% interval: ~592 – 678.**
- If the pool is instead the 722 measured here (i.e. counting the ~36 unmapped
  closed machines as still open): point ~693, interval ~623 – 714.

**Honesty caveat.** (a) This measures the generator's *mechanical* gate — full
Lean kernel checking of each emitted closure is a separate, un-run step; a
differential PASS is necessary, not sufficient, for a real closure. (b) The
sample is a fixed deterministic slice, not an independent random draw; the CI
treats it as if it were, so read it as an indicative band, not a guarantee.
(c) The pool still contains ~36 already-closed machines that could not be
excluded (they only cost sample slots and, being closeable, don't bias the
rate). (d) The 20M horizon is a bounded observation: a machine that first
halts or exhausts fuel only after 20M steps would be scored PASS here. No such
late failure is expected among audited engine-ready holdouts, but it is not
excluded. (e) SKIP rate (split-door corridors) is ~2% here; over the full
population it could differ, which would trade PASSes for SKIPs (declines),
never for undetected halts.

## Bottom line

- **Hit-rate: 47/49 = 95.9% clean full-horizon closure candidates.**
- **Breakdown: 47 PASS, 1 PASS_TIMEOUT (no failure, partial), 1 SKIP
  (split-door corridor), 0 FAIL, 0 HALT.**
- **Extrapolated clean closable count over ~686 untouched: ~658
  (95% band ~592–678).**
- **No halts detected anywhere in the sample.**

Reproduce with:
`SCRATCH=<dir> python3 qgkit/bb6/coverage_calibration.py --horizon 20000000 --stride 15 --timeout 120 --closed <closed_codes.txt>`

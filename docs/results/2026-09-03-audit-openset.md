# Audit of the open set: the near-term closable denominator

**Date:** 2026-09-03. **Harness:** `qgkit/bb6/audit_openset.py`.
**Output:** `experiments/outputs/audit_openset.jsonl` (one row per open
machine). **Bands:** imported from `qgkit/bb6/census_bands.py`. This is
forward-plan phase 1.1: classify every open BB(6) machine by whether the
raw-step closure engine can close it, without closing anything.

## What the harness measures

The open set is the 1,094 codes of `experiments/outputs/d4_fullsweep.jsonl`
minus the 18 already closed (Antihydra plus the seventeen
`*RawTM.lean` machines), leaving 1,076 machines. Each machine gets one
raw simulation to 2x10^7 steps (a multiprocessing pool of six; the step
budget bounds per-machine runtime). Four axes are decided, all
fail-closed:

1. **Halt check.** A halt within 20M steps records verdict HALTS with
   the step. This would be a genuine finding and excludes the machine
   from the rest.
2. **Sidedness.** Left and right extremes are tracked. A side counts as
   advancing when it still sets fresh extremes in the second half of the
   run and its extent exceeds a small cap. The machine is one-sided-right,
   one-sided-left, two-sided, or bounded (neither side advances, the
   signature of a translated cycler or in-place cycle, out of scope for a
   record engine). For a two-sided machine the record side is the extreme
   with fewer distinct arrival states, the side the engine would pick.
3. **Probe benignity.** Structural, read from the table by working
   backward one step from the undefined transition. A halt-is-probe case
   (the undefined state and read are themselves the fatal event) gives
   one-cell safety, as in dossier-9 and dossier-14. A neighbour-guarded
   case gives two-cell safety, as in dossier-7. The rule marks a machine
   two-cell when it dies reading a 0 (a one-cell predicate on the
   undefined state would be violated at every blank cell) or when it dies
   reading a 1 as a single-predecessor satellite whose safe branch returns
   to that predecessor (the array-class case, rank-1). It marks one-cell
   otherwise. This rule reproduces all eighteen certified corridors.
4. **Fuel growth.** Records are fresh-extreme events on the growing side.
   The harness measures the maximum record-to-record step gap and the word
   length (tape extent) at that gap. Fuel is sound when the gap stays
   within the standard quadratic budget 64*(len+64)^2. A gap that exceeds
   it grows faster than quadratic and needs a bigger fuel form.

The probe axis is reported but does not gate the verdict: eight of the
eighteen known closures are two-cell and all are closed, so a neighbour
guard is within the engine's reach. The verdict is gated by sidedness
(bounded gives OUT_OF_SCOPE) and by fuel (super-quadratic gives
ENGINE_READY_WITH_WORK).

## Verdict histogram

| verdict | count |
|---|---:|
| ENGINE_READY | 795 |
| ENGINE_READY_WITH_WORK | 268 |
| OUT_OF_SCOPE | 13 |
| HALTS | 0 |
| total | 1,076 |

The engine-ready count, 795, is the true near-term closable denominator:
the machines whose sidedness gives a growing frontier and whose record
gaps fit the standard quadratic fuel, so the existing raw-step engine
applies without a new record notion or a new fuel form.

## Verdict cross-tabulated against the census bands

Bands are the pinned definitions from `census_bands.py` (structured is
`laws == 1 and nreg >= 3`, multi_law is `laws > 1`, unstructured is the
rest).

| band | ENGINE_READY | WITH_WORK | OUT_OF_SCOPE | HALTS | total (open) |
|---|---:|---:|---:|---:|---:|
| structured | 223 | 21 | 0 | 0 | 244 |
| multi_law | 39 | 0 | 0 | 0 | 39 |
| unstructured | 533 | 247 | 13 | 0 | 793 |

The structured band is the cleanest: no bounded machines, and only 21 of
244 need a bigger fuel form. The multi-law band is entirely engine-ready.
Both fuel failures and the thirteen out-of-scope machines concentrate in
the unstructured band, as expected of the unmodeled cohort.

## Engine-ready inside the structured and EXACT cohorts

- **262-structured band.** 244 of the 262 are open (the other 18 are the
  known closures, all structured). Of the 244 open, 223 are ENGINE_READY.
  Counting the 18 closures, which every one classifies ENGINE_READY under
  this audit, 241 of the 262 structured machines are engine-ready.
- **EXACT set (`sweep251_results.jsonl`).** Of the 63 EXACT machines, 7
  are among the closures, leaving 56 open. All 56 classify ENGINE_READY.
- **Degenerate-EXACT cohort.** The sweep report's degenerate-fit class is
  the EXACT machines whose fit reuses no rule more than twice
  (top_support at most 2, the "support 1-2" memorization specs; the
  forward plan's approximately 43 degenerate-fit EXACTs, the residue of
  the 63 EXACT after the 20 directly-probed compact-spec machines). Under
  the reproducible top_support threshold this cohort is 45 machines. All
  45 classify ENGINE_READY.

Every high-confidence structured cohort is fully or nearly fully
engine-ready. The near-term batch-close target (forward-plan phase 2.2)
is not blocked by sidedness, probe, or fuel for any EXACT machine.

## Halt findings

None. No open machine halts within the 20M-step horizon.

## The axis distributions

Sidedness over the 1,076 open machines: two-sided 476, one-sided-right
317, one-sided-left 270, bounded 13. The record engine has a growing
frontier on 1,063 of the 1,076.

Probe kind over the 1,073 non-halting machines with a single undefined
transition: one-cell 687, two-cell 386. Three further machines carry two
undefined transitions and are reported with probe kind anomalous
(`1RB---_1RC---_1RD1LC_1LE1RF_1LC0LE_1RA0RD`,
`1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`,
`1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---`); their other axes are
classified normally. A two-probe corridor is a small extra obligation for
the generator, not a barrier.

The 268 fuel failures share a clear signature: the maximum gap occurs at
a small word length (49 to 261 cells, median 146) with a gap in the
millions of steps. These machines perform heavy bounded computation
between sparse frontier extensions, so the frontier-extreme record notion
allocates far too little fuel. A cubic fuel form covers every observed
case, which is why the verdict is ENGINE_READY_WITH_WORK rather than
OUT_OF_SCOPE. The engine-ready machines, by contrast, reach their maximum
gap at word lengths in the thousands, the array-class growth the engine
already handles.

## Self-check: the eighteen known closures

The audit's sidedness, probe, and fuel axes are necessary-not-sufficient
heuristics for closability. Their validity rests on the fact that every
already-closed machine must classify ENGINE_READY under this audit. It
does. All eighteen known closures classify ENGINE_READY, and every one of
the eighteen probe kinds matches its certified corridor lemma (ten
one-cell `_read_1` corridors for dossiers 9 through 18, eight two-cell
`_probe` corridors for dossiers 1, 2, 3, 7, 8, Dvisetu, Antihydra, and
rank-1). Run `python3 qgkit/bb6/audit_openset.py --selfcheck` to
reproduce. The two-sided closures (dossiers 2, 3, 12, 14 through 18,
rank-1) carry the largest record gaps among the eighteen, up to 13.0M
steps at word length 6,456 for dossier-12, and all remain within the
quadratic budget.

## Scope note

The horizon is 20M raw steps. A machine that halts, changes sidedness, or
first exceeds quadratic fuel only past that horizon would be misread; the
verdict is a 20M-step snapshot, not a proof. The three structural axes are
heuristics for closability, not a closure: ENGINE_READY means the engine's
three preconditions hold at this horizon, not that a Lean proof exists.
The self-check against the eighteen closures is the calibration that these
heuristics do not exclude a genuinely closable machine.

Two known limitations are recorded rather than hidden. First, a translated
cycler drifts steadily on one side and is classified one-sided, not
bounded; its constant record gaps pass the fuel test, so a residual
translated-cycler population may sit inside the 795 engine-ready count and
would need a cycle detector to separate. The bounded verdict catches only
in-place cyclers, of which there are 13. Second, the fuel axis reads a
super-quadratic gap at any word length as needing a bigger fuel form,
including gaps that arise from a long startup transient; this is the
fail-closed reading, and it can only under-count engine-ready machines,
never over-count them.

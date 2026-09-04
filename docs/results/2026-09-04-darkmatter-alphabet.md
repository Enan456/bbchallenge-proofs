# Dark-matter alphabet survey: how much of the "unstructured" band is secretly fixed-dimensional?

**Date:** 2026-09-04 · **Harness:** `qgkit/bb6/darkmatter_alphabet.py` ·
**Band source:** `qgkit/bb6/census_bands.py` over
`experiments/outputs/d4_fullsweep.jsonl` · **Simulator:** the project's
generic raw BB(6) stepper (blank tape, `st='A'`, `hd=0`, fail-closed the
instant a `---` transition is read), the same loop as `dossier4.regimes` /
`cone_sweep.align_run`.

> Everything below is a **measurement** on a reproducible sample. Nothing here
> is a proof and no closure is claimed. A machine landing in class (a) is a
> *closability lead* — a fixed-dimension affine macro-law that the raw-step
> generator could plausibly close — not a decided machine. **No machine
> halted** in any run (horizons up to 5·10⁷; see the halt note below).

## Halt note (fail-closed, checked first)

**Zero halts.** Across the 40-machine survey at horizon 3·10⁷, the four
persistence re-runs at horizon 5·10⁷, and every positive-control run, no
machine ever read a `---` transition. The simulator fails closed (it stops and
reports the step) the instant one is read; none was.

## Question

The census (`census_bands.py`, frozen 2026-09-03) buckets the 1,094 BB(6)
holdouts as `structured` (262), `multi_law` (39), and **`unstructured` (793)**.
The unstructured predicate is exactly

```
band == unstructured  ⇔  not (laws > 1)  and  not (laws == 1 and nreg >= 3)
```

i.e. no single affine regime law fit **in the raw {0,1} alphabet** on the
record-event *time* sequence. The alphabet-artifact lesson from the dossier
corpus: several machines that looked array-class / horizonless were actually
**fixed-dimension** once the tape was re-encoded in the right period-`k` block
alphabet. Nobody had run that natural-alphabet search across the 793. This did.

## Method

1. Pulled the 793 unstructured codes via the pinned `band()` predicate.
2. **Deterministic sample of 40**, evenly spaced across the band in census
   file order: indices `[(i*793)//40 for i in range(40)]`. Same `n` ⇒ same
   machine list, every run.
3. For each machine, ran the generic raw simulator from blank tape to a long
   horizon (survey 3·10⁷; persistence checks 5·10⁷), fail-closed on halt.
4. A **record event** = the head reaches a fresh extreme (`hd>hi or hd<lo`),
   exactly the `dossier4.regimes` event stream. Over a full-granularity sliding
   window of the last 400 *consecutive* record events (a second raw pass, so a
   head-sweep phase is not aliased away by decimation), snapshotted the tape
   region `[lo..hi]` and, for every period `k ∈ {1..6}` and every block phase,
   computed the **macro-state**: the block-symbol histogram (a fixed-dimension
   vector, boundary blocks included) plus the run-length-encoded (RLE) skeleton
   length.
5. **FIXED-DIM-IN-ALPHABET(k)** ⇔ on the end-anchored window, for some head-
   sweep stride `s ∈ {1..16}`, every stride-`s` phase subsequence of the
   macro-state vector has a **constant first difference** (an affine recurrence)
   over a run of ≥ 8 snapshots per phase, and a hold-out (delta fit on the first
   half predicts the second half exactly, all coordinates, exact integers)
   confirms it. The RLE skeleton slope is reported as a *quality* flag (bounded
   ⇒ clean single skeleton; growing ⇒ count-affine but positionally scattered),
   not as a gate.

### Detector calibration (honest scope)

The detector was tuned against known positives and negatives, not asserted:

* **Fires** on hand-proven one-sided growers from the dossier corpus (e.g.
  `1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---`, `1RB0LD_1RC0LC_1LA1RC_..._0RA0RE`
  — dim-2 laws at stride 4) and on census-`structured` counters.
* **Rejects** genuinely chaotic tapes: e.g. a machine whose whole-tape 0-count
  swings 136→581→270 between record events registers no affine law at any `k`.
* **Known false negative:** dossier-19 (`1RB0LE_0RC---_1RD0LA_..._0RC1LC`) is
  proven closable, yet its *whole-tape* 0-count has a sawtooth super-structure
  (497→490→jump→493…) with no clean period ≤ 16, because the histogram
  conflates a fixed startup region with a migrating boundary. The detector
  misses it.

**Consequence:** the detector is **conservative — high precision, lower
recall.** A class-(a) hit is a strong fixed-dimension witness; class (b)
contains *both* genuine dark matter *and* fixed-dim machines the whole-tape
histogram cannot see (dossier-19-type). The (a) fraction is therefore a
**floor** on how much of the band is secretly structured.

## Result: the (a)/(b)/(c) breakdown (n = 40)

| Class | Count | Fraction |
|---|---|---|
| **(a) FIXED-DIM-IN-ALPHABET** | **11** | 27.5% |
| **(b) HIGHER-RANK / DARK** | **29** | 72.5% |
| **(c) SUSPECTED-HALTING / degenerate** | **0** | 0% |

No machine halted; no machine was degenerate or too wide to analyze.

### (a) The fixed-dimension hits — the alphabet artifact, made precise

All 11 hits are **dim-2 macro-laws** (a growing symbol field over a bounded
scatter of the other symbol) already visible at **k = 1**, but with a
head-sweep **stride the census never tested**:

| stride `s` | # machines |
|---|---|
| 1 | 4 |
| 2 | 2 |
| 4 | 2 |
| 6 | 1 |
| 8 | 1 |
| 16 | 1 |

* **10 of 11 have a *scattered* skeleton** — their raw-alphabet RLE length
  *grows* (the array-class illusion) while the block-symbol *histogram* is
  exactly affine. This is the alphabet artifact in this band: the machines look
  horizonless in the raw run-length view but are 2-dimensional in the
  count view.
* The block re-encodings **corroborate but do not extend**: the same law
  re-expresses at k=2 (6 machines) and k=4 (4 machines), but **no machine in
  the sample was fixed-dim *only* in a k ≥ 2 alphabet.** For the 793-band the
  "secret structure" is chiefly a **stride/period + macro-state-vs-time**
  artifact (the census fit affine on event *times* at stride ≤ 4; these need the
  tape-content histogram and strides up to 16), *not* an exotic-alphabet one.
* 9 of the 11 are high-confidence (constant-difference run ≥ 15 snapshots);
  2 were borderline at 3·10⁷ (run 8–9) and **both firmed up to solid hits at
  5·10⁷** — e.g. `1RB0LC_1RC0RA_1LD1LA_1RE1LD_---1RF_0RD1RA` becomes a clean
  stride-4 law. All four persistence re-runs held at 5·10⁷.

Representative (a) machines:

```
1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF   k=1 dim=2 stride=2  run=120  CLEAN skeleton
1RB0LD_1RC0RA_1RD1RF_1LA0LE_1RE1LD_0RB---   k=1 dim=2 stride=4  run=60   scattered
1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA0RE_0RC---   k=1 dim=2 stride=8  run=30   scattered
1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA   k=1 dim=2 stride=16 run=15   scattered
```

### (b) The dark matter — two textures

Of the 29 class-(b) machines:

* **12 are array-class** — the RLE skeleton *grows* in *every* tested alphabet
  (a genuinely lengthening array of blocks; higher-rank). Example:
  `1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC` (width 7 872 at 3·10⁷).
* **17 are chaotic / higher-rank** — no clean fixed-dim fit and no uniform RLE
  growth; the tape composition varies irregularly. Example:
  `1RB0RC_0LC0LE_1RA0RD_1LB1RF_1LC1LB_0RA---` has an RLE slope of +1.75 at k=1
  collapsing to −0.75 at k=2 — no stable low-dimensional view.

Class (b) is where the conservative-detector caveat bites: an unknown fraction
of these 29 are dossier-19-type fixed-dim machines the whole-tape histogram
cannot resolve. So (b) is an **upper bound** on genuine dark matter.

## Extrapolation to the full band

At 11/40 = **27.5%**, a binomial 95% interval (n = 40) is
[13.7%, 41.3%]. Scaled to the 793 unstructured machines:

* **Point estimate: ≈ 218** are secretly fixed-dimensional (closable leads).
* **95% interval: ≈ 108–328.**
* Because the detector is conservative (misses dossier-19-type structure),
  **~218 is a floor**: *at least* roughly a quarter of the "dark matter" is
  secretly structured, and the true fraction is plausibly higher.

Correspondingly, **at most ≈ 575** of the 793 (72.5%, upper bound) are genuine
higher-rank / array-class dark matter — split in this sample roughly evenly
between clean array-class (≈ 30% of the band) and irregular/chaotic
(≈ 43% of the band).

## Honesty note

* All figures are measurements of a mechanical detector on a 40-machine
  deterministic slice, not proofs. "Fixed-dim" here means the block-symbol
  histogram obeys a constant-first-difference (affine) recurrence over ≥ 8
  head-sweep periods with an exact integer hold-out — a *sufficient* witness of
  low-dimensionality and a closability lead, nothing more.
* The detector is **conservative**: high precision (validated against
  hand-proven positives and chaotic negatives), lower recall (documented
  false negative: dossier-19). Class (a) is a floor; class (b) is an upper
  bound on genuine dark matter.
* The census `unstructured` verdict and this survey measure **different axes**:
  the census fits an affine law on record-event *times* (raw alphabet, stride
  ≤ 4); this fits an affine law on the tape *content* macro-state (histogram,
  stride ≤ 16). A machine can be quadratic in event-time yet chaotic in tape
  content (several class-(b) machines are), and vice versa. The 27.5% is the
  fraction the *census axis missed but the macro-state axis caught*.
* Nothing here decides any machine; every class-(a) hit's affine law remains an
  unproven conjecture about the machine's orbit. Reproduce with
  `python3 qgkit/bb6/darkmatter_alphabet.py --n 40 --horizon 30000000`.

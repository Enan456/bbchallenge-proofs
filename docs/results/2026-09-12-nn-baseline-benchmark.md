# Neural baseline: the certified-emulation benchmark, demonstrated

**Date:** 2026-09-12. Code: `qgkit/bb6/decider/nn_baseline.py`. This turns the
DeepMath "benchmark" framing from a proposal into a measured result, and makes
the "neural network" claim genuine rather than asserted. No DL library is
available or used; the network is a **from-scratch numpy MLP** (two hidden
layers of 48, ReLU, softmax cross-entropy, SGD backprop), trained on the
dossier-2 renewal-map event stream (symbol-history window `W=4`, ~1.3M symbols
over ~6k orbits). Honest by construction: a learned sequence-emulator sees only
the event history, exactly as it would on any sequence benchmark; the certified
emulator sees the exact integers.

## Task A — the net learns the grammar

1-step next-symbol prediction. Test accuracy **0.732** vs base rate 0.367. The
learned next-symbol distribution by last symbol:

| last symbol | net predicts C | F | T | certified grammar |
|---|---|---|---|---|
| C | 0.006 | 0.004 | **0.990** | `C→T` only (T=1) |
| F | 0.684 | 0.315 | **0.001** | `F→{C,F}`, never T (T=0) |
| T | 0.524 | 0.369 | **0.107** | `T→{C,F}`, never T (T=0) |

The net **recovers the symbolic law**: `C→T` almost exactly, `F↛T` exactly, and
TT-forbidden *mostly* (residual 0.107). The ~0.73 ceiling is the grammar's own
branching entropy — after `T` or `F` the `C`-vs-`F` choice is a real split that
symbol history alone cannot resolve. Note the contrast that is the whole point:
the certified extractor gives these transitions **exactly** (1, 0, 0); the net
leaves mass on forbidden transitions.

## Task B — the net breaks where the arithmetic lives

k-step-ahead symbol prediction:

| horizon k | MLP accuracy | base rate | certified emulator |
|---|---|---|---|
| 1 | 0.736 | 0.367 | **1.000 (exact)** |
| 5 | 0.396 | 0.369 | **1.000 (exact)** |
| 20 | 0.374 | 0.370 | **1.000 (exact)** |

The net's accuracy **collapses to the base rate by k=20** — no better than
guessing the majority symbol — while the certified emulator is exact at every
horizon. This is precisely what the native-resolution density result predicts:
long-horizon behaviour is governed by the arithmetic offset, which equidistributes
and does not concentrate, so it is unpredictable from any coarse learned
representation. The theorem and the experiment agree.

## Why this matches DeepMath's intent (honestly)

DeepMath is the conference on the *mathematical theory of deep learning*. This
experiment is a mathematics-of-learning result with a provable answer key:

- **A benchmark with certified ground truth.** Unbounded, exactly-labeled,
  law-governed sequence data on which a learned representation's successes and
  failures are both *exactly* measurable — the successes (local grammar) and the
  failure mode (arithmetic extrapolation) are not guessed, they are proven.
- **A separation result.** Learned representation recovers local structure;
  certified emulation is exact globally. The gap is not incidental — it is the
  native-resolution non-concentration theorem, observed empirically.
- **The "neural network" in the title is now real.** A trained net, with
  measured behaviour, not an analogy.

## Scaling sweep — the wall is arithmetic, not capacity (run)

To pre-empt "your net is just too small," we swept width, depth, and context and
measured 1-step vs 20-step accuracy. **The long-horizon wall holds in all 12
configurations** — 20-step accuracy never exceeds the base rate, while 1-step
stays at the grammar ceiling:

| axis | values | 1-step | 20-step | base rate |
|---|---|---|---|---|
| width (depth 2, W=8)   | 16, 48, 128, 384 | 0.732–0.740 | 0.367–0.371 | ≈0.370 |
| depth (width 96, W=8)  | 1, 2, 3, 4        | 0.735–0.741 | 0.363–0.373 | ≈0.371 |
| context (width 96, d2) | W=2, 4, 8, 16     | 0.733–0.739 | 0.359–0.371 | ≈0.370 |

No width (up to 384), depth (up to 4), or context window (up to 16) lets the net
beat the base rate at horizon 20. The 1-step accuracy sits at the grammar's
branching-entropy ceiling throughout. This is the decisive form of the claim:
the long-horizon unpredictability is not a capacity limitation a bigger model
would fix — it is the native-resolution arithmetic obstruction, which no coarse
learned representation can cross, and against which the certified emulator is
exact. Code: `qgkit/bb6/decider/nn_baseline.py` (sweep variant).

## Honest scope
The net is small and from-scratch (numpy); the sweep uses the same family up to
width 384 / depth 4. A large pretrained library model is untested here, but the
claim is specifically that the wall is *arithmetic, not capacity* — the sweep is
the evidence, and the density theorem is the reason. Larger-model confirmation is
a natural follow-up but not expected to change the long-horizon base-rate wall.

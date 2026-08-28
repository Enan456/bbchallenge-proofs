# The array-class certification ladder: all eleven machines

**Date:** 2026-08-27 · **Code:** `qgkit/bb6/d5_generic.py` ·
2M-step learn / 2M-step held-out per machine, fail-closed at every
rung (segment extraction → exact tiling → literal rule learning →
exact held-out reproduction).

Applying the rank-1 formalism (arrival segmentation, sweep
transducer, 20-cell literal decision windows — *no* machine-specific
parametrics) to the other ten EXACT array-class machines:

| machine | anatomy | tiled | held-out exact | verdict |
|---|---|---|---|---|
| `1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC` | one-sided + cursor restarts | 100% | **99.7%** (parametrics: exact) | **CALCULUS (v2, step-1 doc)** |
| `1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB` | one-sided, dip ladder 3+6k/5+6k | 99.8% | 82.4% (74,443/90,318) | CANDIDATE — needs its parametric families |
| `1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC` | one-sided, dense zigzag, nested dips | 40.6% | **99.3%** where tiled | LAW-EXACT — needs dip-aware segmentation |
| `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB` | one-sided, dense zigzag, nested dips | 55.9% | **98.6%** where tiled | LAW-EXACT — needs dip-aware segmentation |
| `1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---` | one-sided, continuous dip spectrum | 0.4% | — | ARCH-VARIANT |
| `1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE` | one-sided (left), sparse turns | 0.0% | — | ARCH-VARIANT |
| `1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD` | two-sided grower | 0.4% | — | TWO-SIDED |
| `1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE` | two-sided grower | 0.5% | — | TWO-SIDED |
| `1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---` | two-sided grower | 31.5% | 0.3% | TWO-SIDED |
| `1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF` | two-sided grower | 13.5% | 0% | TWO-SIDED |
| `1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC` | two-sided grower | 8.4% | 0% | TWO-SIDED |

## What the ladder shows

1. **The formalism ports.** One machine beyond rank-1
   (`1RB0LF_1RC---…`) passes the architecture gate essentially whole
   (99.8% tiling) and reaches 82.4% held-out exactness with *purely
   literal* rules — precisely the state rank-1 was in before its
   cascade/trisection parametrics were identified. Two more machines
   are **law-exact where extraction succeeds** (99.3%, 98.6%): their
   transducer laws are real; what fails is the segmenter's
   mini-arrival heuristic, which misclassifies their *nested unit
   dips* (excursion depths in arithmetic families 3+6k, 5+6k — the
   depth-parametrized cascade signature) as restarts.
2. **Architecture taxonomy.** The eleven EXACT machines split:
   one-sided sweepers (6, of which 4 are now within reach of the
   rank-1 treatment), and two-sided growers (5) that need the
   bidirectional version of the formalism (alternating left/right
   traversal segments — same machinery, two frontiers).
3. **Certification status.** Certified-exact calculus: rank-1
   (v2, 99.73% frozen at 200M + exact reseed differentials). The
   ladder positions above are what current tooling certifies today;
   each next machine is a bounded per-machine anatomy project (the
   dip-aware segmenter and the bidirectional segmenter are the two
   missing tools, each reusing the existing unit-tiling core).

## Honest scope

Horizons: 2M learn / 2M validate per machine (rank-1's numbers are
from its own 200M closure). "Tiled" is the fraction of segments
passing exact input/output/step-count tiling; held-out numbers count
only exact full-configuration reproduction. No parametric rules were
granted to any machine except rank-1 (its own document); every
number above is fail-closed.

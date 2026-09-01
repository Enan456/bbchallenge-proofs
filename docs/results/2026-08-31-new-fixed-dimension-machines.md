# Three new fixed-dimension machines: the census claim falls

**Date:** 2026-08-31 · **Data:**
`experiments/outputs/sweep251_results.jsonl` (10x-budget finder sweep
over the previously unprobed structured pool) · shape gates run at 1M
steps per machine

## The result

The deep finder sweep surfaced seven machines with small, high-support
orbit specifications. Four are the certified machines themselves,
blindly re-discovered by the pipeline with the smallest specs in the
pool, a strong validation of the instrument:

| machine | rules | top support | identity |
|---|---|---|---|
| `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | 15 | 555 | dossier-3 (certified) |
| `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` | 16 | 1,643 | Antihydra (certified) |
| `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | 17 | 562 | dossier-2 (certified) |
| `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` | 30 | 700 | dossier-1 (certified) |

Three are new, and **all three pass both fixed-shape gates** (interior
hole count and RLE dimension bounded across 591 to 907 fresh-extreme
events over 1M steps), the gates every array-class machine fails:

| machine | rules | top support | gates |
|---|---|---|---|
| `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` | **5** | 680 | PASS / PASS |
| `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` | 70 | 334 | PASS / PASS |
| `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE` | 75 | 268 | PASS / PASS |

The dossier-4 census claim that the certified four are the only
fixed-dimension machines in the cohort is therefore **falsified by
this deeper sweep**: it was an artifact of the top-25 ranking cutoff,
not of the class. The fixed-dimension class has at least seven
members, three of them uncertified.

## The five-rule machine

`1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` carries the smallest
exact spec the program has seen. Its law, from the fail-closed fit
over 720 observed transitions:

- dominant drift (support 680): (x0, x1) -> (x0 + 4, x1 - 3), cost
  (32/3)x1 - 41/3;
- renewal (support 7): (x0, x1) -> (3 x0, x1 - (3/2) x0);
- two startup rules on one counter (support 16, 15);
- one rare rule at support 2 whose fractional coefficients are
  under-determined (two samples) and need a longer horizon before
  they can be trusted.

This is the drift-and-renewal anatomy of the dossier-2/3 reduced map
(compare (a,b) -> (a+6, b-3) with fatal diagonal), expressed directly
at record level with a multiplicative renewal: a new Collatz-like
two-counter hybrid, and the most tractable certification target
identified since dossier-1.

## Correction (later the same day)

The full law derivations (docs/results/2026-08-31-dossier7-dossier8-
laws.md) show the 1M-step gate verdicts on the two larger machines
were horizon artifacts in one direction and right in another: their
literal RLE dimension is unbounded (the state carries a unary-coded
ladder (1 0)^k whose k grows), so the strict RLE gate eventually
fails; but the macro state is nevertheless a fixed integer vector
((a, b, k) and (a, b, k, g)), so the fixed-dimension classification
stands at the counter level, which is the level the certified four
are classified at. The five-rule machine (Dvisetu) is fixed-dimension
in the strict sense.

## Honest scope

Shape gates: hole-count and RLE maxima compared between the first and
last third of events at a 1M-step horizon with slack 2 and 4; the
certified four pass the same gates under the same instrument
(instrument validation, not proof). Spec quality varies: the support-2
rule of the five-rule machine is under-determined. Certification of
the three new machines is future work; the finder spec is evidence,
never a proof.

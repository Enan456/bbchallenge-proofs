# stage756 — incision atlas

**Honest scope:** every number and figure here is bounded empirical
structure over finite budgets; nothing proves halting or
non-halting for any machine.  Exact mode mirrors the Lean-certified
event process (`packages/bbchallenge`); record mode is a heuristic
proxy.

## Antihydra — exact certified event process

| metric | value |
|---|---|
| mode | exact-certified |
| machine | antihydra |
| n_events | 20000 |
| n_merge | 9972 |
| n_drop | 10028 |
| heads_min | 2 |
| heads_final | 9919 |
| min_death_margin | 4 |
| events_within_1e8_raw_steps | 16 |
| log10_total_raw_steps | 7045.92 |
| raw_steps_first_event | 228 |

The `events_within_1e8_raw_steps` row is the measured acceleration
of boundary-only checking: that many incision events carry the same
information as 10^8 raw steps (cross-check: stage753 observed
14,109 E-entry events in its 10^8-step replay).

## Record-mode machines (sim budget 200,000 steps)

| machine | halted | records | events | near-collapse | dim-change | dims min/max | dims tail mean |
|---|---|---|---|---|---|---|---|
| `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` | False | 621 | 46 | 40 | 16 | 1/3 | 2.91 |
| `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` | False | 341 | 73 | 63 | 34 | 1/5 | 3.33 |
| `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | False | 460 | 437 | 251 | 408 | 1/4 | 3.47 |
| `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | False | 496 | 476 | 273 | 441 | 1/4 | 3.49 |
| `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | False | 462 | 247 | 145 | 219 | 1/4 | 3.48 |
| `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` | False | 64 | 19 | 16 | 10 | 1/12 | 7.25 |
| `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` | False | 277 | 37 | 37 | 1 | 1/2 | 2.0 |
| `1RB1RA_1RC1LB_0LD0RA_1RA1LE_---1LF_1LC0LF` | False | 62 | 32 | 30 | 7 | 1/11 | 7.25 |
| `1RB1RA_1RC1LE_1RD1LC_0LB0RA_---1LF_1LD0LF` | False | 84 | 61 | 59 | 9 | 1/11 | 4.0 |

Figures: `antihydra_exact.png`, `records_<id>.png` (when matplotlib
is available).  Event data: `events/*.jsonl` (resumable).

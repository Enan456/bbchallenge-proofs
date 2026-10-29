# Cross-verification against Google DeepMind's BB(6) cryptids (2026-10-22)

**Context.** On 2026-10-15 Google DeepMind posted *At the Limits of
Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver
Frontier* (arXiv:2610.22603) and the companion repository
`google-deepmind/cryptids`, containing Lean 4 Collatz-like reductions for
53 BB(6) holdouts: 11 the paper calls novel, 31 rediscoveries of
wiki-documented machines, and later additions. Seven of those 53 machines
also carry Lean conditional closures in this repository, developed
independently between 2026-07-27 and 2026-09-04 (this repo was private
until 2026-10-22, so neither side saw the other's work):

| this repo | machine | Google status | our Lean closure committed |
|---|---|---|---|
| dossier-2 (Piasa) | `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | one of the paper's 11 "novel" cryptids | 2026-08-25 |
| dossier-3 (Grafton Piasa) | `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | one of the paper's 11 "novel" cryptids | 2026-08-25 |
| dossier-7 (Kaskaskia) | `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` | one of the paper's 11 "novel" cryptids | 2026-09-03 |
| dossier-27 | `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` | added 2026-10-20 (PR #9), no wiki page | 2026-09-04 |
| Antihydra | `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` | rediscovery (community machine) | 2026-08 |
| Dvisetu (dossier-6) | `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` | rediscovery (wiki `suspect_15`) | 2026-08 |
| dossier-8 (Cahokia) | `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE` | rediscovery | 2026-09 |

All 53 Google machines and all 115 machines in this repo are drawn from the
same 1,094-machine holdout snapshot (`experiments/outputs/BB6_holdouts_1094.txt`).

**What was cross-verified.** For the four machines where both sides claim a
*new* reduction (dossier-2, 3, 7, 27), both abstract systems were replayed
against one raw simulation of the machine from the blank tape:

- Google's `start / encode / next` (ported literally from their Lean, see
  `qgkit/bb6/gdm_cross/gdm_rules.py`): every time the raw configuration
  equals `encode(expected)` the expected state advances by `next`. This
  checks exactly what `IsValidAcceleration` asserts, step by step: the
  start configuration is reached, every `next` successor is reached
  (`ReachesPlus`), and `next = none` never fires without a raw halt.
- This repo's orbit (`metaOrbit` for dossier-2/3, `worbit` for
  dossier-7/27, ported literally from our Lean, see `our_rules.py`):
  every abstract state must be *realized* on the tape (`Realizes` /
  `Inv`) at the predicted raw step, and the fail-closed orbit must never
  return `none`.

Harness: `qgkit/bb6/gdm_cross/`; tests: `tests/bb6/test_gdm_cross.py`
(14 tests, including decode∘encode round-trips for every Google state
family and agreement of the new `metaStep` port with the independent
2026-08 port in `halting_game23.py`). Reproduce the 20M-step runs with

```sh
python -m qgkit.bb6.gdm_cross d2 d3 d7 d27 --horizon 20000000 --md out.md
```

## Results (20,000,000 raw steps each; all PASS)

| machine | Google abstract steps hit | Google start (raw step) | this repo abstract steps realized | our anchor (raw step) | either orbit died? | raw halt? |
|---|---|---|---|---|---|---|
| dossier-2 | 2,214 | 100 (as documented) | 4,412 | 235 (= Lean `anchor_run`) | no | no |
| dossier-3 | 49 | 76 (as documented) | 4,718 | 2,044 (= Lean `anchor_run`) | no | no |
| dossier-7 | 5,223 | 162 (as documented) | 5,263 records | 0 (anchor `(A, [])`) | no | no |
| dossier-27 | 5 | 169 (**docstring says 66**) | 6,817 records | 0 (anchor `(A, [])`) | no | no |

Per-machine reports with final abstract states, gap statistics, and
granularity diagnostics: `docs/results/gdm_cross/{d2,d3,d7,d27}.md`
(JSON alongside).

## Findings

1. **Both formalizations agree with the machines and with each other on
   all four.** Neither Google's `next` nor our orbit ever disagreed with
   the raw trace over 2×10⁷ steps per machine, and neither fail-closed
   system died. Since Google proves `IsHalt ↔ CollatzHalts next start`
   and we prove `Safe → ¬RawHalts`, the two together say: the machine
   halts iff Google's counter system halts, and our orbit conjecture
   implies Google's counter system never halts. This is the first
   independent reproduction of any of the Google BB(6) reductions that we
   are aware of.

2. **Documentation error in Google's dossier-27 file.** The module
   docstring of `M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean` says the
   machine "reaches `S6 1` in 66 steps". The raw trace reaches `P_cfg 3`
   at step 97 and `S6_cfg 1` at step 169. Their proof is unaffected:
   `init_to_S6_1` is a `ReachesStar` statement with no step count, and 66
   is the step count of their `step_drain_odd_end_66_0349` turnaround
   lemma. Worth a one-line PR upstream.

3. **Granularity differs, and neither is wrong.** Google's `next` for
   dossier-3 composes whole sweep cascades: the raw trace passes through
   2,317 other members of their own canonical family before reaching the
   expected successor (first instance at raw step 1,181: `C(5,7,10)` met
   while `C(0,2,40)` was expected). `IsValidAcceleration` only requires
   `ReachesPlus`, so this is allowed, but it means their `next` is not a
   "first return" map and a reader should not expect it to be. Our
   `metaStep` samples every spawn entry (one realization per episode).
   For dossier-27, Google's `R2` rule multiplies the block count by ~3
   per abstract step, so only five abstract steps fit in 2×10⁷ raw steps
   (the fifth at raw step 4,065,667); a 10⁸-step run
   (`docs/results/gdm_cross/d27_100M.md`, 71 s) catches the sixth at raw
   step 38,979,318 (`R2 2196`, next expected `Q 6808`), still PASS, with
   our word orbit at 16,613 exact record transitions over the same
   horizon (max word length 16,656).

4. **Statement strength.** Google's `isHalt_iff_acceleration` is a
   bidirectional reduction; ours is one-directional (`Safe → ¬Halts`),
   with the converse ("leaving the guarded region halts within tens of
   raw steps") established only empirically (`2026-08-30-halting-game.md`).
   Upgrading our four closures to an `iff` is the natural next Lean step
   and is now straightforward to state against their predicates via the
   shared raw semantics. Conversely, our closures come with the
   halt-localization lemmas (`halt_requires_*_probe_00`) and the
   standard-format parser-parity theorems that their files do not carry.

5. **What neither side has.** No machine is decided. Google's abstract
   counter systems and our orbit conjectures are, for these four machines,
   two descriptions of the same open arithmetic question. The dossier-2/3
   question (`docs/results/2026-08-26-renewal-map-analysis.md`) is known
   to have no congruence invariant to modulus 384 and no rotation
   rigidity, which is why neither side could close it.

## Validation horizons (added 2026-10-29)

The Lean theorems on both sides are horizon-free; step counts bear only on
the evidence behind the open orbit conjectures. Sources: the paper's text
(arXiv:2610.22603, Section on pattern detection and Appendix A) and this
repository's results documents.

| what was run | DeepMind (as reported in the paper) | this repository |
|---|---|---|
| raw steps per machine used to find the rules | 5×10⁶ (pattern-detection pass) | 2×10⁷ to 10⁸ (stage751 exact-replay fits at 10⁸; `2026-08-27-d4-fullset-certification.md`) |
| raw steps the rules were checked against | 128,000 per synthetic transition during refinement | dossier-2/3: 10⁹ raw steps each (`closure-report.tex`); dossier-7/8: 2×10⁷ with 5,251/5,251 and 3,879/3,879 record transitions exact (`2026-08-31-dossier7-dossier8-laws.md`); dossier-27: 2×10⁷ with 10,909/10,909 exact (`tests/bb6/test_d27_theorems.py`) |
| abstract-system iterations | not reported | dossier-2/3 renewal map: 10⁸ iterations ≈ 10¹⁵ raw steps, minimum margin 4 from the fatal set (`2026-08-26-renewal-map-analysis.md`) |
| synthetic fresh-value replays of proof obligations | none reported | 10⁸ raw steps per obligation; Antihydra 13/13, dossier-1 33/33 (stage753) |
| whole-holdout census | 1,094 machines analysed for rule discovery | all 1,094 at 1.2×10⁵ steps with depth-18 halt cones: 0 halts, 0 alignments (`2026-09-03-state-and-gaps.md`) |
| cross-verification of the other side's reduction | none | 2×10⁷ raw steps per shared machine, 10⁸ for dossier-27, both abstract systems on one trace (this document) |

Reading: the paper's confidence that a machine is a cryptid rests on the
Lean proof that its rules are sound, which is legitimate and horizon-free;
the paper reports no run longer than the detection pass. This repository's
conjectures for the mirror pair were watched about 10³ times longer in raw
steps and about 10⁹ times longer through the renewal map. Neither is
understanding, and the community's own simulation of every BB(6) holdout to
10¹³ steps (BusyBeaverWiki, BB(6) page) exceeds both; the table is a
statement about validation effort behind the same open conjecture, nothing
more.

## Non-claims

- No claim of priority is made beyond the commit dates above; both
  efforts were independent and Google's repository was public first.
- The cross-verification is a bounded empirical replay of two kernel-
  checked reductions, not a Lean proof relating them. The Lean bridge
  (`SafeMetaOrbit ↔ ¬CollatzHalts next start`) is listed as follow-up.

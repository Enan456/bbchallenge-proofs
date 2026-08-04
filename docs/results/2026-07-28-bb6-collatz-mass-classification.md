# BB(6) Collatz-lens mass classification (stage745)

**Date:** 2026-07-28
**Scripts:** `experiments/stage745_collatz_mass_sweep.py` (sweep),
`experiments/stage746_next_cryptid_dossiers.py` (dossiers)
**Module:** `qgkit/bb6/vcollatz/classify.py` (`characterize_holdout`)
**Input:** `experiments/outputs/BB6_holdouts_1094.txt` (1094 machines = 137 frontier + 957 untested)
**Profile:** fast (`decider_budget=20k, backward_depth=200, ctl_radius=4, far_dfa_states=6, sim_steps=700k, extract_steps=1M`)

## Result

All 1094 holdouts classified, 0 errors, full per-machine records in
`experiments/outputs/stage745/rows.jsonl`.

| label | count |
|---|---|
| GROWING_DIM | 1006 |
| CRYPTID_COMPACT_GROWTH | 51 |
| BOUNDED_VARYING | 35 |
| VCOLLATZ_EXACT_PROJECTION | 2 |
| DECIDED_* | **0** |

No machine was decided — consistent with this being a genuine residual set that
already survived much larger decider budgets.

## Soundness event during the sweep

The first run produced 42 `DECIDED_NONHALT:bouncer` rows. These came from the
toc chain's step-4 `certify_bouncer`, whose frontier certificates were
**falsified on 2026-07-18** (stage647: 135/137 are non-uniform carry-counters;
certificates invalid as proofs). `characterize_holdout` now demotes those
certifications to undecided (`decider.demoted =
"unsound_bouncer_certificate_2026-07-18"`); the Lean-backed `bouncer_sound`
decider remains trusted. The tainted rows were purged and re-swept.

**Cross-check:** the finished sweep contains exactly **137 demoted bouncer
certificates** — a one-for-one match with the 137 known frontier machines the
falsified decider certifies. The sweep independently re-identified that
population.

## Exact vector-Collatz projections (the headline)

Only 2 of 1094 machines admit an exact, faithful, fixed-dimensional
vector-map projection at these budgets — and both are 1-dimensional with
mod-2 branching, i.e. the literal generalized-Collatz shape:

| code | d | mod | branches | note |
|---|---|---|---|---|
| `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` | 1 | 2 | 2 | **Dvisetu** (known; stages 655–744) |
| `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB` | 1 | 2 | 1 | **new top novel candidate** |

The sweep therefore independently re-derives Dvisetu as one of the two most
Collatz-like machines in the entire holdout set, and surfaces exactly one peer.

## Top novel compact-growth candidates

Novel = not on the BusyBeaverWiki Cryptids page (2026-07-27 snapshot) and not
Dvisetu. Top 12 by stage655 score:

| score | dmax | dominant delta | support | code |
|---|---|---|---|---|
| 266.19 | 2 | (3, -2) | 0.917 | `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB` |
| 254.25 | 5 | (2, -2, 1) | 0.74 | `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` |
| 242.68 | 4 | (0, 0, 0) | 0.433 | `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` |
| 242.20 | 7 | (-2, 3) | 0.599 | `1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB` |
| 241.96 | 5 | (-2, 3) | 0.511 | `1RB1LC_1LC0RD_0LE1LA_0RF1RA_1RD0LA_---0RB` |
| 241.96 | 5 | (-2, 3) | 0.511 | `1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB` |
| 241.32 | 4 | (0, 0) | 0.325 | `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD` |
| 241.19 | 4 | (0, 0) | 0.412 | `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` |
| 239.77 | 4 | (0, 0) | 0.385 | `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` |
| 239.44 | 10 | (0,…,0,1) | 0.552 | `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF` |
| 239.44 | 10 | (0,…,0,1) | 0.552 | `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF` |
| 238.56 | 7 | (-2, 3, 0) | 0.493 | `1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB` |

Note the delta-rule families: three distinct machines share the (-2, 3)
two-block transfer rule and two share a 9-dimensional carry rule — likely
TNF-distinct members of shared macro-dynamics families worth analyzing
together.

Full ranked list: `experiments/outputs/stage745/summary.json` (`top_novel`,
25 entries) and `classification.md`.

## Comparison with the stage652 taxonomy

Stage652 (957 untested only, different dims heuristic): GROWING_DIM 788,
BOUNDED_VARYING 90, FIXED_DIM_CARRY 9, SHORT 70. Stage745 covers all 1094
with the frontier records dims trajectory; the heuristics agree that
growing-dimension behavior dominates (~92%), while stage745's compact-growth
tier isolates the 51 machines with cryptid-shaped structure that the class
labels alone hide.

## Honest scope

- Every non-DECIDED label is bounded empirical structure. Nothing here proves
  halting or non-halting for any machine.
- `VCOLLATZ_EXACT_PROJECTION` maps are block-length projections
  (`EXTRACT_HALT_FAITHFUL = False`); they do not capture halt conditions and
  support no machine-level non-halting claim.
- The compact-growth score is the stage655 ranking heuristic for human
  reverse-engineering priority, nothing more.

## Stage746 dossiers (complete: 8 of 8)

All 8 top novel candidates ran 50,000,000 raw steps: **none halted**
(`experiments/outputs/stage746/dossier_00..07.json`, `dossiers.md`).

**Dossier 0 — `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB`** (the Dvisetu peer):

- No halt through 50,000,000 raw steps.
- At 3M-step record depth: dims lock to 2 blocks (period-1 match 0.985), the
  (3, −2) two-block transfer rule support RISES to 0.948, score 283.6.
- 77 one-block checkpoint values observed. Caveat: checkpoints are sampled
  every 64 steps, and the long arithmetic (+64) stretches in the series mean
  the tape spends extended phases as a single smoothly-growing block — a
  different macro-shape from Dvisetu's discrete collapse checkpoints. The
  irregular jump points (e.g. 622→731, 987→1068, 2201→2326) are the
  structural events worth macro-rule analysis.
- High-budget re-extraction (3M steps, max_dim 6) returned NO map, while the
  1M-step stage745 extraction succeeded (d=1, mod 2, 1 branch). The ≥90%
  dominant-dimension gate is budget-sensitive here; the 1M-step map remains
  faithful for the vectors it covered, but the projection is not stable
  across budgets — a caution for any macro-system derivation.

**Dossier 1 — `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`:**

- No halt through 50,000,000 raw steps.
- Dims lock to 3 blocks (period-1 match 0.98), dominant rule (2, −2, 1)
  support 0.851, score 275.0.
- Only 8 genuine one-block collapse checkpoints in 50M steps, and the series
  accelerates: 1, 68, 105, 278, 420, 633, 2071, 5379 — a sparse
  super-linear checkpoint sequence, the classic generalized-Collatz
  reverse-engineering target.

**Dossiers 2–7 (all no-halt @ 50M steps):**

| # | code | dmax | delta @ frac (3M) | one-block checkpoints |
|---|---|---|---|---|
| 2 | `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | 4 | (0,0,0) @ 0.462 | **1, 11, 111, 4700** — extreme acceleration |
| 3 | `1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB` | 7 | (−2,3) @ 0.682 | only the initial 1 — never re-collapses |
| 4 | `1RB1LC_1LC0RD_0LE1LA_0RF1RA_1RD0LA_---0RB` | 5 | (−2,3) @ 0.484 | only the initial 1 |
| 5 | `1RB1LC_1LC0RD_0LE1LA_---1RA_1RF0LA_0RF0RB` | 5 | (−2,3) @ 0.484 | only the initial 1 |
| 6 | `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD` | 4 | (0,0) @ 0.402 | 82 values, +128 arithmetic runs + irregular jumps |
| 7 | `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | 4 | (0,0) @ 0.425 | 1, 65, 2394 — sparse |

Family structure confirmed: dossiers 4 and 5 have byte-identical 3M-step
feature vectors (score 259.062, same rule and support) — almost certainly TNF
siblings of one dynamics family; dossier 3 shares their (−2,3) rule at higher
support. The three never collapse to a single block after startup, so their
macro-dynamics live entirely in the multi-block regime (no Dvisetu-style
checkpoint map exists for them).

All 8 machines remain undecided by every sound decider. Ranked
reverse-engineering targets:

1. **Dossier 1** (`1RB0LE_...0RB`) — sparse accelerating collapse map
   (1, 68, 105, 278, 420, 633, 2071, 5379): cleanest macro-system target.
2. **Dossier 2** (`1RB0LC_...1RA`) — 1, 11, 111, 4700: even sparser; check
   for a multiplicative/exponential checkpoint law.
3. **Dossier 0** (the peer) — strongest rule support (0.948) but re-run its
   extraction with a record-phase-aware gate before trusting the 1-D map.
4. **The (−2,3) family** (dossiers 3/4/5 together) — one macro analysis
   likely covers all three.

## Honest scope (dossiers)

50M-step non-halting is bounded evidence only. Checkpoint series are
sampling-stride-limited (64 steps). Nothing above decides any machine.

## Stage747: exact macro system for dossier-1 — PASS

**Script:** `experiments/stage747_dossier1_macro_system.py`
**Machine:** `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` (halts iff state F reads 0)
**Status:** `PASS_EXACT_MACRO_SYSTEM`

The macro state is the augmented frontier record `(machine_state, side,
blocks)` — on blocks alone the dynamics are NOT deterministic; with the
augmentation there are **0 determinism conflicts** over all observed
transitions.

Derivation is fail-closed at every layer: rules are fitted per input-derivable
group as constant-delta or exact rational affine maps (solved over ℚ,
re-verified on every member; constant input columns are folded with an exact
guard); groups that cannot generalize become flagged literals.

**Verification (the conclusive gates):**

- In-sample replay: **3,832/3,832 transitions exact** (20M-step fit run,
  post-startup).
- Out-of-sample: the frozen table reproduces **4,150/4,150 transitions
  exactly** beyond the fit horizon in a fresh 100M-step run — zero
  mismatches, zero uncovered.
- Rule economy: **36 generalized rules + 7 flagged literals** (all 7 are
  level-2 hierarchy-spawning events seen ≤2× in the fit window).

**The macro system (headline rules by support):**

| rule | support |
|---|---|
| dim-3 sweep `(a,b,c) → (a+2, b−2, c+1)`, state E, right frontier | 2,620 |
| dim-4 sweep `(p,a,b,c) → (p, a+2, b−2, c+1)` (prefix frozen) | 979 |
| dim-5 sweep `(p,q,a,b,c) → (p,q, a+2, b−2, c+1)` | 80 |
| expansion chain `(n) → (n,1) → (1,n,1) → (2,n−2,2)` | 8 each |
| suffix merge `(…,a,1,c) → (…, a+c+4)` at middle = 1 | (per-dim groups) |

**Checkpoint law (cycle-aware, exact):** consecutive full-collapse values in
100M steps are 1, 1, 5, 11, 20, 67, 104, 277, 419, 632, 2070, 5378. Pairs
whose intervening dynamics stay ≤ dim 3 (SINGLE_CYCLE) satisfy exactly

```text
n odd  →  n' = (3n + 7) / 2        (verified 5/5: 5→11, 11→20, 67→104,
                                     277→419, 419→632; 0 failures)
```

Even collapse values always spawn a hierarchical (dim 4–5) epoch instead —
the four MULTI_LEVEL pairs (20→67, 104→277, 632→2070, 2070→5378) are
compositions of the same rules one level down. This "odd steps simply, even
recurses" structure is the machine's defining generalized-Collatz signature.

**Halt localization (bounded):** the machine halts iff state F reads 0; state
F appears at **0 of 7,992** frontier records in 100M steps (records are E:
7,949, D: 30, A: 11, B: 2). No unreachability claim — F occurs between
records; a proof would need the F-entry windows characterized against the
macro invariant.

**Honest scope:** PASS means the macro system reproduced every observed
record transition exactly, in and out of sample. It is not a non-halting
proof. The proof path it opens: show every macro rule preserves the
"F never reads 0" invariant (Dvisetu-style terminal-residue analysis on the
merge/expansion windows), then formalize the raw-to-macro correspondence as
in the kirmira package.

## Stage748: halt-window census (2026-07-29)

**Script:** `experiments/stage748_dossier1_halt_window_census.py`

The machine's only route to halting is local: F is entered solely via
`C0 = 0RF`, and `F0 = ---`, so halting requires **state C reading 0 with a
second 0 immediately to its right**. A 100M-step census of every F-entry:

- **7,947 F-entries** (≈ one per frontier-record cycle); **F read 1 every
  time** (assert held through the full budget).
- **Only 10 distinct 9-cell windows** ever occur at F-entries. The dominant
  window `1111·0·1111` — C in a single-0 gap between two 1-blocks — covers
  7,872/7,947 (99.1%); the other nine (counts 1–18) are startup/small-value
  variants, and every window has a 1 in the F-read cell.
- Events sit almost exclusively at the gap left of the rightmost block
  (nearest-run-index-from-right = 1), i.e. exactly where the macro sweep
  operates. By dimension: dim-3 6,446, dim-4 1,407, dim-5 94.

**Candidate halt-unreachability invariant:** every 0-gap that state C probes
has length exactly 1. This places the machine squarely in the non-regular
"state X reads s" invariant class identified for the 137-frontier (2026-07-18)
— but here backed by an exactly verified macro system to carry the induction.

**Next (stage749):** align each F-entry with the macro rule firing at that
record cycle (rule → window multiset). If each of the 36 rules yields exactly
one window shape, the invariant preservation argument reduces to 36 local
checks — the precondition for a Lean/kirmira-style formalization.

Bounded census; no unreachability claim.

## TNF-equivalence / novelty check (2026-07-29)

Both dossier-1 and the peer are already in first-entry canonical form with the
first-move-R orientation (i.e. the DB-representative string is our string);
their mirror-canonical forms were computed as well. BusyBeaverWiki full-text
search (`insource`) returns **0 hits** for both machines in both orientations
(5-state prefix search covers `---`/`1RZ` halt spellings), and the machine
page URLs 404. Neither machine is published on the wiki in any orientation.
Caveat: this checks the public wiki record only — community decider verdicts
on private/holdout lists cannot be ruled out without asking on the
bbchallenge forum/Discord.

## Stage749: rule↔window alignment — 33 local obligations

**Script:** `experiments/stage749_dossier1_rule_window_alignment.py`

Every F-entry in 100M steps was assigned to the macro rule firing in its
record interval: **0 unmatched intervals** (independent reconfirmation of the
stage747 rule table's totality). Of the 30 rules whose intervals contain
F-entries, **27 produce exactly one F-window shape**; 3 boundary rules
(pre-merge groups with a middle component of 2 — `(4,R,3,(4,2,4))`,
`(4,R,4,(4,4,2,4))`, `(4,R,5,(4,4,1,2,1))`) produce exactly two. All window
shapes come from the stage748 10-window set, and every shape reads 1 at the
F-cell.

**Consequence:** the halt-unreachability invariant ("every 0-gap C probes has
length exactly 1") reduces to **33 (rule, window) local obligations** — for
each pair, show that the rule's raw micro-trajectory only probes C-reads-0 in
that window shape. This finite obligation list is the direct input for a
kirmira-style raw-to-macro formalization with a Lean-checked induction.

Bounded alignment census; no unreachability claim.

## Stage750: all 33 obligations discharged (uniformity + fresh-value replay)

**Script:** `experiments/stage750_dossier1_obligation_discharger.py`
**Status:** `ALL_DISCHARGED_UNIFORM` (33/33, 0 failed)

For every (rule, window) obligation, two fail-closed checks pass:

1. **Uniformity:** across every firing of the rule in 100M steps, the C-probe
   events occur at identical positions relative to the block structure, with
   per-firing counts either constant or exactly affine in the VAR block
   lengths. RLE templates use position-wise abstraction (an entry is literal
   iff constant across all firings, else VAR).
2. **Fresh-value replay:** synthetic configurations built from each rule's
   RLE template with block values never observed for that rule (guard- and
   parity-respecting, head placed on the fresh blank cell beyond the block
   region per record semantics) reproduce both the macro rule's predicted
   output and the same probe structure — 59/59 synthetic replays passed;
   F read 1 in every replay event.

**Meaning:** the uniform-crossing premise needed for the halt-unreachability
induction is now mechanically established for every obligation. The
non-halting argument for this machine is structurally complete at the
empirical level: exact macro system (stage747) + finite obligation list
(stage749) + uniformity/fresh-value discharge (stage750). What remains is
proof engineering: a kirmira-style raw-to-macro correspondence and a
Lean-checked induction over the 33 obligations.

Honest scope: uniformity + fresh-value replay evidence for the induction
premise; not itself a proof.

## Phase 0/1: sync with the official open set (2026-07-29)

The community's annotated 1534-holdout sheet (July 2026) shows 1,158 machines
not yet marked HALT/NONHALT (1,083 blank + 18 CRYPTID + 56 equivalence-
duplicates + 1 tentative). Diff against our 1,094: 1,093 still open, 1
decided by the community's SOCSS proof in March 2026 (our sweep had it as
GROWING_DIM undecided — no conflict), 65 new to us. The full current-open
list is `experiments/outputs/BB6_open_1158_2026-07-29.txt`.

Sweeping the 65-machine delta (same fast profile) completes **full
Collatz-lens coverage of the official open set**:

| label | count (all 1,159 swept) |
|---|---|
| GROWING_DIM | 1,069 |
| CRYPTID_COMPACT_GROWTH | 53 |
| BOUNDED_VARYING | 35 |
| VCOLLATZ_EXACT_PROJECTION | 2 |

Still exactly two exact 1-D projections (Dvisetu + peer) across the entire
official open set. Two new cryptid-tier machines from the delta:
`1RB0LB_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` (score 236.5, 9-dim carry rule)
and `1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB` (score 232.3, 10-dim carry
rule).

Community-context notes: dossier-1 and the peer both sit in the official
list with status blank and bulk classification "Quadratic Mess" — known and
binned, never individually analyzed; our characterization is the first. The
community simulates survivors to 10^14–10^15 with accelerated simulation;
our raw budgets (10^8) are shallow by comparison — for macro-PASS machines
the verified rule systems provide the accelerated-simulation path.

## Stage751/752: full open-set observatory + halt-localization (2026-07-29)

**Scripts:** `experiments/stage751_open_set_observatory.py` (parallel,
resumable; ran sharded across this machine and the Mac Studio),
`experiments/stage752_generalized_halt_localization.py`.
**Coverage:** all 1,158 official open machines, 0 timeouts, 0 errors.
Budgets: fit 10M / verify 30M steps (74 machines at 20M/100M).

**Macro verdicts:** `PASS_EXACT_MACRO_SYSTEM` **9** · PARTIAL 35 ·
NOT_FITTABLE_HIGH_DIM 1,114.

**The ranked queue (stage752, 100M-step halt-localization on the 9):**

| machine | macro | obligations | note |
|---|---|---|---|
| `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` | exact | **13** | **Antihydra** |
| `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | exact | 24 | dossier-7 machine |
| `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | exact | 26 | dossier-6 machine |
| `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` | exact | 33 | dossier-1 (fully discharged + Lean layer) |
| `1RB1RA_1RC1LE_1RD1LC_0LB0RA_---1LF_1LD0LF` | exact | 51 | sibling pair A |
| `1RB1RA_1RC1LB_0LD0RA_1RA1LE_---1LF_1LC0LF` | exact | 54 | sibling pair B |
| `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` | exact | 68 | |
| `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` | replay mismatch @752 budget | — | wiki cryptid; budget-sensitive |
| `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | replay mismatch @752 budget | — | dossier-2; budget-sensitive |

Every landing-symbol census is unanimous: across millions of halt-window
events per machine, the entered state never read its halting symbol.

**Headline: Antihydra's halting reduces, under an exactly verified macro
system, to 13 local (rule, window) obligations** — the smallest obligation
list in the open set. Its known analysis is the probabilistic Collatz
argument; an exact replay-verified rule table with a 13-item halt-avoidance
obligation list is, to our knowledge, a new kind of artifact for it.

**Honest scope:** obligations here are census-level alignments (stage749
analogue). Only dossier-1 has been through the stage750 uniformity +
fresh-value discharge. PASS is exact about observed records, not a proof;
the two replay-mismatch machines passed stage751 at different budgets
(fit-horizon sensitivity, like the Dvisetu peer).

## Lean halt-localization layer (axiom-clean)

**File:** `lean/QIG/Dossier1RawTM.lean` (Lean 4, bare core, no sorry;
axioms = `propext` + `Quot.sound` only)

Fully machine-checked, unconditional theorems about the exact raw machine:

- `step_eq_none_iff` — the machine halts in one step iff state F reads 0;
- `into_F_only_from_C0` — F is entered only via C reading 0;
- `halt_requires_c_probe_00` — **any raw halt from a non-F start passes
  through a reachable configuration where C reads a 0 whose right neighbour
  is also 0**;
- `blank_nonhalting_of_c_probe_safe` — `CProbeSafe blankStart → ¬ RawHalts
  blankStart`.

`CProbeSafe blankStart` ("every 0 that C reads in any reachable
configuration has a 1 to its right") is precisely the invariant discharged
empirically by stages 748–750. The proof burden is now a single named Lean
contract: derive `CProbeSafe blankStart` from the 33 macro obligations via a
DvisetuRawTM-style raw-to-macro closure induction. Everything else in the
chain — halt localization and the invariant⇒non-halting implication — is
machine-checked and unconditional.

---

## Stage753: generalized obligation discharger — Antihydra 13/13 (2026-08-03)

**Script:** `experiments/stage753_generalized_obligation_discharger.py`
**Outputs:** `experiments/outputs/stage753/` (per-machine JSON + run.log)

Machine-agnostic port of the stage750 dossier-1 discharger onto the
generalized `qgkit.bb6.vcollatz.macro` fitter, run over all 9
`PASS_EXACT_MACRO_SYSTEM` machines at 100M steps. Validated by exact
regression: on dossier-1 it reproduces stage750's 33 obligations and
discharges all 33 with zero machine-specific branches in the code.

### Headline

**Antihydra (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) discharges all
13 of its (rule, window) halt-avoidance obligations**: firing templates
uniform, every entry-event count constant/affine (or exactly-guarded
piecewise) in the variable block lengths, and fresh-value synthetic replays
reproduce both the macro prediction and the safe probe structure. Antihydra
now stands at the same "structurally complete empirically" tier as
dossier-1: its non-halting argument is finished except for the raw-to-macro
closure induction in Lean.

### Full scoreboard (100M steps)

| machine | obligations | discharged | status |
|---|---|---|---|
| Antihydra `…_---0RA` | 13 | **13** | ALL_DISCHARGED_UNIFORM |
| dossier-1 `…_---0RB` | 33 | **33** | ALL_DISCHARGED_UNIFORM |
| `1RB1RC_…_0RD1RD` | 24 | 6 | FAILED (synthetic replay divergence) |
| `1RB1RB_…_0LE1LE` | 26 | 13 | FAILED (synthetic replay divergence) |
| `1RB1RA_…_1LD0LF` | 51 | 47 | FAILED (non-affine counts) |
| `1RB1RA_…_1LC0LF` | 54 | 48 | FAILED (non-affine counts) |
| `1RB0RA_…_---1RA` | 68 | 62 | FAILED (non-affine counts) |
| dossier-2 `1RB0LC_…` | — | — | MACRO_NOT_EXACT (known phase-sensitive) |
| wiki cryptid `1RB1LA_…` | — | — | MACRO_NOT_EXACT (known phase-sensitive) |

Zero unsafe landings across every machine and every run (the safety
invariant itself never fails; all failures are discharge-machinery
obstructions). Total: 176/269 obligations discharged where fitting applies.

### Method discoveries (v2–v4, forced by Antihydra)

1. **Head-side margin**: a frontier record's head is not always adjacent to
   the nearest interior 1-run; the zero offset is part of the configuration
   and must be captured and reproduced in replay reconstruction.
2. **Far-side margin**: zeros between the last 1-run and the opposite
   frontier are blank-equivalent as tape content but **load-bearing for
   record timing** — the next frontier-expansion depends on the historical
   width. A new per-rule literal self-check (replay the first observed
   firing, demand the exact observed transition and event multiset) caught
   this; it now passes on every rule of every machine, certifying the
   reconstruction is faithful.
3. **Boundary subfamilies**: Antihydra's final obstruction was a window
   occurring in 6/3,003 firings of one rule — exactly the firings whose
   middle block sits at the group-cap boundary value 4 (the final sweep step
   before a merge). The count fitter now supports exactly-guarded boundary
   splits (the event-count analogue of the affine solver's constant-column
   folding), and each boundary subfamily receives its own pinned fresh-value
   synthetic replay.

### Honest scope

`ALL_DISCHARGED_UNIFORM` is uniformity + fresh-value replay evidence for
the induction premise over bounded (100M-step) runs. It is not a proof of
non-halting. The remaining burden for Antihydra is the same single Lean
contract shape as dossier-1's: derive the probe-safety invariant from the
13 macro obligations via raw-to-macro closure induction.

### Next

- Antihydra Lean layer: halt localization (`into-G-only-from` analogue) +
  probe-safety ⇒ non-halting, then the closure-induction contract.
- d7/d6 (24/26): fresh-value divergence — macro state under-determines
  off-trajectory dynamics; likely needs interior-gap components in the
  synthetic template.
- m51/m54/m68: residual non-affine counts — deeper modular/phase structure
  than mod-2..4 + boundary splits.

---

## Antihydra Lean halt-localization layer (2026-08-04)

**File:** `lean/QIG/AntihydraRawTM.lean` (Lean 4, bare core, no sorry;
axioms = `propext` + `Quot.sound` only). Mirror of `Dossier1RawTM.lean`
for `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`.

Machine-checked, unconditional:

- `step_eq_none_iff` — halts in one step iff F reads 0;
- `into_F_only_from_E0` — F is entered only via E reading 0 (`E0 = 1LF`,
  write 1, move left);
- `halt_requires_e_probe_00` — **any raw halt passes through a reachable
  configuration where E reads a 0 whose left neighbour is also 0**;
- `blank_nonhalting_of_e_probe_safe` — `EProbeSafe blankStart → ¬RawHalts
  blankStart`.

`EProbeSafe blankStart` is exactly the invariant stage753 discharged
(13/13 obligations, 14,109 events, zero unsafe landings). Antihydra's
undecidedness is now formally reduced to that single contract.

Also proven (Layer-2 start): the three **sweep lemmas** `sweep_A`,
`sweep_C`, `sweep_E` — Antihydra's self-looping transitions rewrite 1 over
1, so a head crossing a block of n ones leaves the tape literally unchanged;
each is a clean symbolic induction over n. Every stage753 macro-rule
micro-trajectory decomposes into these sweeps plus bounded boundary steps,
so these are the atoms of the closure induction.

---

## Dossier-1 closure induction, phase 1: the caterpillar lemma (2026-08-04)

**File:** `lean/QIG/Dossier1RawTM.lean` (additions; still core-only,
axiom-clean, no sorry).

Micro-trajectory tracing showed dossier-1's dominant macro rule (97.8% of
record transitions, the `(…,a,b,c) → (a+2,b−2,c+1)` sweep) is a five-step
**caterpillar cycle** `A@h → B@(h+1) → B@h → C@(h+1) → D@(h+2) → A@(h+1)`
crawling right across the middle block — and inside the cycle, state C
reads only the 1 that B just wrote. Now proven symbolically:

- `cat_cycle` — one cycle: exact 5-step computation, explicit output tape,
  and the only intermediate C-configuration reads 1;
- `cat_run` — for **all** block lengths n: the caterpillar runs exactly 5n
  steps, ends in A at h+n with the exact predicted tape (`catTape`), and
  **no intermediate configuration has C reading a 0**;
- supporting: `stepN_add` (sequential composition), `writeAt_self`,
  `writeAt_overwrite`.

Consequence: the unbounded core of the dominant rule is now *proven*
C0-probe-free for every block value — the safety of 97.8% of dossier-1's
steps no longer rests on empirical evidence. The C0 probes (the actual
danger points, window `1111·0·1111`) are confined to the rule's bounded
boundary steps, which are fixed finite step sequences — the next phase.

Remaining for `CProbeSafe blankStart`: boundary-step lemmas for the
dominant rule (bounded, computational), the same treatment for the
merge/expansion rules, and the top-level shape-family closure induction.

---

## Dossier-1 closure induction, phase 2: the dominant rule end-to-end (2026-08-04)

**Theorem `dominant_rule_run`** (`lean/QIG/Dossier1RawTM.lean`, core-only,
axiom-clean, no sorry): for every middle-block length `b = m + 4`, from an
L-record of shape `(1, b, 1)` with single-0 gaps, the machine runs exactly
`13 + 5m` raw steps, ends in state `E` at the new right frontier — and
**every C-probe of a 0 during the entire rule has a 1 immediately to its
right** (`CSafeSeg`), for all `m`.

Proof decomposition, all machine-checked:
- `prefix_run` — the 7 boundary steps containing **the rule's single C0
  probe** (the `1111·0·1111` window from the stage748 census), proven safe
  because the probed gap's right neighbour is the first 1 of the middle
  block;
- `cat_run` — the C0-free caterpillar (phase 1);
- `suffix_run` — the 6 exit steps across the right block (no C0 probe);
- glue: `stepN_add`, `CSafeSeg` composition (`csafe_compose`,
  `csafe_of_strong`), and pointwise `catTape` lemmas
  (`catTape_outside` / `catTape_trail` / `catTape_end`).

This is the first macro rule of any machine in this program whose safety
is *proven for all block values* rather than discharged empirically — the
stage750 obligation for this rule is now a theorem. Remaining for
`CProbeSafe blankStart`: the same treatment for the merge and expansion
rules (same technique, different bounded segments), R-side records, and
the top-level shape-family closure induction gluing records together.

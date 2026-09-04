# Conjecture-reduction analysis: do the 115 closures collapse to a few roots?

**Date:** 2026-09-04.
**Author tooling:** `qgkit/bb6/conjecture_reduction.py` (reproducible;
reads TM codes straight from the Lean sources and joins
`experiments/outputs/audit_openset.jsonl`).

**Honesty note up front.** Only two kinds of statement in this document
are *proofs* of equal dynamics: (a) exact equivalence under state
relabeling, and (b) the proven law-level reductions already committed in
the closures (the d2/d3 mirror, the named sibling families). Everything
else — the single-transition "skeleton families," the growth-signature
grouping, the branching-constant reading — is **heuristic structural
evidence** that machines share a generalized-Collatz map. It is *not* a
proof that the `Safe…Orbit` conjectures are inter-reducible. Moving a
fatal probe cell, in particular, keeps the growth map but changes *which*
orbit event is fatal, so two skeleton-siblings have closely related but
not literally identical `Safe…Orbit` predicates. No conditional result
is relabeled unconditional here, and no reduction is claimed as proved
beyond the ones already in the kernel.

---

## 1. The cohort

115 kernel-checked conditional non-halting closures, each reducing
`RawHalts` to one `Safe…Orbit` conjecture:

- **109** `SafeD<n>Orbit` closures, dossiers **7–119** (gaps at
  4,5,6,32,36,84).
- **6** named closures with their own conjecture: **d1 Cohomo**, **d2
  Piasa**, **d3 Grafton Piasa**, **d5 Big Muddy** (rank-1), **d6
  Dvisetu**, **Antihydra**.

Of these, **8 carry an explicit extracted affine / renewal law** (d1,
d2, d3, d5, d6, d7 Kaskaskia, d8 Cahokia, Antihydra). The remaining
**~107 are raw-step corridor closures**: closed from a halt corridor + a
record definition + a 20M-step fail-closed mirror, with **no per-cycle
affine law extracted**. For those, the only abstract-map information
available is the audit growth signature.

**Audit join:** 97/115 codes match `audit_openset.jsonl` by exact code
(the 18 misses are the low/named machines the open-set audit records
under a different normalization).

---

## 2. Rigorous code-level relations (proofs, and their limits)

Computed over the 12 transition cells (6 states × 2 bits) of each TM:

| relation | method | result |
|---|---|---|
| exact relabeling equivalence | lex-min canonical over state perms fixing start-state A | **0 collapses** — all 115 are distinct up to relabeling |
| syntactic BB mirror | L↔R reversal + canonical relabel | **0 pairs detected** |
| single-transition variant | Hamming ≤ 1 over the 12 cells | **26 machines collapse into 7 roots** |

**Key negative result — the proven mirror is invisible to code-level
tools.** d2 and d3 are a *proven* mirror pair (one renewal law,
reflected), yet they are **not** syntactic BB-mirrors: their
mirror-canonical forms differ and their transition tables sit at Hamming
distance 10. The d2/d3 reduction lives entirely in the **record-level
renewal map** (the five-integer `R(a,b)` of `renewal_analysis3.py`),
reflected — not in the raw transition table. Consequence: **syntactic
clustering gives only a lower bound on reducibility.** The reductions the
program actually proved live in the abstract dynamics and are not
recoverable from the code.

---

## 3. The reduction graph

### Rigorous single-transition skeleton families (the only code-level collapses)

The differing cell in every one of these families is **cell index 10 =
state F, read 0** — i.e. the fatal / undefined-probe transition. These
are literally the same machine skeleton with the fatal probe relocated,
so they share one growth map.

| family | dossiers | size | growth signature (audit, uniform) |
|---|---|---|---|
| **F1** | D69–D80 | **12** | one-sided-right, record right, l/r_nstate = **5/3**, one-cell probe — identical across all 12 |
| **F2** | D82–D93 | **11** | one-sided-left, record left, l/r_nstate = **3/5**, one-cell probe — identical across all 11 |
| P1 | D101, D102 | 2 | differ only in F0 target (0LD↔1LC) |
| P2 | D53, D54 | 2 | differ only in F0 target (1LA↔1LC) |
| P3 | D55, D56 | 2 | differ only in F0 target (0LA↔0RA) |
| P4 | D57, D58 | 2 | differ only in F0 target (1RB↔1RC) |
| P5 | D59, D61 | 2 | differ only in D0 target (0RA↔1RA) |

The two big families have **perfectly uniform** growth signatures (12/12
and 11/11 identical `(sidedness, record_side, l_nstate, r_nstate,
probe_kind)` tuples) — the strongest available structural evidence that
each family is a single generalized-Collatz map with a movable fatal
event.

### Proven law-level families (already in the kernel; not code-level detectable)

From the closure write-ups (`docs/submissions/cryptid-names.md`,
`campaign-consolidation`). These are asserted at the law/record level;
the syntactic tools above do **not** see them.

- **d2 / d3** — Piasa & Grafton Piasa: **proven mirror pair**, one
  Euclid-and-Collatz five-integer renewal law reflected.
- **d7 / d8** — Kaskaskia & Cahokia: sibling laws, same unary-ladder
  renewal at opposite ladder parity (d8 adds an epoch counter g).
- **d14 / d15** — Mazon & Braidwood Tully: documented as the *same
  machine, table swapped* (same species certified twice).
- **d16 / d17 / d18** — the rest of the Tully beds: same two-ended
  grower family as d14/d15.
- **d10 / d11** — Farmer City & Cairo: the "dip-aware pair."

---

## 4. Root count

| accounting | independent roots (from 115) |
|---|---|
| exact-equiv + syntactic mirror + single-transition variant (Hamming ≤ 1) | **89** |
| … + looser variant (Hamming ≤ 2) | **85** |
| … additionally crediting the proven law-level families of §3 | **≤ ~80** (not decidable by these tools; see note) |

**Reading.** At the level of *rigorous code-level identity*, the cohort
does **not** dramatically collapse: 89 of the 115 conjectures remain
structurally distinct. The collapses that do occur are real and sharp —
two families of 12 and 11 machines that are the same skeleton with a
moved probe, plus five twin pairs — removing 26 machines into 7 roots.
The proven law-level families (§3) shrink the true independent count
further, but because those reductions are semantic (invisible to the
transition table), **the structural methods here cannot certify the
lower number**; 89 is an honest *upper bound* on independent roots
reachable by code-level analysis, and the true count is smaller but not
pinned down by this analysis.

**Largest clusters:** F1 (D69–D80, 12 machines) and F2 (D82–D93, 11
machines).

**Reducibility to Collatz / Antihydra.** The program's own verdict
(`2026-09-04-goal-resolution.md`) is that the *entire* cohort is
Collatz-class: every closure reduces to an orbit conjecture that no
finite certificate decides, backed by five independent negative results
(no congruence invariant to mod 384; ranking-class certificates refuted;
zero invariant-decidable machines across 258+20 probed; zero
eventually-periodic holdouts; zero structurally-unreachable-halt
machines). So all 115 belong to one *family* (generalized-Collatz), but
that is a classification, **not** a proof that any two of the 89
structural roots are inter-reducible. The one machine reduced to a named
external problem is Antihydra (the community's guarded random walk); the
d2/d3 renewal map is Collatz-and-Euclid-flavoured but is its own map, not
the 3x+1 map.

---

## 5. Branching-constant census (C2)

**Known exact constants** (from proven laws — complete only for the 8
law-carrying machines):

| machine | constant | mechanism |
|---|---|---|
| d2 / d3 (Piasa) | **φ** (golden ratio) | Fibonacci death-cone, no-TT constraint; φ also appears as 1/φ in the gambler's-ruin hazard root |
| d7 / d8 (Kaskaskia/Cahokia) | **~3/2** per renewal | unary ladder `(10)^k`, drift-drain + reload |
| d6 (Dvisetu) | **4/3** per cycle | n mod 3 renewal with a divide-by-3 recursing branch |
| d5 (Big Muddy) | **2-adic** (train lengths) | rank-1 trisection word odometer |
| Antihydra | **1** (linear cone) | guarded random walk, a ≥ 2 merge throttle |

**State-geometry census of the joined raw-step tranche (97 machines).**
The audit collapses to exactly **two** mirror-symmetric classes:

- one-sided-right, record right, **l/r_nstate = 5/3** — 60 machines
- one-sided-left, record left, **l/r_nstate = 3/5** — 37 machines

i.e. the whole raw-step holdout tranche is a single one-sided
single-cell-probe grower geometry in two reflections. There are no
two-sided or bounded machines among the joined set.

**Does state-geometry predict the constant? — underpowered; no
predictive claim.** Only **5 distinct** exact constants exist across the
8 law-carrying machines, and all of them sit in the named/low set; the
107 raw-step machines have **no extracted per-cycle multiplier** at all
(only a `max_gap / word_len_at_max` proxy, median ≈ 3.0 left / 3.3 right,
dominated by outliers up to ~2×10⁴ — a growth *proxy*, explicitly **not**
the branching constant). With n = 5 constants there is no statistical
power for a geometry→constant regression, and this analysis makes no such
claim.

What *is* visible is a qualitative association between constant and
**renewal branch arity**, not raw state geometry:

- Fibonacci / no-TT 2-symbol renewals → **φ** (d2/d3),
- **mod-3** renewals → **4/3** (d6) and **3/2** (d7/d8),
- throttled merge (a ≥ 2 guard) → **1** (Antihydra),
- 2-adic train-length branching → **2-adic** growth (d5).

The richer cone constant (φ) is carried by the higher-interaction
machines (d2/d3, two counters + walking holes), while the slow
mod-3 climbers (4/3, 3/2) are the low-state counter machines — a
structural *tendency*, offered as a reading, not a law.

---

## 6. Bottom line

- **Independent roots: 89** by rigorous code-level analysis (exact
  relabeling + syntactic mirror + single-transition variant), an upper
  bound; the true count is lower once the proven law-level families are
  credited, but structural methods cannot certify that smaller number.
- **Largest clusters:** F1 = D69–D80 (12) and F2 = D82–D93 (11), each a
  single skeleton with the fatal probe relocated and a perfectly uniform
  growth signature.
- **26 machines collapse into 7 code-level roots** (the two big families
  + five twin pairs); the differing cell is the fatal F0 probe in six of
  the seven.
- **Branching constants** are known exactly only for the 8 law-carrying
  machines {φ, 3/2, 4/3, 2-adic, 1}; the 107 raw-step machines have no
  extracted constant, so the census is complete only for the named set
  and no geometry→constant predictor can be fit.
- **The whole cohort is Collatz-class** (program's own five-angle
  verdict), but that is a family classification, not a proof of
  pairwise inter-reducibility. The most striking finding is negative:
  the program's *proven* reductions (e.g. the d2/d3 mirror) live in the
  abstract renewal dynamics and are **invisible** to transition-table
  clustering, so code-level structural analysis systematically
  *under*-detects reducibility.

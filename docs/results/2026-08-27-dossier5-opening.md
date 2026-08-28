# Dossier-5: the array-class shape language, opened

**Date:** 2026-08-27 · **Lean:** `busy-beaver-core/BusyBeaverCore/ArrayShape.lean`
(compiles at `[propext, Quot.sound]`) · **Code:** `qgkit/bb6/d5_vectors.py`,
`qgkit/bb6/d5_recurrences.py`

## Mandate

The dossier-4 sweep ended with a boundary: the four certified machines
are the cohort's only fixed-dimension-shape machines in reach;
everything else structured is array-class. Dossier-5 is the response:
a shape language over *growing sequences of blocks*, with the same
discipline as before — empirics fail-closed first, then compiled Lean.

## First decode: the top machine rewrites a word

`1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC` (rank-1 EXACT candidate),
468 entry vectors over 2M steps: its tape at entries is an
**alternating word** — 1-runs of length 1 or 3 (occasionally 2)
separated by single 0s. Episodes are local word rewrites; the dominant
one (126 of 467 transitions) is **block trisection**:

```
(1)  ->  (1, 0, 1, 0, 1)      [one block becomes three; dim +4]
```

with the remaining signatures being the same operation shapes at
larger scales and positions. This is substitution/tag-system dynamics
on a word over a two-letter block alphabet — exactly the class the
reversible v-Collatz vector maps were built for, now with its concrete
first specimen.

## The Lean foundation (compiling today)

`ArrayShape.lean` defines the language every array-class episode
theorem will speak:

- `arrayTape origin blocks` — blocks of 1s with single-0 separators,
  laid out from an origin; `width` for the footprint.
- Evaluation lemmas: `arrayTape_head` (inside the first block),
  `arrayTape_tail` (defer past block + separator), `arrayTape_sep`
  (separators read 0), `arrayTape_before` / `arrayTape_after`
  (0 outside the layout).

The dossier-2/3 compiler stack (simulation-driven atoms, episode
plans, funext normalizations) re-targets onto this vocabulary; the new
difficulty is that episode theorems must quantify over list shapes
(prefix + edited middle + suffix), which the head/tail/append-style
lemmas are designed to support.

## The golden ratio, positioned

Dossier-3's abstract death tree obeys L(k) = L(k−1) + L(k−2) exactly —
golden-ratio branching, sourced in the T-cannot-follow-T alternation,
and equal to the forward factor complexity. We tested whether the
**raw** halt cones of the 11 EXACT machines carry small integer
recurrences: none do (raw constraint-pattern cones mix families), and
one machine's raw growth already sits at ≈ φ (1.6221). The φ finding
is a statement about *abstract* death trees — which array-class
machines do not have until dossier-5 builds their abstract maps. The
standing prediction, falsifiable as the program proceeds: **each
array-class machine's abstract death tree will satisfy a small integer
recurrence, with a per-machine Pisot-like constant determined by its
episode-alternation constraints** — the golden ratio being the
founding example (no-TT), with other alternation rules yielding other
constants (plastic, supergolden, …).

## Roadmap

1. Fail-closed word-rewrite calculus for the rank-1 machine
   (trisection + companions, with exact step costs).
2. Substitution-system abstract map (word ↦ word) and its death tree —
   the recurrence prediction gets its first test.
3. Episode compiler re-target: plans over (prefix, middle, suffix)
   list shapes; atoms unchanged in spirit.
4. The conditional closure, array-class: `SafeWordOrbit → ¬ RawHalts`.

## Honest scope

One machine decoded at entry-vector level; the trisection calculus is
observed, not yet fail-closed-validated; the Lean layer is a
foundation, not yet an episode engine; the recurrence prediction is a
prediction.

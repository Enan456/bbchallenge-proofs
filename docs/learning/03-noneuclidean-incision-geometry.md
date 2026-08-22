# Set 3 — Incision geometry: a non-Euclidean program for boundary-only checking

**Status: research program.** Nothing in this document is implemented or
proven yet. It is the design rationale for plan 3. Where Sets 1–2 are
finished mathematics, this is a hypothesis about *where to look next* — and
it must be held to the same honest-labeling standard as the rest of the repo.

## The core idea, stated plainly

Set 2 shows that for collapse-like machines, everything dangerous is
concentrated at **incisions**: the rare abstract states where the orbit's
next move is not the dominant rule. Concretely, for Antihydra
(`astep : AState → Option AState` on triples `(a, m, c)`):

- the **death set** (halt opportunity) is exactly
  `D = { (a, m, c) | m = 0 } ∪ { (a, 2, c) | a ≤ 1 }` — where `astep`
  returns `none`;
- the **incision set** (where anything other than the frozen-counter hydra
  rule happens) is the boundary region `m ∈ {1, 2}` — every drop and merge,
  i.e. every change to the counter `a`, happens there.

Between incisions the dynamics are *closed-form*: from `(a, m, c)` with
`m ≥ 3`, exactly `⌊(m−1)/2⌋` hydra steps fire deterministically, each
`(a, m, c) → (a, m−2, c+3)`, before the orbit re-enters `m ∈ {1, 2}`. So the
machine's entire fate is decided by the **sequence of boundary events** — a
much sparser process than either raw steps (10⁸ observed) or even abstract
steps. The efficiency claim of this program is exactly that: *certified
event-skipping*. Prove the closed-form jump between consecutive boundary
hits once, and both simulation and proof obligations only ever need to be
evaluated **at the boundaries**, "catching" each incision as it happens
rather than scanning for it.

That much is ordinary discrete math, and is provable in core Lean today. The
geometric layer is the second half of the idea.

## Why non-Euclidean coordinates

The boundary-event process for Antihydra is a walk on `(a, c)` where the
values grow without bound (`c` gains +3 per hydra volley; `a` drifts via
−1 / +2 coin-flips at drops/merges). In raw (Euclidean) coordinates the
trajectory races off to infinity and every plot degenerates. The natural
normalizations are:

- **logarithmic coordinates** `(log a, log c, log t)` — multiplicative
  growth becomes additive, and the affine rules become approximate
  translations. Exponentially growing trajectories become quasi-geodesics;
- **projective/simplex coordinates** `(a : m : c) / (a + m + c)` — the orbit
  becomes a bounded trajectory on the 2-simplex, and the death set `D`
  becomes a genuine *boundary face* of the space, which is the precise sense
  in which "incisions live on the boundary";
- the **hyperbolic upper half-plane ℍ²** unifies both: a point at height `y`
  models scale, and exponential expansion in value is unit-speed motion in
  the metric `ds² = (dx² + dy²)/y²`. Systems with exponential orbits and
  rare boundary interactions (continued fractions via the Gauss map,
  geodesic flow coding) are classically analyzed exactly this way. The
  hypothesis is that in ℍ²-normalized coordinates the incision events of a
  collapse-like machine trace a *stable geometric figure* (an invariant
  curve, horocycle-like level set, or bounded-distortion region) whose shape
  is machine-characteristic — while in Euclidean coordinates the same data
  looks like unstructured escape.

**Honesty box.** The choice of ℍ² is a modeling hypothesis, not a theorem.
No known invariant separates Antihydra's orbit from its death set — if one
existed, the Antihydra conjecture would be solved. What geometry can
realistically deliver, in increasing ambition: (1) a rigorous, certified
acceleration framework (boundary-only checking — provable now), (2) a
visual/empirical taxonomy of incision figures across the 51 compact-growth
machines (may reveal shared structure the per-machine view hides), (3) for
*some* machines, a provable safety margin — a geometric invariant keeping
the orbit at positive distance from the death face, which would upgrade a
conditional reduction to an unconditional non-halting proof. (3) cannot work
for Antihydra-class machines unless the underlying arithmetic conjecture
falls, and no claim otherwise should ever be made.

## What "graphing the incisions" concretely means

For each machine with a proven (or empirically exact) orbit emulation:

1. Run the *abstract* orbit (cheap — thousands of events, not 10⁸ raw
   steps), recording only boundary events: `(event index, rule fired, state
   before/after, distance-to-death-set)`.
2. Embed each event via the chosen chart (log / simplex / ℍ²) and plot the
   incision point cloud and its time-ordering.
3. Measure: drift and variance of the distance-to-death coordinate, return
   times to the boundary region, and whether the normalized cloud is
   bounded, recurrent, or escaping.
4. Compare figures across machines: the stage745 delta-rule families (e.g.
   the three machines sharing the `(−2, 3)` transfer rule) should produce
   near-identical figures if the hypothesis has content.

## What the Lean side would look like

Split into two packages to protect the trust base:

- **`BBChallenge.Incision` (core-only, provable now):** for each machine,
  the boundary decomposition of `astep` (`astep s = none ↔ s ∈ D`, with `D`
  as an explicit decidable predicate), the closed-form **volley lemma**
  (`aorbitN` jumps between consecutive boundary states in one application),
  and the equivalence `SafeOrbitA ↔ the boundary-event process never enters
  D`. This makes "check only at the boundaries" a theorem, not a heuristic,
  and gives the Python side a certified acceleration it can mirror.
- **`BBChallenge.Geometry` (separate Lake package, may import mathlib):**
  the chart `φ : AState → ℚ × ℚ` (exact rational log-surrogates or simplex
  coordinates — avoiding `ℝ` where possible), statements of the form
  "the event process preserves region `R`" for candidate invariant regions
  `R` found empirically, and — only if an `R` disjoint from `D`'s image is
  ever found and proven invariant — the resulting unconditional non-halting
  corollary, imported back through the Set 2 reduction.

The dependency direction is strict: Sets 1–2 never import Set 3, so the
existing axiom-clean results are untouched no matter how speculative the
geometry gets.

# Lemma B probed: cross-cylinder coherence is friendly, and raw Erdős–Turán is the wrong tool

**Date:** 2026-09-09. Attacks the arithmetic core of the density form (Lemma B
of `sequential-integer-bound.tex`): the empirical offset exponential sum
`E_h = (1/M) Σ e(h·z_d)` must be small up to native frequency `h ~ S` for the
count `P[o_d∈{1,3,5}] ≤ C/S` to hold. The concern was that the ~`λ^d` depth-`d`
cylinders might *conspire* — their linear-form resonances aligning to rebuild a
large `E_h` (the adversarial case, which would make Lemma B genuinely
Tao-hard). We measured it. **The coherence is friendly.** But there is a real
methodological finding attached: raw Erdős–Turán is lossy here, and the honest
path is a smoothed count.

## What was measured

Over ~1.7×10⁶ F-visits in a fixed scale band (bit-length 15–19), histogram the
`z = o/(o+β)` values into `2^17` bins and FFT to get `|E_h|` at all frequencies
at once.

**Finding 1 — no high-frequency resonance growth.** `|E_h|` follows the
density's `~1/h` shape at low `h`, then flattens by `h≈100` to a floor of
~3–4× the pure-noise level `1/√M`, and *stays at that floor* with no growth all
the way to `h≈65000`. The octave-envelope max is ~3–4× noise across every octave
from `h=64` to `h=65536`. The cylinders do **not** conspire.

**Finding 2 — the 3-adic structure is low-frequency only.** Since
`det P_k = ±3^{k+1}`, 3-adic frequencies were the natural suspects. They spike
only at the bottom: `h=3` is 6.8× its local median, `h=9` is 2.6×, `h=27` is
1.3×, and by `h=81` the 3-adic frequencies are unremarkable (ratio ≈1). No
persistent 3-adic conspiracy — the opposite of the adversarial case.

**Finding 3 — the floor is essentially sampling noise.** Varying the ensemble
size, the high-frequency median `|E_h|` (h∈[1024,4096]) scales close to
`1/√M`: it drops by 1.75× then 1.53× as `M` quadruples (pure noise would be
2.00×), i.e. it decays like `1/√M` with a slight excess. That slight excess is
most consistent with orbit-correlation in the sampling (F-visits along one orbit
are not independent), not a genuine resonance floor. Reading: the *true*
high-frequency `E_h` is at or near zero — cross-cylinder cancellation is
essentially **complete**.

## The methodological finding: raw Erdős–Turán is lossy

`sequential-integer-bound.tex` showed raw Erdős–Turán gives only an `O(1)`
discrepancy, and called that the obstruction. The measurement clarifies *why*,
and it is not a genuine obstruction. Erdős–Turán is a worst-case bound over all
intervals; its `Σ (1/h)|E_h|` is dominated by the **low-frequency** terms, where
`|E_h| ~ 1/h` merely encodes that the invariant density `h(z)` is not flat — a
harmless macroscopic fact that says nothing about small-offset concentration.
The **fine** equidistribution lives in the high-`h` terms, and those are at the
noise floor. So the `O(1)` is an artifact of conflating the density's shape with
its fine structure. The right tool is a **smoothed count**: test against a bump
`φ` of width `~6/S`, so `P[o_d∈{1,3,5}] ≤ ∫φ·h_d + Σ_h φ̂(h) E_h`. The main
term is `h(0)·O(1/S)` (the local density value), and the error weights the
high-`h` (noise-floor) `E_h`, where cancellation holds — separating the two
regimes that Erdős–Turán merged.

## Honest status of Lemma B

**Reframed from "possibly adversarial, Tao-hard" to "friendly, plausibly
provable, ingredients identified."** The probe shows the cylinders do not
conspire and the offsets equidistribute at native resolution essentially
perfectly. The route to a proof now has two identified, standard ingredients:
1. **Cross-cylinder incoherence:** the offset forms `(u_C,v_C)` are pairwise
   incommensurable (entries of distinct matrix products `∏P_{k_j}`), so their
   per-cylinder linear sums (Lemma, classical) add *incoherently* — a
   square-root, not linear, accumulation. This is the "no conspiracy" statement,
   now strongly supported numerically.
2. **Smoothed count** in place of raw Erdős–Turán, to isolate the local density
   value from the fine equidistribution.

**What this is NOT.** It is not a proof. The measurement is over a finite scale
band and finite `M`; the slight-above-`1/√M` excess wants a clean explanation
(orbit-correlation is the likely one, but unproven); and turning "incommensurable
forms add incoherently" into a theorem *uniform in the ~`λ^d` cylinders and in
scale* is exactly the estimate still to be written — the genuine analogue of
Tao's characteristic-function bound. What changed is the expectation: the
structure is friendly, so this is a hard-but-standard exponential-sum estimate,
not a fight against an adversarial arithmetic conspiracy. The dynamics (gap,
uniform in scale and branches) was already controlled; the arithmetic core now
looks tractable by known methods rather than needing a new idea.

Measure form unconditional; specific orbit Collatz-hard; density form
conditional on this (now friendly-looking) estimate.

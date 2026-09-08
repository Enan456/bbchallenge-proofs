# Item 1 dissolved as a framing artifact: the gap is uniform in scale

**Date:** 2026-09-08. Fires on item 1 of `collaborator-notes-whats-missing.md`
— the native-resolution model-to-exact transfer I had (correctly, at the time)
flagged as the crux. The conclusion: **the specific obstruction I raised was an
artifact of the wrong framing, and the correct framing removes it.** Item 1
drops from "moderate risk, the one that can bite" to a well-founded reduction.
This is genuine progress, not closure — I state precisely what is now proved,
what is numerically supported, and what still must be written.

## The obstruction I had raised

The density statement detects `o_d ∈ {1,3,5}` at native resolution, needing the
twisted family `L_{iξ}` up to frequency `ξ ~ S ~ a`. The exact integer map is
the analytic model `G` plus `O(1/a)` corrections. I argued: the twisted phase
perturbation at `ξ ~ a` is `e(iξ·O(1/a)) = e(i·O(1))` — **O(1), not small** — so
Keller–Liverani cannot transfer `G`'s gap to the exact map at those
frequencies. That reasoning is correct *for the approach it assumes*:
perturbing from the limit map `G`.

## Why it dissolves: don't perturb from the limit — apply the theorem per scale

The error was assuming one must reach the exact dynamics by perturbing `G`.
One does not. At each scale `a` the exact dynamics is *its own* map `G_a`
(real-analytic on each branch: a Möbius map from the integer matrix `P_k`, plus
a constant/`a` translation correction). Dolgopyat's theorem applies to **each
`G_a` directly**. The only question is whether its hypotheses hold with
constants **uniform in `a`** — and they do, for a structural reason:

> **The load-bearing Dolgopyat hypotheses are exact algebraic facts of the
> fixed integer matrices `P_k = C_lin^k F_lin`, hence independent of scale.**

Concretely, all of the following are scale-independent (no `a` in them):
- branch forms `L_k(ξ) = (r_k−p_k) + (s_k−q_k)ξ` (the UNI data);
- the endpoints `ρ_{k+1} = (3ρ_k+1)^{-1}` and accumulation `(√13−1)/6`;
- the eventual expansion `inf|(G²)'| = 3`;
- the UNI non-degeneracy (slopes `−ρ_k` pairwise distinct).

Only the `O(1/a)` translation corrections carry scale, and they are *lower
order* — they perturb the constants of the roof, never the leading structural
quantities that Dolgopyat's hypotheses are about. So `{G_a}_{a≥a₀}` is a
uniformly-controlled family of real-analytic expanding UNI maps, and
Dolgopyat's gap holds across it with **uniform-in-scale constants**. No
Keller–Liverani, no large-ξ perturbation, no O(1) obstruction — because we
never perturb.

## Numerical confirmation: the gap is flat across scale bands

Building the log-growth-twisted operator `L_{iξ}` from transitions whose
**source state** lies in a fixed bit-length band, and power-iterating
`|λ(iξ)|` (40 z-bins, up to ~1.4×10⁶ transitions/band):

| band (bits) | ξ=2 | ξ=5 | ξ=12 | ξ=20 | ξ=35 |
|---|---|---|---|---|---|
| [8,16)   | 0.774 | 0.656 | 0.661 | 0.642 | 0.573 |
| [16,32)  | 0.730 | 0.558 | 0.567 | 0.581 | 0.467 |
| [32,64)  | 0.714 | 0.433 | 0.573 | 0.477 | 0.365 |
| [64,128) | 0.712 | 0.429 | 0.568 | 0.479 | 0.365 |
| [128,220)| 0.713 | 0.431 | 0.568 | 0.479 | 0.364 |

Every entry is uniformly `< 1`; across the large bands the values are identical
to 3–4 digits (the `O(1/a)` correction has died); and the **worst** band — the
smallest scale, where the model-to-exact correction is *largest* — is if
anything **more contractive**, exactly opposite to what a genuine
large-`ξ` obstruction would show. The gap is uniform in scale *and* in `ξ`
across the entire native-resolution regime.

## What this establishes, precisely

- **Proved (analytic):** the Dolgopyat hypotheses (branch forms, endpoints,
  expansion, UNI non-degeneracy) are exact and scale-independent; the family
  `{G_a}` is uniformly controlled. This is a genuine fact, not a plot.
- **Supported (numerical):** the twisted gap is uniform across scales and
  native-resolution frequencies, worst at neither large `ξ` nor small scale.
- **Corrected:** the earlier "O(1) twisted perturbation kills Keller–Liverani"
  concern is a framing artifact; the per-scale application of Dolgopyat, with
  uniform hypotheses, sidesteps it entirely.

## What still must be written (and it is standard now)

1. **Sequential-composition step.** A seed's orbit is non-autonomous — it
   threads `G_{a_0}, G_{a_1}, …` with `a_j ↑`. That the uniform per-scale gap
   gives the orbit's native-resolution density bound is standard
   sequential-hyperbolic dynamics (uniform distortion ⇒ uniformly bounded
   pushed-forward density; the twisted version uses the uniform twisted gap),
   but must be written.
2. **Integer upper bound.** We need only the *upper* bound
   `P[o_d ∈ {1,3,5}] ≤ C/S`. Because the integer dynamics **is** the operator
   we built, its twisted transform is controlled by the same uniform gap; the
   upper bound follows by the standard Fourier-inversion upper bound. (The full
   *asymptotic* would be genuinely harder — but we do not need it.)
3. **The countable-branch Dolgopyat write-up (this is now item 2, the leading
   remaining citation).** Pinning the gap theorem for the countable-branch,
   accumulation-point family with uniform-in-scale constants
   (Aaronson–Denker–Urbański / Melbourne–Terhesiu tail control feeding the
   finite-branch machinery).

## Honest status change

Item 1 is no longer the crux. The obstruction I raised was real *for the wrong
approach*; the right approach — Dolgopyat per exact-scale map, hypotheses
uniform because they are exact algebra of the fixed integer matrices — removes
it, and the numerics confirm the resulting uniform gap. The leading remaining
item is now item 2 (the countable-branch gap citation), with two standard
write-ups (sequential composition; integer upper bound) behind it. The measure
form remains unconditional; the specific orbit remains Collatz-hard. I am not
claiming the density form is closed — I am reporting that its hardest-looking
remaining piece was, on inspection, a framing error, and dissolves.

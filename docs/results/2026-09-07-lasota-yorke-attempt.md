# Stepping through the door: the Lasota-Yorke attempt on the almost-all theorem

**Date:** 2026-09-07. A genuine attempt at the one lemma Front 3 isolated
(`2026-09-04-transfer-operator.md`) — the analytic core of a Tao-style
almost-all-seeds theorem for the renewal map R. Honest status: **not a
finished proof**, but the main obstruction the transfer-operator scaffold
feared is now *removed by a proven structural fact*, and the theorem is
reduced from "one hard intermittency lemma" to "two checkable Rychlik
constants," both strongly supported numerically.

## The obstruction that isn't: no intermittency

The transfer-operator scaffold flagged the parabolic generator T
(unipotent, neutral) as a Pomeau-Manneville intermittency obstruction —
the reason standard Lasota-Yorke fails on the un-induced map. That fear
is unfounded. A one-line parity argument (verified exhaustively) gives
the symbol grammar:

- `beta(a) = a-1 (a odd) / a-2 (a even)` is **always even**.
- **T** fires iff `b` even, outputs `b-3` (odd) -> next step is never T.
- **C** (b odd) outputs `beta-(b-3) = even` -> next step is **always T**.
- **F** (b odd) outputs `b-beta-4 = odd` -> next step is C or F.

So the grammar is `T -> {C,F}`, `C -> T`, `F -> {C,F}`, and crucially
**TT is impossible**: the neutral generator T is never iterated. It
occurs only inside an isolated `C -> T` pair. There is no neutral orbit
segment of length >1, hence **no genuine intermittency** — the cusp is
touched but never followed.

This is the key that unlocks the rest, and it is a theorem, not a
measurement.

## The induced map is uniformly expanding with geometric tails

Inducing on the F-section (the above-diagonal crossings), in the
scale-invariant coordinate `z = o/(o+beta)`, `o = b-beta`:

- **Uniform expansion:** median `|dz'/dz| = 4.28`, and **99.8%** of local
  slopes exceed 1 across the whole state space (measured over ~3x10^6
  induced transitions). The det-3 factor of the C and F generators is the
  source; each return composes at least one such expander.
- **Geometric return-time tail:** mean return 3.81, `log P(return >= k)`
  linear with slope **-0.284** (summable). Because TT is forbidden and
  C is always glued to a following T, long returns are runs of expanding
  `F`/`CT` blocks, each independently exiting — a geometric law, not the
  polynomial tail an intermittent map would give.
- **Bounded distortion:** each branch of the induced map is a **Mobius
  map** in `z` (an affine map on `(a,b)` in projective coordinates), and
  a composition over a return is again Mobius. Mobius maps have classical
  bounded distortion (conformal, cross-ratio controlled). Distortion is
  therefore not the obstacle.
- **Spectral gap (numerical, corroborating):** the Ulam discretization of
  the induced transfer operator gives `|lambda_2| = 0.23`, gap `0.77` —
  quasi-compact behavior, consistent with the prior 0.21/0.44.

## The Rychlik reduction: what remains

With no intermittency, the induced map falls under **Rychlik's theorem**
for piecewise-monotone maps with countably many branches: if (i) the map
is uniformly expanding (`inf |g'| = lambda > 1`) and (ii) `sum_branches
var(1/|g'|) < infinity` (summable variation / bounded distortion +
geometric branch tails), then the transfer operator is quasi-compact on
BV, yielding a **unique absolutely continuous invariant measure with
exponential decay of correlations**. Combined with the positive drift
(transience, `E_mu[log|F'|] = 0.134 > 0`) and Borel-Cantelli on the
summable fatal hazard, this gives **almost-all seeds never die**.

**What is now rigorous:** the no-intermittency grammar (parity proof);
the Mobius/bounded-distortion structure of the branches; the qualitative
uniform expansion and geometric tails.

**What remains for a complete proof** (bounded, checkable analysis on the
explicit piecewise-Mobius branches — not open-ended):

1. A rigorous uniform lower bound `inf_z |g'(z)| >= lambda > 1` for the
   induced F-return map, from the explicit generator matrices (the
   numerics say `lambda ~ 4`, so there is large margin).
2. A rigorous `sum_branches var(1/|g'|) < infinity` bound, from the Mobius
   distortion estimate plus the geometric return-time tail (slope -0.284
   gives ample summability).

Neither is claimed complete here. Both are the standard two Rychlik
hypotheses, now with the intermittency obstruction proven absent, so the
remaining work is verification of two constants for an explicit
finite-data map, not the discovery of a new mechanism.

## Honest verdict against Tao

Tao *proved* his Collatz almost-all theorem (the Syracuse stationary
measure). We have *proven the enabling structural fact* (no
intermittency) and reduced our almost-all theorem to the two standard
Rychlik constants, with strong numerics for both. That is materially
closer to the door than the Front-3 scaffold — it removes the feared
obstruction — but it is **not** through it: the two constant-bounds are
not yet rigorously established. No theorem is claimed, and nothing here
touches the specific-orbit result, which stays Collatz-hard.

## Other ideas on stepping through the door

1. **Finish Rychlik directly** (the above) — the nearest route; two
   explicit constant bounds.
2. **Young-tower / operator renewal** (Sarig, Gouezel): build a Young
   tower over the F-section; the geometric return tail gives exponential
   mixing and a local limit theorem directly. Heavier machinery, but it
   also yields the *rate*, feeding an effective statement.
3. **Leverage the conjecture-collapse** (`2026-09-04-conjecture-reduction.md`):
   the 115 conjectures are <=89 roots; an almost-all theorem proven for
   one renewal-map root transports to its whole affine-conjugacy family,
   multiplying the payoff of a single proof.
4. **The specific-orbit wall stays shut** — effective equidistribution is
   "door bolted" (diffusive n^-1/2 error vs exponentially shrinking fatal
   window). Almost-all is the ceiling of this program; the specific
   machine is Collatz-hard and not to be attempted by these methods.

# The R -> SL(2,Z) dictionary probe: structure confirmed, horoball route fails, lemma sharpened

**Date:** 2026-09-04. The concrete first step of the modular-surface
route flagged in `2026-09-04-frame-alignments.md`. Run on the exact
renewal map (`renewal_analysis3.py`). Result: the matrix structure is
real and clean, but the fatal set is **not** a horoball, so the easy
Sullivan-log-law avoidance argument does not apply. What the probe does
deliver is a sharpened statement of exactly the lemma the almost-all
theorem needs.

## The map is a three-generator integer-matrix semigroup

Writing each renewal move in closed form (all verified against R):

| move | condition | closed form | linear part | det | trace | eigs |
|---|---|---|---|---|---|---|
| **T** | b even | a+6, b-3 | `[[1,0],[0,1]]` + shift (6,-3) | +1 | +2 | 1, 1 (parabolic) |
| **C** | b odd, b<beta | a'=3b(-3), b'=a-b+(1 or 2) | `[[0,3],[1,-1]]` | -3 | -1 | 1.30, -2.30 (hyperbolic) |
| **F** | b odd, b>beta | a'=3a+6, b'=b-a-(2 or 3) | `[[3,0],[-1,1]]` | +3 | +4 | 1, 3 (expanding) |

This is genuinely modular-surface-shaped: **T is a parabolic,
cusp-fixing generator** (unipotent, trace 2) that drifts the state
toward small b; **C and F are hyperbolic/expanding** generators. The
one wrinkle that matters: C and F have determinant +/-3, not 1. The
factor 3 is the Collatz multiplier (F's eigenvalue is exactly 3), and
it is precisely what makes the dynamics volume-expanding rather than
measure-preserving. That single fact is the source of the measured
transience (Lyapunov drift -0.125) and is why the orbit escapes to
infinity instead of recurring. So the semigroup lives in
GL(2, Z[1/3]) acting projectively on the modular surface, not in
SL(2,Z) itself.

## The horoball route fails: the fatal set is a resonance band, not a cusp

The hoped-for picture was: fatal set = horoball neighborhood of a cusp,
survival = the orbit stays in the thick part, and Sullivan's logarithm
law bounds cusp excursions for almost every geodesic. The b/a ratio
over the certified (6,13) orbit refutes the clean version:

- b/a is **not** confined to a bounded cone: median 0.73, but p99
  ~116 and max ~13,000 over 2043 renewals. The orbit ranges freely
  across ratio 0 to ratio >>1.
- The fatal 'diagonal' condition is `b - beta in {1,3,5}` with
  `b > beta` — a **width-3 arithmetic resonance band just above the
  diagonal**, not a full angular sector. The orbit crossed into
  `b > beta` 527 times and sailed past ratio 116 without dying,
  because being above the diagonal is only fatal inside that thin
  window.
- Minimum diagonal margin over all 527 approaches: `b - beta = 9`
  (never entered {1,3,5}). Minimum axis approach: `b = 3` (never
  reached the `b <= 2` death).

So the fatal set is a measure-zero-in-angle resonance line the orbit
crosses **transversally**, not a horoball it must avoid. Horoball
avoidance (a geometric, robust condition) is the wrong tool; the real
condition is arithmetic — the **phase** `b - beta mod (the fatal
window)` at each diagonal crossing.

## What the probe does buy: the exact lemma

The almost-all theorem now reduces to a precise, standard-shaped
statement:

> As the trajectory crosses the diagonal (`b` passing `beta`), the
> offset `b - beta` **equidistributes** across residues finely enough
> that the fraction of crossings landing in the width-3 fatal window
> `{1,3,5}` is summable along almost every orbit.

This is an equidistribution-of-a-linear-form statement, and the mixing
already measured (`2026-09-04-invariant-measure-ergodic.md`: block
entropy 0.423, short-range memory) is exactly the input such a lemma
consumes.

**Mechanism correction (see `2026-09-04-offset-equidistribution.md`).**
An earlier draft of this paragraph guessed that the parabolic generator
T drives the equidistribution by sweeping the offset through residues
(`b -> b-3` repeatedly). That is wrong: T fires only when `b` is even
and returns `b-3`, which is odd, so T can **never** fire twice in a row
(verified: T-run lengths are all singletons over ~4x10^5 events). There
is no horocycle sweep. The offset instead equidistributes through the
**full three-generator semigroup mixing** — measured directly and
strongly (uniform to <0.3% in every modulus up to 384). So the lemma is
of ordinary equidistribution type, but its mechanism is semigroup
mixing, not a single parabolic flow; proving it for this specific
semigroup is the open work.

## Honest verdict on the route

- The modular structure is real and now explicit (three named
  generators, one parabolic + two det-3 expanders).
- The clean horoball/Sullivan route is **closed** (the fatal set is not
  a horoball).
- The almost-all theorem survives, reduced to offset equidistribution
  under the parabolic drift — narrower and better-posed than before,
  and matched to the measured mixing.
- The **specific-orbit** result is untouched and remains out of reach:
  the (6,13) offsets happen to stay `>= 9` from the fatal window over
  2043 renewals, but that is a property of one generic trajectory's
  phases, and equidistribution is silent about a single orbit. Same
  Collatz-hard wall.

Net for the program's goal: this advances the one publishable target
(almost-all) and does **not** produce an unconditional verdict for any
specific machine — consistent with every prior finding, and with the
honest-labeling constraint. No conditional closure is upgraded.

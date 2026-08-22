# Incision Geometry: Checking Only Where the Cut Can Happen

*NotebookLM source document 3 of 4 — the boundary-only-checking theorem and
the geometric program. Self-contained.*

## The idea in one breath

For collapse-like Busy Beaver machines, everything dangerous is
concentrated at rare events the project calls **incisions** — the moments
the orbit touches an explicit boundary set where a counter can move or the
orbit can die. Between incisions the dynamics are completely deterministic
and can be skipped in closed form. So instead of simulating a hundred
million raw tape steps, or even every abstract step, you only ever need to
look at the boundary — and this is not a heuristic: it is a theorem.

## The certified part

For Antihydra's abstract orbit on triples (a, m, c):

- **The death set is explicit**: the orbit can die only at m = 0, or at a
  drop (m = 2) with the counter a at 1 or less. Theorem `astep_dies_iff`
  proves this is exact — no other state can kill the orbit.
- **The volley is closed-form**: from any state with m ≥ 3, a deterministic
  run of counter-frozen hydra steps lands on the boundary at
  (a, 2 − m mod 2, c + 3⌊(m−1)/2⌋). One formula replaces the whole run.
- **The event process** applies one boundary rule, then one volley: exactly
  one event per counter movement.
- **The incision theorem** (`eventSafe_iff_safeOrbitA`): the event process
  dies *if and only if* the full orbit dies. Boundary-only checking is
  certified sound **and** complete — you lose nothing by never looking
  between events. Chained with the machine reduction: if the event process
  never dies, Antihydra never halts.

All of this is machine-checked in core Lean 4 with the same two-axiom
budget as the rest of the development.

## The measured acceleration

The numbers are dramatic. In the incision atlas (experiment stage756):

- The first **16 incision events** cover more than **10⁸ raw Turing
  machine steps** — the same horizon the empirical pipeline previously
  needed a hundred-million-step replay to observe.
- Twenty thousand events are raw-step-equivalent to roughly **10^7046**
  steps — a number with over seven thousand digits. Boundary-only checking
  is not an optimization; it is a different regime of observation.
- Over those 20,000 certified events, Antihydra's heads counter climbs from
  2 to 9,919 with a clean average drift of +0.5 per event — exactly the
  random-walk expectation that makes the community believe the conjecture —
  and the orbit **never comes within four units of death** after startup.

## The non-Euclidean hypothesis

Why "geometry"? The orbit values explode exponentially (the hydra value
multiplies by roughly 1.5 per event), so in ordinary Euclidean coordinates
every plot degenerates — the trajectory just races off to infinity. The
program's hypothesis is that the *right* coordinates are non-Euclidean:

- **Logarithmic charts** turn multiplicative growth into steady additive
  motion.
- **Projective simplex charts** normalize the triple onto a triangle where
  the death condition literally becomes a *face* of the simplex — "the
  orbit dies" becomes "the trajectory touches the boundary wall."
- **Hyperbolic upper-half-plane surrogates** treat scale as height, the
  classical home for systems with exponential orbits and rare boundary
  interactions (the same geometry that tames continued fractions).

The hope: in the right chart, each machine's incision events trace a
stable, machine-characteristic figure — and machines in the same
"delta-rule family" trace the *same* figure. The first empirical test
passed: across the nine-machine atlas cohort, three machines known to share
a transfer rule show nearly identical near-collapse profiles, and two
others pair up the same way.

The honesty box travels with the hypothesis: the choice of hyperbolic
coordinates is a modeling bet, not a theorem. No known invariant separates
Antihydra's orbit from its death set — if one existed, the Antihydra
conjecture would be solved. What geometry can realistically deliver, in
increasing ambition: certified acceleration (done, proven), an empirical
taxonomy of incision figures across the cryptid cohort (started), and — for
*some* machines — a provable safety margin that would upgrade a conditional
reduction into an unconditional non-halting proof. The first atlas run also
delivered an honest negative: in the raw simplex chart the trajectory
degenerates toward a vertex as one coordinate dominates, so log-scaled
charts are the necessary refinement before any invariant hunting.

## The architecture guarantee

The geometry lives in its own package that the certified packages never
import. However speculative the hyperbolic experiments get, the two-axiom
trust base of the reductions cannot be contaminated — the dependency arrow
points strictly one way.

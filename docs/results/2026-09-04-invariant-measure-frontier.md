# The invariant-measure frontier, synthesized

**Date:** 2026-09-04. Combines the drift experiment
(`2026-09-04-invariant-measure-drift.md`) and the ergodic experiment
(`2026-09-04-invariant-measure-ergodic.md`).

## The two questions, separated

**Almost-all-seeds theorem** (a real result, not the goal): the
renewal map R has natural density zero of dying seeds. The mechanism
is now complete and self-consistent, with every constant pinned:

- transience Lyapunov `V = 1/(a+b)`, drift `e^{-0.134}-1 = -0.125`
  (size grows multiplicatively, rate 0.134);
- per-renewal hazard `h(s) <= C/s`, exact-lattice asymptote
  `C ~ 1.74` (the T-step-onto-diagonal channel is 58% of deaths, the
  fuse 23%; the old "6" was the crude offset numerator);
- the offset process MIXES: block entropy 0.423 nats/symbol, order-2
  Markov, short-range memory only (the no-TT constraint gives a
  lag-1 anticorrelation that decays by lag 2), no long-range
  structure;
- tail sum converges, geometric factor `1/(1-e^{-0.134}) = 7.97`,
  residual hazard `< 1e-59` past renewal 1000; ensemble bound
  `P(ever fatal) <~ 48/size_0`.

What a theorem still needs: prove offset equidistribution and the
geometric drift as properties of an invariant measure, plus the
mixing rate. This is well-scoped and, given the measured mixing,
plausibly reachable through the modular-surface reformulation (R is
built from integer 2x2 matrix moves; the fatal near-tie is a cusp
excursion; geodesic flow on SL(2,Z)\H is exponentially mixing by
known theory). That dictionary is the recommended next probe.

## The specific-orbit result (the actual SafeMetaOrbit, the goal):
out of reach by measure methods, and now provably so for a structural
reason. The certified orbit (6,13) is GENERIC: it matches random large
seeds to three decimals on the stationary symbol law (T 0.38, C 0.38,
F 0.24), entropy rate 0.423, and growth 0.134. A measure argument
therefore grants only the typical survival probability and gives no
pointwise verdict for this one trajectory. Borel-Cantelli and
equidistribution both degenerate for a single deterministic orbit.
This is the Collatz-hard core, and it is why the unconditional goal
cannot be reached this way.

## Verdict

The invariant-measure program yields, at most, an almost-all theorem
(genuine, publishable, one equidistribution lemma from done). It does
not, and by the genericity of the orbit cannot, yield the
unconditional non-halting of any specific certified machine. The five
prior impossibility results (mod-384, ranking certificates,
invariant-decidability, periodicity, monotone divergence) and this
genericity finding together map the wall completely: conditional
reduction is the frontier, almost-all is the reachable theorem, and
the specific orbit is Collatz-hard.

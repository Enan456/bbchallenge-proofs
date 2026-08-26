# The quantum-inspired layer: what it is, honestly

**Date:** 2026-08-26 · **Figures:** `figures/fig5_poincare.png`,
`fig6_fisher_rao.png`, `fig7_amoeba.png`, `fig8_returnmap.png`
(all from real dossier-2 orbit data; generator
`figures/make_figs2.py`-adjacent script in the session scratchpad)

Yes — there is a genuine quantum-inspired thread in this program, and
it is worth stating precisely, because parts of it are real
mathematical lineage and parts of it are naming. This note separates
the two.

## 1. Where "quantum" actually enters the pipeline

**The toolkit lineage.** `qgkit` descends from the parent
*Quantum_Geometry* repository, and every Lean namespace in the program
is `QIG.*` (quantum information geometry). Three concrete practices
carried over:

1. **Reversible vector maps** (`qgkit/bb6/vcollatz`). The v-Collatz
   representation encodes Collatz-like steps as *reversible* maps on
   integer vectors — the circuit-model discipline that every operation
   be invertible. This is what makes backward orbit search
   (`reverse_step`, preimage computation — the classical analogue of
   uncomputation) available during cryptid hunting, and it is how the
   1,094-holdout classification sweep explored candidate dynamics.
   The package docstring says it plainly and we repeat it: *this is
   bookkeeping over exact integer arithmetic and makes no claim of
   quantum advantage or speedup.*
2. **Ensemble (batched) evolution.** Candidate states are evolved in
   batches (`batched_step`) — a classical stand-in for superposed
   exploration. Again: a programming discipline borrowed from quantum
   simulation, not a speedup claim.
3. **State-space geometry.** The habit of treating "the set of
   configurations" as a geometric state space with the *right* metric
   — rather than a list of tuples — is the quantum-information-geometry
   habit, and it is what produced the charts.

## 2. The charts' quantum ancestry is not a metaphor

- **The log chart *is* a dequantization.** Maslov–Litvinov idempotent
  mathematics — the source of our componentwise `log(1+x)` chart and of
  tropical geometry — arises literally as the ℏ→0 limit of quantum
  mechanics (the "dequantization" of the semiring of positive reals).
  When the orbit's affine regimes appear as straight tropical segments,
  we are looking at the classical limit of a quantum-style calculus.
- **The simplex chart is classical state space.** Normalizing
  `(a,b,c)/(a+b+c)` puts the orbit on the probability simplex — the
  space of classical states (diagonal density matrices). Its natural
  metric is Fisher–Rao, which is exactly the classical shadow of the
  quantum Fubini–Study/Bures geometry.
- **The amplitude octant makes this literal** (Fig. 6). Mapping
  probabilities to amplitudes, `p ↦ √p`, sends the simplex
  isometrically (Fisher–Rao → round metric) onto the positive octant of
  the 2-sphere: the orbit becomes a path of "pure states," and
  geodesic distance is statistical distinguishability. This is the
  standard quantum-information picture, applied to a Turing machine's
  certified shape dynamics.
- **The hyperbolic chart** (Fig. 5, now rendered properly on the
  Poincaré disk via the Cayley transform) treats scale as depth: each
  renewal generation is one arc deeper toward the boundary — the
  negative-curvature geometry of hierarchies.

## 3. The upgraded chart set

| figure | what it shows |
|---|---|
| `fig5_poincare.png` | The eternal orbit on the Poincaré disk: shape along the boundary direction, log-scale as hyperbolic depth; renewal generations are nested arcs. |
| `fig6_fisher_rao.png` | The amplitude octant: the orbit as a path on the Fisher–Rao sphere; the quantum-inspired √-embedding of the simplex chart. |
| `fig7_amoeba.png` | Amoeba views (pairwise log–log): the orbit's tropical tentacles; the conserved-γ spine is visible as the straight (b,c) ridge with renewal branches. |
| `fig8_returnmap.png` | The reduced system itself: the renewal return map γₖ₊₁ vs γₖ on symlog axes, with the provably fatal values marked. This is the object the open conjecture is about. |

## 4. Honest boundaries

- No quantum computation is performed anywhere in the pipeline, and no
  quantum advantage is claimed. "Quantum-inspired" here means: (i)
  reversibility and ensemble disciplines borrowed from quantum
  simulation practice, and (ii) state-space geometries (dequantization,
  Fisher–Rao, projective/hyperbolic) whose mathematical origin is
  quantum theory.
- As with the earlier charts: these are instruments of discovery and
  exposition. No Lean theorem depends on any figure or any metric.

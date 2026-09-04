# Frontier campaign: five parallel workstreams

**Date:** 2026-09-04. Turns the unexplored-gaps inventory into five
concurrent subagent fronts. Each front produces honestly-labeled
findings, commits nothing (parent verifies + pushes each as it lands),
never fabricates a proof or relabels a conditional closure as
unconditional, and reports any halt fail-closed.

## The five fronts

| # | front | gaps | kind | deliverable |
|---|---|---|---|---|
| 1 | **Coverage calibration** | A1 | execution + validation | true hit-rate of the generator on a random sample of the 686 untouched engine-ready holdouts, via the 20M-step mirror gate + corridor/probe/fuel checks; extrapolated closable count |
| 2 | **Conjecture-reduction graph** | C1, C2 | structural analysis | reduction/equivalence graph over the 115 Safe-orbit conjectures -> number of INDEPENDENT root conjectures; branching-constant census + branch-word->constant test |
| 3 | **Almost-all theorem scaffold** | B1 | analysis | transfer operator (Ruelle-Perron-Frobenius) for the 3-generator semigroup, numerical spectrum + gap, explicit-stationary-measure route; proof SKELETON + the exact remaining lemma (not a proof) |
| 4 | **Dark-matter alphabet search** | D1 | empirical | automated natural-alphabet re-encoding over a sample of the 793 unstructured machines; classify each as fixed-dim-in-alphabet / higher-rank / suspected-halting |
| 5 | **Non-Archimedean obstruction** | E1 | analysis | p-adic/Berkovich fatal-set obstruction search beyond mod 384 -- any non-Archimedean invariant excluding the fatal set? |
| 6 | **Antihydra even-c gap** | E3 | analysis | characterization of the even-c case between abstract death and raw halting; whether the odd-c lethality formula extends |

## Held for direct (non-autonomous) work
- **A2 split-door corridor lemma** — Lean lemma-building; done by hand to
  avoid sorry-laden or broken proofs.
- **E2 compression decider** — too speculative to hand an agent; revisit
  if Front 2 shows the cohort collapses.
- **C3 closure-pattern class proposition** — gated on a fifth instance;
  folds into Front 1's output.

## Integration discipline
Only Front 1 emits Lean; it validates via the python mirror (the real
fail-closed gate) and stages files WITHOUT touching the aggregator or
running the full `lake build`, so parallel work never races the `.lake`
cache. Parent integrates + builds Lean winners after, in a warm-cache
batch. Fronts 2-5 are python/analysis only.

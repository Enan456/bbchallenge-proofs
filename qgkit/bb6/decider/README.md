# The certificate-emitting decider

A decider in this program's style: the search is empirical and
carries zero trust; the output NONHALT is backed by a per-machine
Lean certificate, so the trust surface is the Lean kernel and two
axioms, never this code.

## Pipeline

1. **Learn** (untrusted): derive the machine's macro law by the
   program's existing instruments (OrbitFinder specs; the one-sided,
   dip-aware, and bidirectional segmenters; the Dvisetu conditional
   extractor). Fail-closed: no law, verdict UNKNOWN.
2. **Search** (untrusted): find a closed invariant over the law's
   affine branch system that excludes the fatal set: congruence
   classes (`invariants.congruence_search`) or monotone linear
   functionals (`invariants.monotone_search`). Verified symbolically
   in exact rational arithmetic; stressed against raw simulation.
   None found, verdict UNKNOWN.
3. **Emit** (the only trusted artifact): a Lean certificate draft in
   the Dossier2RawTM generator style: raw semantics, halt
   localization, episode obligations, the invariant, and the closure
   theorem `invariant -> not RawHalts blankStart`. Obligations are
   compiled by the episode generators per machine; the verdict is
   NONHALT only when the kernel accepts the completed file.

## Verdicts

- `NONHALT(certificate)`: kernel-checked, unconditional.
- `CONDITIONAL(conjecture)`: reduction complete, invariant absent
  (the dossier outcome; not a decision).
- `UNKNOWN(stage, reason)`: fail-closed at the named stage.

## Honest scope

An invariant over a *learned* law decides nothing until the law's
episode obligations are kernel-checked; stage 3 is where empiricism
exits the chain. This package emits drafts and manifests; the
existing generators (busy-beaver-core/generators/) close them.

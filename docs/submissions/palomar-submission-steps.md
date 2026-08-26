# Palomar submission — ready to fire (browser step is yours)

Everything is prepared, validated (local intake: 0 failures / 0
warnings across all five entries), built, and pushed. The registry's
submission is browser-only with GitHub authentication, so the final
step must be done by you (I never enter your credentials).

**Go to:** https://submit.palomar-registry.org/

Per entry, fill:
- **Repository**: `Enan456/bbchallenge-proofs`
- **Commit** (full SHA, pinned): `d500444bf7fd99cee6e3644999a86006a63f6899`
- **Project directory**: `packages/dossier1`
- **Comparator configuration** (one submission per entry):
  1. `packages/dossier1/comparator-antihydra.json`
  2. `packages/dossier1/comparator-dossier1.json`
  3. `packages/dossier1/comparator-incision.json`
  4. `packages/dossier1/comparator-dossier2cryptid.json`  <- new
  5. `packages/dossier1/comparator-dossier3cryptid.json`  <- new
- **Relationship**: "I am a responsible author or maintainer"
- Authenticate with GitHub when prompted (token used once, not stored;
  session remembered 12h — so all five entries fit one sitting).

After Palomar's automated verification, the findings stay private until
you review them and choose to complete registration; on completion the
submission becomes permanently public.

Notes:
- LICENSE (MIT) is now in the repo root — the previous blocker.
- The two new entries' claims are explicitly marked `conditional` in
  their formalization.yaml; nothing overclaims decidedness.

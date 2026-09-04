# Palomar submission — ready to fire (browser step is yours)

Everything is prepared, validated (local intake: 0 failures / 0
warnings across all NINETEEN entries), built, and pushed. The registry's
submission is browser-only with GitHub authentication, so the final
step must be done by you (I never enter your credentials).

**Go to:** https://submit.palomar-registry.org/

Per entry, fill:
- **Repository**: `Enan456/bbchallenge-proofs`
- **Commit** (full SHA, pinned): `f8c07a3a1f8de73c66033e2daea1d1fa43e4e3ab`
- **Project directory**: `packages/dossier1`
- **Comparator configuration** (one submission per entry, 19 total):
  1. `packages/dossier1/comparator-antihydra.json`
  2. `packages/dossier1/comparator-dossier1.json`
  3. `packages/dossier1/comparator-incision.json`
  4. `packages/dossier1/comparator-dossier2cryptid.json`
  5. `packages/dossier1/comparator-dossier3cryptid.json`
  6. `packages/dossier1/comparator-dvisetu.json`
  7. `packages/dossier1/comparator-rank1.json`
  8-19. `packages/dossier1/comparator-dossier7.json` through
        `comparator-dossier18.json` (one per closure)
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

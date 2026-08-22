# Palomar registry validation of the three results (2026-08-22)

**What Palomar is.**  [Palomar](https://palomar-registry.org/) is a registry
of Lean-verified mathematics announced by Terence Tao on 2026-08-18
(incubated by the Lean FRO and ICARM).  A submission is a public GitHub
repo + commit with a small, auditable `Challenge` module (statements, core
Lean/Mathlib imports only, sorried proofs), a `Solution` module re-declaring
the same names with real proofs, a `comparator.json` selecting the compared
declarations, and a `formalization.yaml` metadata record.  The
[Comparator](https://github.com/leanprover/comparator) tool mechanically
checks that Solution proves exactly the Challenge statements using only
permitted axioms (`propext`, `Quot.sound`, `Classical.choice`), with kernel
+ NanoDa replay; an AI editorial review then checks statement/description
alignment.  Registration is a separate, explicit post-review step.

**What was built.**  All three headline results are packaged as Palomar
entries in `packages/bbchallenge` (one entry = one comparator config, per
policy):

| entry | compared theorems | challenge | axioms |
|---|---|---|---|
| `comparator-antihydra.json` | `AntihydraChallenge.antihydra_nonhalting` | 120 lines, core-only, self-contained TM semantics + 1-D hydra process | `[propext, Quot.sound]` |
| `comparator-incision.json` | `IncisionChallenge.astep_dies_iff`, `IncisionChallenge.boundary_checking_complete` | 79 lines, pure arithmetic orbit | `[propext, Quot.sound]` |
| `comparator-dossier1.json` | `Dossier1Challenge.dossier1_nonhalting` | 153 lines, TM semantics + chain-orbit | `[propext, Quot.sound]` |

Each Challenge is fully self-contained (zero imports — machine table, tape
semantics, and abstract systems defined inline with docstrings, well under
the 300-line audit-comfort threshold).  Each Solution re-declares the
challenge verbatim and proves it by a **transport development**
(`Palomar/*Solution.lean`): componentwise isomorphisms onto the certified
development's types, step/orbit commutation lemmas by finite case analysis
and structural induction, then the main theorems of `lean/` and
`packages/bbchallenge/Bridge/` pulled across.  Metadata lives per entry in
`palomar-meta/{antihydra,incision,dossier1}/formalization.yaml` (the three
entries have different provenance classes: Antihydra is *source-based* —
it formalizes the wiki's hydra analysis; incision and dossier-1 are
*original* first presentations — and Palomar's rules forbid mixing those in
one metadata record).

**Validation performed locally** (`scripts/check_palomar.py` +
`scripts/check_lean.sh` + pytest, all on the newly pinned **stable
`leanprover/lean4:v4.30.0`** — moved off the rc since Palomar requires a
named release no older than v4.28.0):

- all six Palomar modules compile; Solutions elaborate with zero sorries;
- `#print axioms` for all four compared theorems: exactly
  `[propext, Quot.sound]` — strictly inside the declared
  `permitted_axioms`;
- comparator configs: required keys only, valid axiom sets;
- challenge/solution structural match: every challenge declaration chunk
  appears verbatim, in order, in its solution; every compared theorem is
  sorried in the challenge and non-sorry in the solution;
- three `formalization.yaml` files pass the mechanical field checks
  including the provenance-alternative rule;
- toolchain/lakefile/manifest requirements met (path-dependency layout is
  explicitly supported by policy §6.1/§6.4);
- whole-repo gate re-verified on v4.30.0: `lean/` + both packages build,
  axiom gate OK, 10/10 parity+geometry tests pass.

**What local validation is *not*.**  The authoritative statement comparison
is Comparator's kernel/NanoDa replay, which runs server-side on submission
(its sandbox stack — landrun/systemd — is Linux-only, so it was not run on
this macOS machine).  The structural validator mirrors the intake contract;
it is a pre-flight, not the verdict.

**Blockers before actual submission** (submission itself uploads the repo
for review and is gated on owner sign-off; nothing was submitted):

1. **Root `LICENSE` file missing** — the one failing check.  Owner must
   choose an SPDX licence; the metadata proposes MIT.
2. **Push the packaged repo to its public GitHub remote**
   (`Enan456/bbchallenge-proofs`) — Palomar verifies write access via a tag
   at the submitted commit plus a gist (agent flow documented at
   `submit.palomar-registry.org/llms.txt`; submission → private review →
   explicit `register` or `withdraw`).
3. **Registry due diligence** (plan 2, task 4): re-check the live
   bbchallenge registry for superseding verdicts on both machines first —
   Palomar's own policy bars famous-open-problem submissions without an
   honest account, which our metadata provides, but community-status checks
   remain on us.
4. The editorial research-interest test is a judgment call Palomar's
   reviewer makes; the conditional-reduction framing (hypothesis stated
   prominently, honest strengthening delta documented) is written to meet
   its honesty requirements.

**Verdict: all three entries are mechanically submission-ready** — one
licence file and a `git push` away, pending owner sign-off.

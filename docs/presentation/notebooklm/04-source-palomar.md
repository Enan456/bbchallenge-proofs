# Registry Day: Validating Three Results for Tao's Palomar

*NotebookLM source document 4 of 4 — the Palomar registry story.
Self-contained.*

## A registry appears

On August 18, 2026, Fields Medalist Terence Tao announced **Palomar**, a
registry of Lean-verified mathematics, incubated by the Lean FRO and ICARM.
Palomar answers a growing problem: AI systems and human formalizers are
producing machine-checked proofs faster than journals can absorb, and the
world needs a place where a *claim* — the exact formal statement, the exact
commit, the exact axioms — is recorded and mechanically re-verified, without
pretending to be peer review.

Palomar's design is adversarial by construction. A submission is a public
GitHub repository at one fixed commit containing a **Challenge** module —
the small, human-auditable statement file, allowed to import only Lean's
core and a short list of verified libraries, with the proofs deliberately
left as holes — and a **Solution** module that re-declares the same
theorems and actually proves them. A tool called Comparator, with Lean's
kernel plus an independent second kernel (NanoDa), mechanically confirms
that the Solution proves *exactly* the Challenge statements using only
three permitted axioms. An AI editorial review then checks that the
informal description honestly matches the formal statement. Registration
is a separate, explicit, immutable step after the submitter sees the
review. Four days after the announcement, this project put all three of
its headline results through that pipeline's full local validation.

## Three entries

Palomar's rule is one entry per comparison configuration, so the three
results became three entries:

1. **Antihydra** — a 120-line, zero-import Challenge that defines the
   machine's complete semantics *and* the 1-D hydra process from scratch,
   and states: if the hydra process never dies, Antihydra never halts.
2. **Incision** — a 79-line pure-arithmetic Challenge stating the explicit
   death set and the boundary-only-checking equivalence.
3. **Dossier-1** — a 153-line Challenge with the second machine's semantics
   and its chain-stack orbit, stating its conditional non-halting.

Each Challenge had to be self-contained — a reader must be able to audit
the exact claim without opening the big development. That forced an
interesting piece of engineering: the Solutions cannot just cite the
existing theorems, because the Challenge defines its own copies of every
type. Each Solution therefore contains a **transport development**:
componentwise isomorphisms between the challenge's types and the certified
development's types, commutation lemmas proved by finite case analysis and
structural induction, and finally the main theorems pulled across the
bridge. About two hundred lines of glue per entry, all machine-checked.

## Validation results

A local validator re-implements Palomar's mechanical intake contract:
configuration shape, challenge size limits (all three are comfortably
under the 300-line audit-comfort threshold), the zero-import rule,
verbatim challenge-solution declaration matching, metadata schema, and the
provenance rules — which turned out to have teeth. Palomar forbids mixing
"original result" and "formalizes an existing source" claims in one
metadata record, and the three entries genuinely differ: the Antihydra
entry *formalizes* the community's published hydra analysis, while the
incision theorem and the dossier-1 reduction are first presentations. They
got three separate, honestly classified metadata files.

Along the way the whole repository moved from a release-candidate Lean
toolchain to the stable release, since Palomar requires a named release —
and everything was re-verified on it: every package builds, the axiom gate
passes, all differential tests pass, and all four compared theorems report
exactly the two axioms `propext` and `Quot.sound`, strictly inside
Palomar's permitted set of three.

Final score: every mechanical check passes except one — the repository has
no license file yet, a choice only the owner can make. After that, the
submission is a git push and a web form away. Nothing was actually
submitted: Palomar's submission uploads the repository for review, and
that outward-facing step is gated on the owner's explicit sign-off — the
same discipline the project applies to all publication.

## The eligibility question

Palomar is explicit that mechanical correctness is not enough: a result
must plausibly interest a research audience, and purported progress on
famous open problems must come with an honest account of exactly what is
and is not claimed. The entries are written to meet that bar precisely
*because* they claim less than they could: no machine is decided; the
Antihydra entry's abstract states in its first paragraph that the
hypothesis is a slightly strengthened form of the open conjecture and
names the exact strengthening. In a registry designed to resist
overclaiming, the honest-scope discipline the project practiced all along
turns out to be the entry ticket.

# The BB(6) Program: Hunting the Hardest Small Turing Machines

*NotebookLM source document 1 of 4 — the program overview. Self-contained.*

## The game

The Busy Beaver problem asks a deceptively simple question: among all Turing
machines with n states, which one runs longest before halting, when started
on a blank tape? The answer function BB(n) grows faster than any computable
function — it is the mathematical edge of what can be known by computation.
BB(5) was settled in July 2024 by the bbchallenge community: 47,176,870
steps, machine-verified in the Rocq (formerly Coq) proof assistant. BB(6) is
the current frontier, and it is a different beast entirely: it is known that
BB(6) exceeds numbers that cannot be written in this universe, and a
community-maintained list of about 1,158 "holdout" machines resist every
known automated decision technique.

The hardest holdouts are nicknamed "cryptids" — machines whose halting
behavior seems to encode genuinely deep arithmetic. The most famous cryptid
is **Antihydra**, a six-state machine whose fate is equivalent to a
Collatz-like conjecture that nobody knows how to prove.

## What this project did

This project attacked the BB(6) open set in five connected stages.

**Stage one: classification.** Every one of the 1,094-machine holdout set
(later the full official 1,158 open set) was run through a
"Collatz-lens" classifier that watches the machine's *records* — the moments
it touches fresh tape — and fits the structure of what it sees. The result
was a taxonomy: about 92 percent show growing-dimension record structure, 51
machines show compact "cryptid-shaped" growth, and exactly two machines in
the entire open set admit an exact one-dimensional generalized-Collatz
projection. The sweep was run with zero errors and full honesty labeling:
nothing in it decides any machine; it only measures structure.

**Stage two: exact emulation.** For the most structured machines, the
project fits an *exact macro system*: a small set of arithmetic rules of the
form "from a record of this shape, exactly this many raw steps lead to a
record of that shape." These rule systems are required to replay the raw
machine perfectly — 100 percent match, in and out of sample, over one
hundred million steps, fail-closed. Two machines got the full treatment:
Antihydra, and an unnamed holdout the project calls dossier-1. For both,
every rule was discharged by mechanical obligations (13 of 13 for Antihydra,
33 of 33 for dossier-1).

**Stage three: machine-checked proof.** Emulation evidence is not proof. The
project built, in the Lean 4 proof assistant using only its minimal core (no
external math library, axioms limited to two standard ones), a complete
formal reduction for both machines: *if* a single arithmetic conjecture
about the machine's abstract orbit holds, *then* the machine never halts.
Every dynamical fact about the machines — where they can halt, how every
rule acts for every block size, the startup, the tape grammar — is proven.
The one unproven ingredient is exactly the famous conjecture. For Antihydra,
a further bridge theorem shows the hypothesis is (a slightly strengthened
form of) the community's own Antihydra conjecture about iterating
b → b + ⌊b/2⌋.

**Stage four: incision geometry.** A new theorem shows that everything
dangerous in these orbits happens at rare "incision" events on an explicit
boundary set, and that checking *only* at those boundaries is provably
sound and complete. Measured against the raw machine, the first sixteen
incision events already cover more than one hundred million raw steps —
a certified, exponential acceleration. An empirical atlas plots these
incision events in non-Euclidean coordinate systems across the cryptid
cohort, looking for machine-characteristic geometric figures.

**Stage five: registry validation.** In August 2026, Terence Tao announced
Palomar, a registry of Lean-verified mathematics. All three headline
results — the Antihydra reduction, the incision theorem, and the dossier-1
reduction — were packaged into Palomar's Challenge/Solution format and
validated against its full mechanical intake contract. They pass every
check except a repository license file awaiting an owner decision.

## The honesty discipline

A recurring theme of the project is fail-closed honesty. An earlier
generation of the pipeline once produced unsound "bouncer" certificates,
which were falsified and permanently demoted; a later gate accepted nine
machines as exact-macro passes, of which two were refuted and one weakly
validated when the gate was tightened — the defensible count is six solid
plus one weak, and the correction is documented, not buried. Empirical
claims are always labeled as bounded observations; only the Lean theorems
are called proofs, and their axioms are checked mechanically on every
build. Nothing anywhere in the project decides any open machine — the
deliverable is the *reduction* of a machine's fate to a clean, isolated
piece of arithmetic, plus the tools to hunt that arithmetic efficiently.

## Why it matters

Busy Beaver research is a stress test for the boundary between computation
and mathematics. Each cryptid that gets formally reduced to a named
conjecture converts an inscrutable machine into a precise mathematical
target — and each certified acceleration (like boundary-only checking)
multiplies the reach of every future search. The project's three-layer
architecture — a tiny auditable trust base, machine-scale certified
dynamics, and a speculative geometric frontier that can never contaminate
the first two — is offered as a template for formal work on the rest of
the open set.

# DeepMath 2026 — OpenReview form fields

**Title**
Orbital Dragons to Hunt Cryptids: Utilizing Non-Euclidean Geometry to Solve Busy Beaver

**Authors**
Enan Srivastava (OpenReview profile required before submitting)

**Keywords**
busy beaver, BB(6), formal verification, Lean 4, Turing machines, Collatz-like systems, certified emulation, non-Euclidean embeddings, dynamical systems, AI-assisted theorem proving

**TL;DR**
Two open BB(6) "cryptid" Turing machines are compressed, machine-checked end-to-end in core Lean 4, into five-integer arithmetic conjectures via geometric orbit analysis and compiler-generated proofs.

**Abstract**
The fifth Busy Beaver number was settled in 2024; the sixth is guarded by "cryptid" Turing machines whose halting problems resist every known decider. We present a certified pipeline that hunts these cryptids geometrically: raw tape dynamics are compressed into orbit events, embedded in non-Euclidean (logarithmic, simplex, hyperbolic) charts where their self-similar structure becomes affine, and re-certified in core Lean 4 (axioms $\{\mathrm{propext}, \mathrm{Quot.sound}\}$ only). Headline result: two previously open BB(6) machines are reduced, machine-checked end to end, to conditional theorems $\mathsf{SafeMetaOrbit} \rightarrow \lnot\mathsf{RawHalts}$, where the conjecture concerns a deterministic affine map on five integers. Every raw step either machine ever takes — startup, one degenerate episode, and an eternity of seven certified episode types — is accounted for by theorems; the remaining conjecture is a subtractive Euclid/Collatz hybrid whose excluded parameter bands are provably lethal, so avoiding them is exactly the halting question. Proofs were compiled by generator–verifier loops: fail-closed empirical calculi validated against $10^9$ raw steps, then emitted as Lean and re-checked by the kernel. Conjectures hold to $10^8$ abstract episodes ($\approx 10^{15}$ raw steps).

**Email Sharing**: check "We authorize the sharing of all author emails with Program Chairs."
**Data Release**: check "We authorize the release of our submission and author names to the public in the event of acceptance."
**License**: suggest CC BY 4.0 (permits the public repo + Palomar packaging to coexist).
**PDF**: upload `deepmath2026.pdf`.

Note: the abstract makes only conditional claims ("Solve" in the title is aspirational —
if the chairs prefer, an alternate title is "Orbital Dragons to Hunt Cryptids:
Non-Euclidean Geometry and Certified Emulation at the Busy Beaver Frontier").

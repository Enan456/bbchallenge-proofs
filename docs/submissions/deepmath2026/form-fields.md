# DeepMath 2026 — OpenReview form fields

**Title**
Orbital Dragons to Hunt Cryptids: Utilizing Non-Euclidean Geometry to Solve Busy Beaver

**Authors**
Enan Srivastava (OpenReview profile required before submitting)

**Keywords**
busy beaver, BB(6), formal verification, Lean 4, Turing machines, Collatz-like systems, certified emulation, non-Euclidean embeddings, dynamical systems, AI-assisted theorem proving

**TL;DR**
We recast Busy Beaver halting as an event-history problem, and reduce two open BB(6) machines --- machine-checked end to end in core Lean 4 --- to five-integer arithmetic conjectures whose excluded configurations are provably lethal.

**Abstract**
Whether the sixth Busy Beaver value can be determined turns on a residual set of "cryptid" Turing machines whose halting problems have resisted every decider brought to bear on them. We reconceptualize the halting question for this class as an event-history problem: the machine's evolution is a long-duration process punctuated by recurrent events, and halting is a terminal event whose hazard concentrates in identifiable regions of a low-dimensional state space. Exploiting this structure, we develop a certified pipeline in which raw tape dynamics are aggregated into orbit events, embedded in non-Euclidean (logarithmic, simplex, hyperbolic) coordinate systems where the dynamics become affine, and re-derived as machine-checked theorems in core Lean 4 under the axiom set $\{\mathrm{propext}, \mathrm{Quot.sound}\}$. Our central result reduces two previously open BB(6) machines, end to end, to conditional theorems $\mathsf{SafeMetaOrbit} \rightarrow \lnot\mathsf{RawHalts}$, in which the antecedent concerns only a deterministic affine map on five integers. We validate each layer by differential testing against $10^9$ raw machine steps and show that the excluded parameter configurations are lethal: entering them provably produces the halting transition. The remaining conjecture is therefore not an artifact of the method but the halting problem itself, compressed to arithmetic on five integers; it survives $10^8$ abstract episodes ($\approx 10^{15}$ raw steps).

**Email Sharing**: check "We authorize the sharing of all author emails with Program Chairs."
**Data Release**: check "We authorize the release of our submission and author names to the public in the event of acceptance."
**License**: suggest CC BY 4.0 (permits the public repo + Palomar packaging to coexist).
**PDF**: upload `deepmath2026.pdf`.

Note: the abstract makes only conditional claims ("Solve" in the title is aspirational —
if the chairs prefer, an alternate title is "Orbital Dragons to Hunt Cryptids:
Non-Euclidean Geometry and Certified Emulation at the Busy Beaver Frontier").

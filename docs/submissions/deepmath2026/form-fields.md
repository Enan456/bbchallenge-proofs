# DeepMath 2026 — OpenReview form fields

**Title**
Orbital Dragons to Hunt Cryptids: Utilizing Non-Euclidean Geometry to Solve Busy Beaver

**Authors**
Enan Srivastava (OpenReview profile required before submitting)

**Keywords**
busy beaver, BB(6), formal verification, Lean 4, Turing machines, Collatz-like systems, certified emulation, non-Euclidean embeddings, dynamical systems, AI-assisted theorem proving

**TL;DR**
Two of the Turing machines blocking BB(6) run hidden Collatz-style arithmetic; we find their law empirically in non-Euclidean coordinates, prove it exactly in Lean, and reduce each machine's halting problem to a five-integer recurrence avoiding a provably fatal set.

**Abstract**
The busy beaver value $BB(n)$ is the longest finite runtime of any $n$-state Turing machine started on a blank tape. $BB(5)$ was settled in 2024 with a computer-checked proof. $BB(6)$ is blocked by a handful of machines whose tapes secretly run Collatz-style arithmetic; nobody can prove whether they stop. We study two of these machines. Our approach is empirical first: we log the machine's behavior as a sequence of events, embed the event data in logarithmic, simplex, and hyperbolic coordinates, and find that the dynamics are piecewise affine in a five-integer state. We then prove this description correct in the Lean proof assistant, down to the machine's individual steps and with a minimal axiom footprint ($\{\mathrm{propext}, \mathrm{Quot.sound}\}$). The result is a machine-checked theorem: if a simple five-integer recurrence never enters an explicit finite set of bad configurations, the machine never halts. We also prove the converse pressure: entering a bad configuration forces the machine to halt. The open problem is thereby moved, without loss, from a Turing machine to a short arithmetic recurrence. Every empirical claim is validated against $10^9$ raw machine steps, and the recurrence is tested for $10^8$ iterations.

**Email Sharing**: check "We authorize the sharing of all author emails with Program Chairs."
**Data Release**: check "We authorize the release of our submission and author names to the public in the event of acceptance."
**License**: suggest CC BY 4.0 (permits the public repo + Palomar packaging to coexist).
**PDF**: upload `deepmath2026.pdf`.

Note: the abstract makes only conditional claims ("Solve" in the title is aspirational —
if the chairs prefer, an alternate title is "Orbital Dragons to Hunt Cryptids:
Non-Euclidean Geometry and Certified Emulation at the Busy Beaver Frontier").

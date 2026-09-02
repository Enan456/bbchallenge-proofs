# DRAFT for discuss.bbchallenge.org — post only after your review

Suggested category: "Proofs" (or "Cryptids"). Suggested title:

**Lean-certified conditional closures for two BB(6) cryptids (a mirror
pair): halting reduced to an explicit five-integer recurrence**

---

This is a reduction result, not a decider, and it decides zero
machines. Posting per the validation-process convention (publication,
then invited reproduction and proof validation); objections and
reproductions welcome.

**The machines.** A mirror pair of six-state holdouts:

```
M1 = 1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD
M2 = 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE
```

**The theorem** (one per machine, checked by the Lean 4 kernel, axiom
footprint {propext, Quot.sound}, no sorry, no mathlib: the files
import Lean core only):

```
theorem dossier2_nonhalting : SafeMetaOrbit -> not RawHalts blankStart
```

where the abstract orbit is a five-integer state (block endpoints
l, r, hole positions h1, h2, and a tag) evolved by an explicit
function metaStep, and SafeMetaOrbit says the iteration never enters
an explicit finite set of bad configurations. The certified account
is complete: startup is checked step by step (235 steps for M1, 2,044
for M2), seven episode theorems with exact step counts cover every
behavior, and a transport theorem shows metaStep predicts the machine
forever. The reduction is also sharp: configurations just outside the
guarded region halt within about fifty raw steps, so the conjecture
is equivalent to non-halting, not merely sufficient.

**What remains open** is arithmetic. Sampling at renewals gives a
closed-form two-counter map (with (alpha, beta) = (6, a-1) or
(9, a-2) by parity of a):

```
R(a,b) = (a+6, b-3)                      b even
       = (alpha + 3(b-3), beta - (b-3))  b odd, b < beta
       = (alpha + 3*beta + 3, b-beta-4)  b odd, b > beta
```

with fatal set b - beta in {1, 3, 5} plus two boundary cases. The
orbit avoids the fatal window for 10^8 iterations (about 10^15 raw
steps) with minimum margin 4. Computational evidence closes two
mechanical routes: no congruence invariant up to modulus 384 excludes
the window, and the branch dynamics has factor complexity ~1.6^n, so
it is not conjugate to a rotation. Measured over the whole seed
space, the dying set has natural density zero at rate ~12/X.

**Reproduce it.**

```
git clone https://github.com/Enan456/bbchallenge-proofs
cd bbchallenge-proofs && git checkout 453158180bb55ad2e9588483801a64946a0ae734
cd busy-beaver-core && lake build       # kernel-checks everything
# then: #print axioms in the Dossier2RawTM / Dossier3RawTM namespaces
```

The self-contained challenge/solution pairs (Lean-core-only imports,
theorem statements sorried in the challenge and proven in the
solution) are under `packages/dossier1/Palomar/`, with comparator
configurations for automated checking. Differential validation of
every episode theorem against raw simulation is in
`tests/bb6/test_dossier23_theorems.py`.

The same repository carries an equivalent conditional closure for
Antihydra (`safeOrbitA_nonhalting`) and one further machine, plus a
structural census of all 1,094 holdouts; happy to detail any of it in
the thread if there is interest.

**Explicit non-claims:** no machine is decided; the conjectures are
open; empirical horizons are exactly the ones stated. What is on
offer for validation is the kernel-checked reduction and the
sharpness result, and what is invited is independent reproduction of
the Lean build and criticism of the conjecture framing.

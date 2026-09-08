# Aperiodicity / coboundary of the offset cocycle — does Method A go through?

**Date:** 2026-09-08 · **Script:** `qgkit/bb6/aperiodicity.py`
(deterministic; numpy only; fixed integer seeds, no randomness).
Reproduce: `python3 qgkit/bb6/aperiodicity.py`.

## What this decides

Method A closes the density form with a **parametrised transfer operator
`L_{s,t}`** for the Gauss-type induced map `G` of the renewal map `R`. Its
success hinges on one property of the **offset cocycle**

```
o = b - beta      (recorded at successive F-crossings; beta = a-1 if a odd, a-2 if a even)
```

being **APERIODIC mod every small `M`**: for every nontrivial character `t`
the twisted leading eigenvalue `lambda(t)` must have modulus `< 1`, i.e. the
character `e(t·o/M)` is **not a coboundary**

```
o  ≡  phi(G x) − phi(x) + c   (mod M).
```

A character with `|lambda(t)| = 1` is a coboundary — **DEGENERATE** — and
Method A needs a twist there.

This is a **measurement + exact-arithmetic** report (labelled per claim). It
is **not** a decision about any machine; it bears only on whether Method A's
transfer-operator argument can run.

## Method (two objects, two rigor levels)

**Ensemble.** 200 deterministic seeds `(6+4k, 13+8k)`, run to `RENEWAL_CAP`
or `bitlen(a) > 800`; **1,040,000 F-crossings** total (5,200/orbit).

- **(2) Offset-residue Markov chain — MEASUREMENT.** State = `o mod M` at
  F-crossings; empirical transition `P` from the real orbits. Report whether
  the chain is irreducible and aperiodic (period 1), its `|lambda_2|`
  (mixing), and the **character-twisted leading eigenvalue**
  `|lambda(t)| = rho(D_t P)`, `D_t = diag(e(2πi·t·r/M))`.
  `|lambda(t)| < 1` strictly for `t ≠ 0` ⟺ aperiodic at `M`.
- **(3) Coboundary cycle-test — EXACT / PROOF.** State = residue pair
  `(a mod M, b mod M)`; `o(x) = (b−beta) mod M` is a function of the source
  residue. Every return of a real orbit to a residue state gives a cycle
  `(L, S) = (#crossings, sum of offsets) mod M`. Character `t` is a
  **coboundary iff a single constant `c` solves `t·S ≡ c·L (mod M)` for every
  observed cycle**. A pair of cycles with no common `c` is a **witness** that
  `t` is non-coboundary — a rigorous aperiodicity certificate for the *real*
  dynamics (real cycles are a subset of any abstraction, so a real conflict is
  a genuine conflict). ~90k–210k cycles per modulus (5,618 at `M=384`, where
  residue-state returns are rarer).

The two objects **agree exactly**: the numeric degenerate set
`{t : |lambda(t)| = 1}` equals the exact coboundary set from the cycle-test at
every `M`.

## Per-modulus result

| M | #adm res | irreducible | aperiodic | \|λ₂\| | genuine max\|λ(t)\| | margin 1−\|λ\| | coboundary chars |
|---|---|---|---|---|---|---|---|
| 2 | 1 | yes | yes | 0.0000 | — | (1.0000) | {0, **1**} |
| 3 | 3 | yes | yes | 0.2054 | 0.4182 | 0.5818 | {0} |
| 4 | 2 | yes | yes | 0.1684 | 0.4103 | 0.5897 | {0, **2**} |
| 5 | 5 | yes | yes | 0.0165 | 0.0648 | 0.9352 | {0} |
| 6 | 3 | yes | yes | 0.2054 | 0.4182 | 0.5818 | {0, **3**} |
| 7 | 7 | yes | yes | 0.0482 | 0.1756 | 0.8244 | {0} |
| 8 | 4 | yes | yes | 0.1683 | 0.4103 | 0.5897 | {0, **4**} |
| 9 | 9 | yes | yes | 0.3835 | 0.4796 | 0.5204 | {0} |
| 12 | 6 | yes | yes | 0.2054 | 0.4182 | 0.5818 | {0, **6**} |
| 16 | 8 | yes | yes | 0.1683 | 0.4103 | 0.5897 | {0, **8**} |
| 24 | 12 | yes | yes | 0.2054 | 0.4182 | 0.5818 | {0, **12**} |
| 48 | 24 | yes | yes | 0.2052 | 0.4182 | 0.5818 | {0, **24**} |
| 384 | 192 | yes | yes | 0.2055 | 0.4180 | 0.5820 | {0, **192**} |

`#adm res` = admissible offset residues: **odd** residues for even `M`
(`M/2` of them), **all** residues for odd `M`. The offset marginal is uniform
over the admissible set to `< 0.3%` at every `M` (e.g. `mod 384`: each of 192
classes ≈ 0.0052 = 1/192). The bolded coboundary character at even `M` is
exactly `t = M/2`.

## Findings

1. **The only degeneracy is the trivial mod-2 parity.** At every tested `M`
   the coboundary (degenerate) characters are **precisely `{0}` and, for even
   `M`, `t = M/2`** — confirmed *identically* by the numeric twist
   (`|lambda(M/2)| = 1`) and by the exact cycle-test (`MATCH` at all 13
   moduli). The character `t = M/2` is the **parity character**: `o` is always
   odd (`beta` even, `b` odd), so `e(o·(M/2)/M) = (−1)^o = −1` is constant.
   This is a genuine coboundary — `o ≡ 1 (mod 2)`, with `phi = 0, c = 1` — but
   a **trivial and expected** one: it is just the statement that the offset is
   odd.

2. **Every genuine (non-constant) character is strictly contracting.** For
   all `t` not in `{0, M/2}`, `|lambda(t)| < 1` with a comfortable margin. The
   worst case over all moduli is `|lambda(t)| = 0.4796` at `M = 9`
   (margin `0.5204`); most genuine characters sit near `0.41` or below, and
   the mod-5/7 cases are far smaller (`0.065`, `0.176`). No genuine character
   comes near the unit circle.

3. **Rigorous non-coboundary witnesses.** For the smallest genuine character
   `t = 1` at each even `M ≥ 8` the script exhibits an explicit incompatible
   cycle pair, e.g.

   - `M = 8`: cycle A `(L=7, S=5)` and cycle B `(L=2, S=0)` admit no common `c`.
   - `M = 16`: A `(L=4, S=0)`, B `(L=1, S=9)`.
   - `M = 24`: A `(L=2, S=16)`, B `(L=1, S=9)`.
   - `M = 48`: A `(L=1, S=9)`, B `(L=14, S=24)`.

   These are exact modular certificates: no `phi, c` can make `o` a coboundary
   for that character on the real dynamics.

4. **The chain mixes.** As a Markov chain the offset residue is irreducible
   and aperiodic (single unit eigenvalue) at every `M`, with
   `|lambda_2| ≤ 0.384`. The subleading modulus is essentially `M`-independent
   for moduli divisible by 3 (`≈ 0.205`, the mod-3 relaxation) and much
   smaller for `M ∈ {5, 7}` — consistent with the known mod-3 conservation law
   being the slowest residue mode and everything else equidistributing fast.

## Verdict

**The aperiodicity Method A needs HOLDS at every tested modulus**
`M ∈ {2,3,4,5,6,7,8,9,12,16,24,48,384}`, with a single, harmless caveat:

- Aperiodicity **fails only** for the trivial parity character `t = M/2`
  (even `M`), because `o` is identically odd. This is not an obstruction — it
  is the mod-2 structure of the offset. Method A must work on the **odd
  sublattice** (equivalently, drop the `t = M/2` character / twist by the
  fixed parity `o ≡ 1 mod 2`), which is standard.
- Restricted to that sublattice — i.e. for **every genuine character** —
  the twisted leading eigenvalue has modulus `< 1` **strictly**, with
  worst-case aperiodicity margin `1 − |lambda(t)| = 0.5204` (at `M = 9`).
- The numeric spectral conclusion and the exact modular cycle-test agree at
  all 13 moduli, and the good direction (non-coboundary) is backed by explicit
  cycle-pair witnesses that are rigorous for the real orbit.

There is **no non-trivial coboundary degeneracy** and **no periodic sublattice
trapping** of the offset residue at any modulus up to 384. Method A's
transfer-operator argument is not blocked by an aperiodicity failure; it needs
only the routine quotient by the offset's fixed parity.

## Honest scope

- Objects (2) and the marginals are **measurements** over the finite ensemble
  (200 seeds, ~10⁶ crossings, `bitlen ≤ 800`): the transition matrices and
  eigenvalues are estimated, not proved. The equidistribution and gap values
  are empirical.
- Object (3), the coboundary status, is **exact modular arithmetic** on the
  observed real cycles. Its two conclusions have different strengths: a
  *non-coboundary* verdict (aperiodic) is a genuine proof for the real
  dynamics via the witness pair; a *coboundary* verdict (only `t ∈ {0, M/2}`
  here) is established on the observed cycle set, which at `M ≤ 48` is large
  (≥ 140k cycles) and, being the trivial parity, is also proved directly from
  `o ≡ 1 (mod 2)`.
- The `M = 384` cycle-test rests on only 5,618 residue-state returns; its
  `MATCH` is corroborated by the robust numeric twist over the full 1.04M
  crossings.
- These results concern the **offset cocycle's aperiodicity only** — the
  hypothesis Method A consumes. They do not by themselves establish the
  transfer operator's Lasota–Yorke / spectral-gap bounds, nor decide the
  underlying SafeMetaOrbit conjecture.

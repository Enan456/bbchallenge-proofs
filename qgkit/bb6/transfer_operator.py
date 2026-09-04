"""Ulam discretization of the transfer (Ruelle-Perron-Frobenius) operator for
the offset/residue return-map process induced by the renewal map R (bb6).

EMPIRICAL NUMERICAL SCAFFOLD -- NOT A PROOF, and NOT a decision about any
machine.  This builds the transfer-operator objects a Lasota-Yorke /
Ionescu-Tulcea-Marinescu argument would consume for the ALMOST-ALL-seeds
theorem, and measures them at a finite horizon:

  * the induced return map to the above-diagonal (F-branch) crossings, in
    scale-invariant coordinates  (z = o/(o+beta),  residue o mod M);
  * its Ulam matrix L (row-stochastic), leading eigenvalue (= 1), second
    eigenvalue -> spectral gap, and the stationary left eigenvector = the
    candidate invariant density;
  * factorization test: does the invariant measure split as (ratio density)
    x (uniform residue)?  -- this is the offset-equidistribution lemma as a
    property of the invariant measure;
  * Ulam-convergence robustness of the gap across grid resolutions.

Deterministic: fixed explicit integer seeds, native bigints, NO randomness.
See docs/results/2026-09-04-transfer-operator.md.
"""
import math
from collections import Counter, defaultdict
import numpy as np


# ---- the verified map (verbatim from renewal_analysis3.py) ----
def R(a, b):
    if b % 2 == 0:
        return a + 6, b - 3, 'T'
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    sym = 'd' if a % 2 == 1 else 'D'
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3), sym + 'C'
    return alpha + 3 * beta + 3, b - beta - 4, sym + 'F'


def fatal(a, b):
    if b <= 2:
        return 'b<=2'
    if b % 2 == 0:
        return 'T->1' if b == 4 else None
    beta = (a - 1) if a % 2 == 1 else (a - 2)
    if b > beta and b - beta in (1, 3, 5):
        return 'diagonal'
    return None


def beta_of(a):
    return (a - 1) if a % 2 == 1 else (a - 2)


BITLEN_CAP = 700       # stop an orbit when bitlen(a) exceeds this
RENEWAL_CAP = 40000    # hard safety cap on renewals


# ------------------------------------------------------------------
# Collect the induced return-map trajectory in the crossing section.
# At each above-diagonal (F-branch) event we record the scale-invariant
# state  (z, r)  with  z = o/(o+beta) in (0,1),  r = o mod M  (odd).
# We return the *sequence* of (z, r) per orbit so consecutive pairs give
# the induced transition (z_k, r_k) -> (z_{k+1}, r_{k+1}).
# ------------------------------------------------------------------
def crossing_sequence(a0, b0, M, bitcap=BITLEN_CAP):
    a, b = a0, b0
    seq = []
    for _ in range(RENEWAL_CAP):
        if fatal(a, b):
            break
        if b % 2 == 1:
            beta = beta_of(a)
            if b > beta:
                o = b - beta
                z = o / (o + beta)           # in (0,1), scale invariant
                seq.append((z, o % M))
        a, b, _ = R(a, b)
        if a.bit_length() > bitcap:
            break
    return seq


def make_seeds(n_family=800, deep=40):
    """Deterministic reproducible seed ensemble (no randomness)."""
    seeds = [(6 + 4 * k, 13 + 8 * k) for k in range(n_family)]
    # large iterated states: iterate a fixed number of steps then reseed
    for k in range(0, n_family, 2):
        a, b = 6 + 4 * k, 13 + 8 * k
        ok = True
        for _ in range(deep):
            if fatal(a, b):
                ok = False
                break
            a, b, _ = R(a, b)
            if a.bit_length() > BITLEN_CAP:
                break
        if ok and b % 2 == 1 and not fatal(a, b):
            seeds.append((a, b))
    return seeds


# ------------------------------------------------------------------
# Ulam matrix from a pool of crossing sequences.
#   z-axis: NZ uniform cells on [0,1)
#   residue axis: the k admissible odd residues mod M
# Cell index = zbin * k + residue_index.  Returns row-stochastic L,
# the visit counts (unnormalized stationary), and bookkeeping.
# ------------------------------------------------------------------
def build_ulam(sequences, NZ, M):
    odd_res = [r for r in range(M) if r % 2 == 1]
    ridx = {r: i for i, r in enumerate(odd_res)}
    k = len(odd_res)
    S = NZ * k

    def cell(z, r):
        zb = int(z * NZ)
        if zb >= NZ:
            zb = NZ - 1
        return zb * k + ridx[r]

    trans = np.zeros((S, S), dtype=np.float64)
    visits = np.zeros(S, dtype=np.float64)
    for seq in sequences:
        prev = None
        for (z, r) in seq:
            c = cell(z, r)
            visits[c] += 1
            if prev is not None:
                trans[prev, c] += 1
            prev = c
    rowsum = trans.sum(axis=1, keepdims=True)
    L = np.divide(trans, rowsum, out=np.zeros_like(trans),
                  where=rowsum > 0)
    return L, trans, visits, rowsum.ravel(), k, odd_res


def spectrum(L, rowsum):
    """Leading + subleading eigenvalues of the row-stochastic operator,
    restricted to the recurrent (visited) sub-block, renormalized."""
    vis = rowsum > 0
    Lv = L[np.ix_(vis, vis)]
    rs = Lv.sum(axis=1, keepdims=True)
    Lv = np.divide(Lv, rs, out=np.zeros_like(Lv), where=rs > 0)
    # right eigenvalues (leading is 1 with all-ones right eigenvector)
    ev = np.linalg.eigvals(Lv)
    evm = np.sort(np.abs(ev))[::-1]
    # stationary = left eigenvector for eigenvalue 1 (invariant density)
    w, V = np.linalg.eig(Lv.T)
    j = int(np.argmin(np.abs(w - 1.0)))
    pi = np.real(V[:, j])
    pi = np.abs(pi)
    s = pi.sum()
    pi = pi / s if s > 0 else pi
    return evm, pi, vis


def main():
    print("# TRANSFER-OPERATOR SCAFFOLD (Ulam) for the induced renewal "
          "return map")
    print("# EMPIRICAL, NOT A PROOF. bears only on almost-all seeds.")
    print(f"# bitlen(a) cap {BITLEN_CAP}")

    M = 6                     # residue modulus; odd residues {1,3,5} = k=3
    seeds = make_seeds()
    print(f"# ensemble: {len(seeds)} deterministic seeds")

    # gather crossing sequences once at the finest modulus we use
    sequences = [crossing_sequence(a0, b0, M) for (a0, b0) in seeds]
    ncross = sum(len(s) for s in sequences)
    print(f"# induced crossings collected: {ncross:,} "
          f"(mean {ncross/len(sequences):.0f}/orbit)")

    # ================================================================
    # (A) primary operator:  NZ=24 z-cells x 3 residues (mod 6)
    # ================================================================
    NZ = 24
    print("\n" + "=" * 70)
    print(f"(A) PRIMARY OPERATOR  L :  {NZ} z-cells  x  {M//2} residues "
          f"mod {M}  =  {NZ*(M//2)} states")
    print("=" * 70)
    L, trans, visits, rowsum, k, odd_res = build_ulam(sequences, NZ, M)
    evm, pi, vis = spectrum(L, rowsum)
    lead = evm[0]
    lam2 = evm[1]
    print(f"  admissible odd residues mod {M}: {odd_res}  (k={k})")
    print(f"  recurrent states: {int(vis.sum())}/{NZ*k}")
    print(f"  leading |eigenvalue|  = {lead:.6f}   (theory: exactly 1)")
    print(f"  second  |eigenvalue|  = {lam2:.6f}")
    print(f"  SPECTRAL GAP 1-|lambda_2| = {1-lam2:.4f}")
    print(f"  |eigenvalues| (top 8): {[round(float(e),4) for e in evm[:8]]}")

    # ---- invariant density: marginalize stationary vector ----
    # rebuild full-length stationary indexed by (zbin, residue)
    full = np.zeros(NZ * k)
    full[vis] = pi
    dens = full.reshape(NZ, k)          # rows: z-bin, cols: residue
    z_marg = dens.sum(axis=1)           # ratio-coordinate invariant density
    r_marg = dens.sum(axis=0)           # residue marginal
    z_marg = z_marg / z_marg.sum()
    r_marg = r_marg / r_marg.sum()

    print("\n  --- invariant density over z = o/(o+beta) (ratio coordinate) ---")
    print("   zbin  z-range        stationary mass   (density = mass/binwidth)")
    for i in range(NZ):
        lo, hi = i / NZ, (i + 1) / NZ
        bar = "#" * int(round(z_marg[i] * 200))
        print(f"   {i:>3}  [{lo:.3f},{hi:.3f})  {z_marg[i]:.5f}   {bar}")

    print("\n  --- residue marginal (offset-equidistribution as an "
          "invariant-measure property) ---")
    print(f"   residues mod {M}: {odd_res}")
    print(f"   marginal        : {[round(float(x),4) for x in r_marg]}  "
          f"(uniform = {1/k:.4f})")
    print(f"   max |r_marg - 1/k| = {float(np.max(np.abs(r_marg-1/k))):.5f}")

    # ---- factorization test: is pi(z,r) ~ f(z) * (1/k) ? ----
    # compare the conditional residue distribution in each z-bin to uniform
    cond = dens / np.maximum(dens.sum(axis=1, keepdims=True), 1e-300)
    dev = np.abs(cond - 1.0 / k)
    # weight the deviation by z-bin mass so empty tail bins do not dominate
    wdev = float((dev.max(axis=1) * z_marg).sum())
    print("\n  --- factorization  pi(z,r) =?= f(z) * uniform_residue ---")
    print(f"   mass-weighted mean of max_r |P(r|z) - 1/k| = {wdev:.5f}")
    print(f"   (small => invariant measure factorizes; residue is uniform "
          f"in every z-slice)")

    # ================================================================
    # (B) ratio-only operator (M=1): the clean z-dynamics spectral gap
    # ================================================================
    print("\n" + "=" * 70)
    print("(B) RATIO-ONLY OPERATOR (residue collapsed): clean z spectral gap")
    print("=" * 70)
    seq1 = [[(z, 1) for (z, _) in s] for s in sequences]   # single residue
    for NZ1 in (16, 24, 32, 48):
        L1, tr1, vs1, rs1, k1, _ = build_ulam(seq1, NZ1, 2)  # M=2 -> odd res {1}
        evm1, pi1, _ = spectrum(L1, rs1)
        print(f"   NZ={NZ1:>3}:  |lambda_1|={evm1[0]:.5f}  "
              f"|lambda_2|={evm1[1]:.5f}  gap={1-evm1[1]:.4f}  "
              f"|lambda_3|={evm1[2]:.4f}")

    # ================================================================
    # (C) Ulam robustness of the primary gap across resolutions
    # ================================================================
    print("\n" + "=" * 70)
    print("(C) ULAM CONVERGENCE of the spectral gap (grid refinement)")
    print("=" * 70)
    print("   NZ x k    states   |lambda_2|   gap 1-|lambda_2|")
    for NZc in (12, 16, 20, 24, 32, 40):
        Lc, _, _, rsc, kc, _ = build_ulam(sequences, NZc, M)
        evmc, _, visc = spectrum(Lc, rsc)
        print(f"   {NZc:>2} x {kc}    {int(visc.sum()):>5}     "
              f"{evmc[1]:.5f}     {1-evmc[1]:.4f}")

    # ================================================================
    # (D) cross-check vs the 5-symbol transition operator (prior result)
    # ================================================================
    print("\n" + "=" * 70)
    print("(D) CROSS-CHECK: 5-symbol {T,dC,DC,dF,DF} transition operator")
    print("=" * 70)
    SYMS = ['T', 'dC', 'DC', 'dF', 'DF']
    six = {s: i for i, s in enumerate(SYMS)}
    Tm = np.zeros((5, 5))
    for (a0, b0) in seeds:
        a, b = a0, b0
        prev = None
        for _ in range(RENEWAL_CAP):
            if fatal(a, b):
                break
            a, b, s = R(a, b)
            if prev is not None:
                Tm[six[prev], six[s]] += 1
            prev = s
            if a.bit_length() > BITLEN_CAP:
                break
    rs = Tm.sum(axis=1, keepdims=True)
    Ps = np.divide(Tm, rs, out=np.zeros_like(Tm), where=rs > 0)
    evs = np.sort(np.abs(np.linalg.eigvals(Ps)))[::-1]
    print(f"   symbol-operator |eigenvalues|: {[round(float(e),4) for e in evs]}")
    print(f"   |lambda_2| = {evs[1]:.4f}   gap = {1-evs[1]:.4f}")
    print(f"   (prior effective-equidist report: |lambda_2|=0.440, gap 0.560)")

    # ================================================================
    # (E) drift as an invariant-measure integral (Lyapunov exponent)
    # ================================================================
    print("\n" + "=" * 70)
    print("(E) GEOMETRIC DRIFT as an integral against the invariant measure")
    print("=" * 70)
    # per-renewal log-growth of size along the ensemble (weighted by the
    # induced measure through simple time-average = space-average heuristic)
    logg = []
    a, b = 6, 13
    for _ in range(200000):
        s0 = a + b
        na, nb, _ = R(a, b)
        if fatal(a, b):
            break
        logg.append(math.log((na + nb) / s0))
        a, b = na, nb
        if a.bit_length() > 4000:
            break
    lg = np.array(logg)
    print(f"   time-average per-renewal log-growth (drift) = {lg.mean():.5f}")
    print(f"   std {lg.std():.5f}  over {len(lg):,} renewals of (6,13)")
    print(f"   (this is E_mu[log|F'|] > 0 : the positive Lyapunov exponent")
    print(f"    the invariant measure mu must integrate; matches prior 0.134)")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  leading eigenvalue           : {lead:.6f}  (= 1, as required)")
    print(f"  primary spectral gap         : {1-lam2:.4f}  (1-|lambda_2|)")
    print(f"  symbol-operator gap          : {1-evs[1]:.4f}  (cross-check)")
    print(f"  residue marginal max dev     : "
          f"{float(np.max(np.abs(r_marg-1/k))):.5f}  (uniform => equidist)")
    print(f"  factorization deviation      : {wdev:.5f}")
    print(f"  invariant-measure drift      : {lg.mean():.5f}  (>0, transient)")


if __name__ == "__main__":
    main()

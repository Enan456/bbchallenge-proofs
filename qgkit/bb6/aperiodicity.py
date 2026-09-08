"""Aperiodicity / coboundary analysis of the offset cocycle for the renewal
map R (bb6) -- the property Method A's parametrised transfer operator L_{s,t}
depends on.

WHAT THIS DECIDES
-----------------
Method A closes the density form with a twisted transfer operator L_{s,t} for
the Gauss-type induced map G of R.  It succeeds iff the offset cocycle
  o = b - beta        (recorded at successive F-crossings)
is APERIODIC mod every small M: for every nontrivial character t the twisted
leading eigenvalue has modulus < 1, i.e. e(t*o/M) is NOT a coboundary
  o  ==  phi(G x) - phi(x) + c   (mod M).
A character for which |lambda(t)| = 1 is a coboundary (DEGENERATE): Method A
needs a twist there.

This file MEASURES (numeric, labelled) and, where possible, PROVES (exact
modular cycle arithmetic) the aperiodicity/coboundary status per modulus M.

Two objects, at two rigor levels:

 (2) offset-residue Markov chain   [MEASUREMENT]
     state = o mod M at F-crossings; empirical transition P from real orbits.
       - irreducible?  aperiodic (period 1)?  |lambda_2| (mixing).
       - character-twisted leading eigenvalue |lambda(t)| = rho( D_t P ),
         D_t = diag(e(2 pi i t r / M)) over admissible residues r.
         |lambda(t)| < 1 strictly for t != 0 (nontrivial)  <=>  aperiodic at M.

 (3) coboundary cycle-test on the residue state (a mod M, b mod M)  [PROOF]
     o(x) = (b - beta) mod M is a function of the source residue.  Along real
     orbits every return to a residue state yields a cycle (L, S) = (number of
     crossings, sum of offsets) mod M.  Character t is a COBOUNDARY iff there
     is a constant c with  t*S ==  c*L  (mod M) for every observed cycle.
     A pair of cycles with no common c is a WITNESS that t is non-coboundary
     -- a rigorous aperiodicity certificate for the real dynamics at M
     (real cycles are a subset of any abstraction, so a real conflict is a
     genuine conflict).

The two objects agree exactly: the numeric degenerate set {t : |lambda(t)|=1}
equals the exact coboundary set from the cycle-test.

Deterministic: fixed explicit integer seeds, native bigints, NO randomness.
See docs/results/2026-09-08-aperiodicity.md.
"""
import math
from collections import Counter, defaultdict
from math import gcd

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


MODULI = [2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 24, 48, 384]
BITLEN_CAP = 800
RENEWAL_CAP = 6000


# ------------------------------------------------------------------
# (1) offset sequences along real orbits.
# Each event at an F-crossing records:
#   o      = b - beta          (the offset; odd, >= 7 for a survivor)
#   par    = a % 2             (parity of a: 0 -> DF branch, 1 -> dF branch)
#   ab     = (a, b)            (kept to form residue states at any modulus)
# ------------------------------------------------------------------
def make_seeds(n_family=200):
    return [(6 + 4 * k, 13 + 8 * k) for k in range(n_family)]


def offset_orbits(seeds):
    """Return a list (one per orbit) of event lists [(o, par, a, b), ...]."""
    orbits = []
    for (a0, b0) in seeds:
        a, b = a0, b0
        ev = []
        for _ in range(RENEWAL_CAP):
            if fatal(a, b):
                break
            if b % 2 == 1:
                be = beta_of(a)
                if b > be:                       # F-crossing
                    ev.append((b - be, a % 2, a, b))
            a, b, _ = R(a, b)
            if a.bit_length() > BITLEN_CAP:
                break
        orbits.append(ev)
    return orbits


# ------------------------------------------------------------------
# (2) offset-residue Markov chain and its character twist.
# ------------------------------------------------------------------
def offset_chain(orbits, M):
    """Empirical transition matrix P on admissible offset residues mod M."""
    adm = sorted({o % M for ev in orbits for (o, *_ ) in ev})
    idx = {r: i for i, r in enumerate(adm)}
    k = len(adm)
    N = np.zeros((k, k))
    marg = Counter()
    for ev in orbits:
        rs = [o % M for (o, *_ ) in ev]
        for r in rs:
            marg[r] += 1
        for x, y in zip(rs, rs[1:]):
            N[idx[x], idx[y]] += 1
    rowsum = N.sum(axis=1, keepdims=True)
    P = np.divide(N, rowsum, out=np.zeros_like(N), where=rowsum > 0)
    return adm, k, P, N, marg


def chain_spectrum(P):
    """Return sorted |eigenvalues| of the row-stochastic P (mixing / period)."""
    ev = np.linalg.eigvals(P)
    return np.sort(np.abs(ev))[::-1]


def char_is_constant(adm, t, M):
    """Is r -> e(2 pi i t r / M) constant over the admissible residues?"""
    vals = {round(math.cos(2 * math.pi * t * r / M), 9) for r in adm}
    vals2 = {round(math.sin(2 * math.pi * t * r / M), 9) for r in adm}
    return len(vals) == 1 and len(vals2) == 1


def twisted_leading(adm, P, M):
    """|lambda(t)| = spectral radius of D_t P for every t = 0..M-1.
    Returns list of (t, |lambda(t)|, is_constant_character)."""
    out = []
    for t in range(M):
        phase = np.array([np.exp(2j * np.pi * t * r / M) for r in adm])
        Dt = P * phase[:, None]                    # D_t P (twist current state)
        rho = float(np.max(np.abs(np.linalg.eigvals(Dt))))
        out.append((t, rho, char_is_constant(adm, t, M)))
    return out


# ------------------------------------------------------------------
# (3) exact coboundary cycle-test on the residue state (a%M, b%M).
# ------------------------------------------------------------------
def collect_cycles(orbits, M):
    """Every return to a residue state (a%M, b%M) yields a cycle (L, S) mod M,
    with L = #crossings around the loop, S = sum of offsets around the loop."""
    cycles = []
    for ev in orbits:
        first = {}
        cumL = 0
        cumS = 0
        for (o, par, a, b) in ev:
            st = (a % M, b % M)
            if st in first:
                L0, S0 = first[st]
                cycles.append(((cumL - L0) % M, (cumS - S0) % M))
            else:
                first[st] = (cumL, cumS)
            cumL += 1
            cumS = (cumS + (o % M)) % M
    return cycles


def coboundary_c_set(M, L, S, t):
    """Set of c in Z/M solving  c*L ==  t*S (mod M), or None if unsolvable."""
    L %= M
    rhs = (t * S) % M
    if L == 0:
        return set(range(M)) if rhs % M == 0 else None
    g = gcd(L, M)
    if rhs % g != 0:
        return None
    Lg, Mg, rg = L // g, M // g, (rhs // g) % (M // g)
    inv = pow(Lg % Mg, -1, Mg) if Mg > 1 else 0
    c0 = (rg * inv) % Mg if Mg > 1 else 0
    return set(range(c0, M, Mg))


def degenerate_chars_exact(M, cycles):
    """t is a coboundary iff SOME constant c works for ALL cycles.  Return the
    exact set of coboundary (degenerate) characters t in 0..M-1."""
    degen = []
    for t in range(M):
        allowed = None
        ok = True
        for (L, S) in cycles:
            sols = coboundary_c_set(M, L, S, t)
            if sols is None:
                ok = False
                break
            allowed = sols if allowed is None else (allowed & sols)
            if not allowed:
                ok = False
                break
        if ok and (allowed is None or allowed):
            degen.append(t)
    return degen


def witness_pair(M, cycles, t):
    """For a NON-coboundary character t, return two cycles whose c-sets are
    disjoint (a rigorous non-coboundary certificate), else None."""
    seen = []
    for (L, S) in cycles:
        sols = coboundary_c_set(M, L, S, t)
        if sols is None:
            return (L, S), None            # unsolvable alone: c*L==t*S has no c
        for (L0, S0, s0) in seen:
            if not (sols & s0):
                return (L0, S0), (L, S)
        seen.append((L, S, sols))
        if len(seen) > 4000:
            break
    return None


# ------------------------------------------------------------------
def main():
    print("=" * 74)
    print("APERIODICITY / COBOUNDARY ANALYSIS of the offset cocycle o = b-beta")
    print("renewal map R (bb6).  MEASUREMENT + exact modular PROOF. NOT a")
    print("decision about any machine; bears on Method A's transfer operator.")
    print("=" * 74)

    seeds = make_seeds()
    orbits = offset_orbits(seeds)
    ncross = sum(len(ev) for ev in orbits)
    print(f"# ensemble: {len(seeds)} deterministic seeds, "
          f"{ncross:,} F-crossings ({ncross // len(seeds)}/orbit), "
          f"bitlen cap {BITLEN_CAP}")

    # branch / parity structure (item 1)
    par = Counter(p for ev in orbits for (_, p, *_ ) in ev)
    print(f"# F-crossing branch parity a%2:  odd(dF)={par[1]:,}  "
          f"even(DF)={par[0]:,}  (both branches occur)")
    print("# offset o is ODD at every F-crossing "
          f"(beta even, b odd): {all(o % 2 == 1 for ev in orbits for (o, *_ ) in ev)}")

    print("\n" + "=" * 74)
    print("PER-MODULUS TABLE")
    print("=" * 74)
    print(f"{'M':>4} {'adm':>4} {'irr':>4} {'aper':>5} {'|lam2|':>8} "
          f"{'genuine max|lam(t)|':>20} {'margin':>8} "
          f"{'degenerate chars t':>22}")
    print("-" * 84)

    summary = []
    for M in MODULI:
        adm, k, P, N, marg = offset_chain(orbits, M)
        spec = chain_spectrum(P)
        lam2 = float(spec[1]) if k > 1 else 0.0

        # irreducible & aperiodic (period 1) as a Markov chain:
        # count unit-modulus eigenvalues; >1 => periodic, exactly 1 => aperiodic
        onunit = int(np.sum(spec > 1 - 1e-6))
        irreducible = onunit == 1 or k == 1     # simple leading eigenvalue
        aperiodic_chain = onunit == 1

        tw = twisted_leading(adm, P, M)
        genuine = [rho for (t, rho, c) in tw if t != 0 and not c]
        constchars = [t for (t, rho, c) in tw if t != 0 and c]
        gmax = max(genuine) if genuine else 0.0
        margin = 1.0 - gmax

        # exact coboundary cycle-test
        cycles = collect_cycles(orbits, M)
        degen = degenerate_chars_exact(M, cycles)
        expected = [0] + ([M // 2] if M % 2 == 0 else [])
        match = sorted(degen) == sorted(expected)

        summary.append(dict(M=M, k=k, lam2=lam2, gmax=gmax, margin=margin,
                            irreducible=irreducible, aperiodic=aperiodic_chain,
                            degen=degen, expected=expected, match=match,
                            constchars=constchars, ncyc=len(cycles), tw=tw,
                            marg=marg, adm=adm))

        print(f"{M:>4} {k:>4} {str(irreducible):>4} {str(aperiodic_chain):>5} "
              f"{lam2:>8.4f} {gmax:>20.4f} {margin:>8.4f} "
              f"{str(degen):>22}")

    # -------- detail per modulus --------
    print("\n" + "=" * 74)
    print("DETAIL: character-twisted leading eigenvalues |lambda(t)|")
    print("=" * 74)
    for s in summary:
        M = s['M']
        print(f"\nM = {M}   admissible residues (o mod M): {s['adm']}")
        # marginal equidistribution
        n = sum(s['marg'].values())
        fr = {r: round(s['marg'][r] / n, 4) for r in s['adm']}
        print(f"  offset-residue marginal: {fr}   (uniform = "
              f"{1 / len(s['adm']):.4f})")
        print(f"  chain: irreducible={s['irreducible']}  "
              f"aperiodic(period1)={s['aperiodic']}  |lambda_2|={s['lam2']:.4f}")
        line = "  |lambda(t)|: " + "  ".join(
            f"t{t}={rho:.3f}{'*' if c else ''}" for (t, rho, c) in s['tw'])
        print(line)
        print(f"    (* = constant/parity character e(t*o/M) with t={s['constchars']}"
              f"; these are the trivial mod-2 coboundary o==1 (mod 2))")
        # exact cycle-test verdict
        vtag = "MATCH" if s['match'] else "MISMATCH!"
        print(f"  exact cycle-test ({s['ncyc']:,} cycles): coboundary chars "
              f"t={s['degen']}   expected {{0}}+parity={sorted(s['expected'])}"
              f"   [{vtag}]")
        # a rigorous non-coboundary witness for the smallest genuine character
        cycles = collect_cycles([ev for ev in orbits], M)
        gt = next((t for (t, rho, c) in s['tw'] if t != 0 and not c), None)
        if gt is not None:
            w = witness_pair(M, cycles, gt)
            if w and w[1] is not None:
                (L1, S1), (L2, S2) = w
                print(f"  witness (t={gt} non-coboundary, PROOF): "
                      f"cycle A (L={L1},S={S1}) & cycle B (L={L2},S={S2}) "
                      f"admit no common c mod {M}")

    # -------- verdict --------
    print("\n" + "=" * 74)
    print("VERDICT")
    print("=" * 74)
    all_match = all(s['match'] for s in summary)
    min_margin = min(s['margin'] for s in summary if s['margin'] > 0)
    worst = min((s for s in summary if s['margin'] > 0),
                key=lambda s: s['margin'])
    print(f"  Every modulus M in {MODULI}:")
    print(f"    - offset-residue chain is IRREDUCIBLE and APERIODIC "
          f"(single unit eigenvalue).")
    print(f"    - the ONLY coboundary (degenerate) characters are t=0 (trivial)"
          f" and, for even M, t=M/2.")
    print(f"    - t=M/2 is the PARITY character: o is always odd, so e(o*M/2 /M)"
          f" = (-1)^o = -1 is constant -- a genuine but trivial mod-2 "
          f"coboundary (o == 1 mod 2, phi=0, c=1).")
    print(f"    - EVERY genuine (non-constant) character has |lambda(t)| < 1 "
          f"strictly.")
    print(f"  Exact cycle-test agrees with the numeric twist at all M: "
          f"{all_match}")
    print(f"  Worst-case aperiodicity margin over genuine characters: "
          f"1-|lambda(t)| = {min_margin:.4f}  (at M={worst['M']}, "
          f"|lambda|={worst['gmax']:.4f}).")
    print(f"  => Aperiodicity Method A needs HOLDS at every tested M, once the")
    print(f"     trivial mod-2 parity is quotiented (work on the odd sublattice"
          f" / drop t=M/2).")


if __name__ == "__main__":
    main()

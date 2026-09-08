"""Effective mixing / equidistribution rate of the offset over the induced
first-return map G of the renewal map R (bb6).

EMPIRICAL MEASUREMENT -- NOT A PROOF, and NOT a decision about any machine.
This quantifies, at a finite horizon, the four things the "Method B"
(effective-equidistribution) route would need as an INPUT:

  (1) the exact COCYCLE structure of the crossing offset  o_d = b_d - beta_d:
      is o_d a Birkhoff sum of a per-step function, or a projective/
      multiplicative observable whose *residue* o_d mod M is carried by a
      finite affine cocycle over G?  We verify the residue cocycle exactly.

  (2) the CORRELATION DECAY (Dolgopyat) rate of the induced map G for the
      scale-invariant offset observable z=o/(o+beta) and for the offset-
      residue characters e(t*o/M); fit C(n)=<f,\bar f o G^n>-|<f>|^2 vs lag
      and compare to the induced spectral gap |lambda_2|~0.21.

  (3) the EFFECTIVE EQUIDISTRIBUTION rate of o_d mod M -> uniform: the
      per-crossing relaxation rate of the residue marginal (|lambda_2| of the
      pooled residue transition operator P_M), the TV decay of P_M^d, and the
      translation exponential-in-d  =>  polynomial-in-N (natural density).

  (4) inputs for an honest assessment of the modular-surface framework
      (the linear parts have det +-3, i.e. GL(2,Z[1/3]), NOT SL(2,Z)).

Deterministic: fixed explicit integer seeds, native arbitrary-precision
ints, NO randomness.  See docs/results/2026-09-08-effective-mixing.md.
"""
import math
import cmath
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


# ------------------------------------------------------------------
# The affine cocycle:  every renewal move is  (a,b) -> Lin.(a,b) + shift
# with Lin in {I, Clin, Flin}.  Reducing this mod L is EXACT, so
# (a mod L, b mod L) evolves by an affine cocycle and  o mod M  (M | L)
# is a deterministic factor of the reduced state.  R_mod reproduces a
# single renewal step working ONLY on residues (a mod L, b mod L) plus the
# branch symbol chosen by the full (bigint) dynamics.
# ------------------------------------------------------------------
def step_symbol(a, b):
    """Which branch fires at (a,b) -- needs the true size comparison."""
    if b % 2 == 0:
        return 'T'
    beta = beta_of(a)
    return ('d' if a % 2 == 1 else 'D') + ('C' if b < beta else 'F')


def R_mod(ar, br, sym, L):
    """Apply the renewal move of type `sym` to residues (ar,br) mod L.
    `sym` in {'T','dC','DC','dF','DF'} is supplied by the true dynamics
    (the branch choice depends on a size comparison not visible mod L)."""
    if sym == 'T':
        return (ar + 6) % L, (br - 3) % L
    if sym == 'dC':   # a odd, C branch:  a'=3b-3,        b'=a-b+2
        return (3 * br - 3) % L, (ar - br + 2) % L
    if sym == 'DC':   # a even, C branch: a'=3b,          b'=a-b+1
        return (3 * br) % L, (ar - br + 1) % L
    if sym == 'dF':   # a odd, F branch:  a'=3a+6,        b'=b-a-3
        return (3 * ar + 6) % L, (br - ar - 3) % L
    if sym == 'DF':   # a even, F branch: a'=3a+6,        b'=b-a-2
        return (3 * ar + 6) % L, (br - ar - 2) % L
    raise ValueError(sym)


def o_mod_from_residue(ar, br, M):
    """o = b - beta,  beta = a-1 (a odd) / a-2 (a even).  a parity is
    ar mod 2 (valid because 2 | L).  Returns o mod M."""
    beta_r = (ar - 1) if ar % 2 == 1 else (ar - 2)
    return (br - beta_r) % M


# ------------------------------------------------------------------
# reproducible seed ensemble (same family convention as prior scripts)
# ------------------------------------------------------------------
def make_seeds(n_family, deep=40, bitcap=None):
    seeds = [(6 + 4 * k, 13 + 8 * k) for k in range(n_family)]
    for k in range(0, n_family, 2):
        a, b = 6 + 4 * k, 13 + 8 * k
        ok = True
        for _ in range(deep):
            if fatal(a, b):
                ok = False
                break
            a, b, _ = R(a, b)
            if bitcap and a.bit_length() > bitcap:
                break
        if ok and b % 2 == 1 and not fatal(a, b):
            seeds.append((a, b))
    return seeds


# ------------------------------------------------------------------
# Run one orbit; return the induced-crossing record:
#   per crossing d:  (o (bigint), beta, z=o/(o+beta), return-word since prev)
# plus, if verify_mod is set, the residue-cocycle prediction of o mod M.
# ------------------------------------------------------------------
def orbit_crossings(a0, b0, bitcap, renewal_cap, mods=(), L=None,
                    keep_o=False):
    a, b = a0, b0
    ar = br = None
    if L is not None:
        ar, br = a % L, b % L
    crossings = []           # list of dicts
    word = []                # branch symbols since previous crossing
    mismatches = 0
    for _ in range(renewal_cap):
        if fatal(a, b):
            break
        if b % 2 == 1:
            beta = beta_of(a)
            if b > beta:      # F-branch crossing
                o = b - beta
                z = o / (o + beta)
                rec = {'z': z, 'word': tuple(word)}
                for M in mods:
                    rec[M] = o % M
                if keep_o:
                    rec['logo'] = math.log(o)
                if L is not None:
                    rec['modok'] = all(o_mod_from_residue(ar, br, M) == o % M
                                       for M in mods)
                    if not rec['modok']:
                        mismatches += 1
                crossings.append(rec)
                word = []
        sym = step_symbol(a, b)
        word.append(sym)
        if L is not None:
            ar, br = R_mod(ar, br, sym, L)
        a, b, _ = R(a, b)
        if a.bit_length() > bitcap:
            break
    return crossings, mismatches


def admissible(M):
    """Residue support of o (o is always odd)."""
    if M % 2 == 0:
        return [r for r in range(M) if r % 2 == 1]
    return list(range(M))


def tv_from_uniform(counts, res):
    n = sum(counts.get(r, 0) for r in res)
    if n == 0:
        return None
    u = 1.0 / len(res)
    return 0.5 * sum(abs(counts.get(r, 0) / n - u) for r in res)


# ==================================================================
def main():
    print("# EFFECTIVE MIXING / EQUIDISTRIBUTION RATE  (induced return map G)")
    print("# EMPIRICAL, NOT A PROOF.  bears only on almost-all seeds.\n")

    MODS = [2, 3, 4, 5, 6, 8, 16, 384]
    L = 2 * 384 * 5             # 3840: divisible by every M and by 2 (parity)
    for M in MODS:
        assert L % M == 0
    BITCAP = 340
    RENEWAL_CAP = 20000
    N_FAMILY = 1500

    seeds = make_seeds(N_FAMILY, bitcap=BITCAP)
    print(f"# ensemble: {len(seeds)} deterministic seeds, "
          f"bitlen(a) cap {BITCAP}, cocycle modulus L={L}")

    # ---- collect all crossings ----
    all_orbits = []            # list of per-orbit crossing lists
    total_mismatch = 0
    total_cross = 0
    for (a0, b0) in seeds:
        cr, mm = orbit_crossings(a0, b0, BITCAP, RENEWAL_CAP,
                                 mods=MODS, L=L, keep_o=True)
        all_orbits.append(cr)
        total_mismatch += mm
        total_cross += len(cr)
    print(f"# induced crossings collected: {total_cross:,} "
          f"(mean {total_cross/len(seeds):.0f}/orbit)\n")

    # ==============================================================
    # (1) COCYCLE STRUCTURE
    # ==============================================================
    print("=" * 68)
    print("(1) COCYCLE STRUCTURE OF THE OFFSET o_d = b_d - beta_d")
    print("=" * 68)
    print(f"residue-cocycle check: o_d mod M predicted from (a,b) mod L")
    print(f"  via the affine cocycle, for M in {MODS}:")
    print(f"  crossings checked: {total_cross:,} x {len(MODS)} moduli;  "
          f"MISMATCHES: {total_mismatch}")
    print(f"  => o_d mod M is EXACTLY a factor of the affine cocycle on "
          f"(Z/L)^2 (0 mismatches).")

    # return-word (G symbolic) statistics
    wc = Counter()
    wlen = Counter()
    for cr in all_orbits:
        for rec in cr:
            wc[rec['word']] += 1
            wlen[len(rec['word'])] += 1
    tot_w = sum(wc.values())
    print("\n  induced return-word statistics (branch symbols between "
          "consecutive crossings):")
    print(f"    return-word length: "
          f"{{{', '.join(f'{k}:{wlen[k]/tot_w:.3f}' for k in sorted(wlen) if k<=8)}}}"
          f"  mean {sum(k*v for k,v in wlen.items())/tot_w:.2f}")
    top = wc.most_common(8)
    print("    most common return words (last symbol is the F-crossing):")
    for w, c in top:
        print(f"      {'.'.join(w):<20} {c/tot_w:.3f}")

    # offset is multiplicative, NOT additive: log o_d grows ~linearly
    logs = [rec['logo'] for cr in all_orbits for rec in cr]
    # per-orbit slope of log o vs crossing index
    slopes = []
    dlog_per_cross = []
    for cr in all_orbits:
        if len(cr) < 20:
            continue
        ys = [rec['logo'] for rec in cr]
        xs = list(range(len(ys)))
        n = len(ys)
        mx = sum(xs) / n
        my = sum(ys) / n
        num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        den = sum((x - mx) ** 2 for x in xs)
        if den > 0:
            slopes.append(num / den)
        for i in range(1, len(ys)):
            dlog_per_cross.append(ys[i] - ys[i - 1])
    slopes.sort()
    mean_dlog = sum(dlog_per_cross) / len(dlog_per_cross)
    print("\n  the INTEGER offset o_d is a projective/multiplicative "
          "observable, not a Birkhoff sum:")
    print(f"    log(o_d) grows ~linearly in d; per-orbit slope median "
          f"{slopes[len(slopes)//2]:.4f} (mean {sum(slopes)/len(slopes):.4f})")
    print(f"    mean increment  E[log o_{{d+1}} - log o_d] = {mean_dlog:.4f} "
          f"nats/crossing  (geometric growth => o_d NOT a bounded cocycle)")
    print(f"    ==> o_d itself carries no bounded per-step summand; only "
          f"o_d mod M (finite cocycle) and z=o/(o+beta) (projective) are "
          f"stationary observables of G.")

    # ==============================================================
    # (2) CORRELATION DECAY over G  (Dolgopyat rate)
    # ==============================================================
    print("\n" + "=" * 68)
    print("(2) CORRELATION DECAY over G  (fit C(n)/C(0) = |lambda|^n)")
    print("=" * 68)

    def autocorr(series_list, fvals, maxlag=10):
        """Normalized autocorrelation rho(n)=C(n)/C(0) pooled over orbits.
        fvals: function rec->complex.  Uses within-orbit lag-n pairs."""
        # global mean
        allf = [fvals(r) for cr in series_list for r in cr]
        mu = sum(allf) / len(allf)
        var = sum((abs(x - mu) ** 2) for x in allf) / len(allf)
        rho = []
        npairs = []
        for n in range(0, maxlag + 1):
            num = 0.0
            cnt = 0
            for cr in series_list:
                fv = [fvals(r) for r in cr]
                for i in range(len(fv) - n):
                    num += ((fv[i] - mu).conjugate() * (fv[i + n] - mu)).real
                    cnt += 1
            rho.append((num / cnt) / var if cnt and var > 0 else 0.0)
            npairs.append(cnt)
        return rho, npairs, var

    def fit_rate(rho, lo=1, hi=6):
        xs, ys = [], []
        for n in range(lo, hi + 1):
            if n < len(rho) and rho[n] > 0:
                xs.append(n)
                ys.append(math.log(rho[n]))
        if len(xs) < 2:
            return None, None, None
        n = len(xs)
        mx = sum(xs) / n
        my = sum(ys) / n
        num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
        den = sum((x - mx) ** 2 for x in xs)
        slope = num / den
        # R^2
        yhat = [my + slope * (x - mx) for x in xs]
        ss_res = sum((y - yh) ** 2 for y, yh in zip(ys, yhat))
        ss_tot = sum((y - my) ** 2 for y in ys)
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
        return math.exp(slope), -slope, r2   # |lambda|, rate, R^2

    observables = [
        ("z = o/(o+beta)", lambda r: complex(r['z'])),
        ("cos,sin 2pi o/6", lambda r: cmath.exp(2j * math.pi * r[6] / 6)),
        ("e(o/8)", lambda r: cmath.exp(2j * math.pi * r[8] / 8)),
        ("e(o/16)", lambda r: cmath.exp(2j * math.pi * r[16] / 16)),
        ("e(o/384)", lambda r: cmath.exp(2j * math.pi * r[384] / 384)),
        ("[o mod 6 == 1]", lambda r: complex(1.0 if r[6] == 1 else 0.0)),
    ]
    print(f"  induced spectral gap (prior transfer_operator.py): "
          f"|lambda_2|=0.21 (per return)  => rate -ln|l2| = {-math.log(0.21):.2f}")
    print("  noise floor per rho(n) ~ 1/sqrt(#pairs) "
          f"~ {1/math.sqrt(total_cross-total_cross//50):.4f}\n")
    print(f"  {'observable':<18} {'rho(1)':>8} {'rho(2)':>8} {'rho(3)':>8}"
          f" {'|lambda|fit':>11} {'rate':>7} {'R^2':>6}")
    for name, fv in observables:
        rho, npairs, var = autocorr(all_orbits, fv, maxlag=8)
        lam, rate, r2 = fit_rate(rho, 1, 5)
        r1 = rho[1] if len(rho) > 1 else 0
        r2v = rho[2] if len(rho) > 2 else 0
        r3v = rho[3] if len(rho) > 3 else 0
        lam_s = f"{lam:.3f}" if lam is not None else "  n/a"
        rate_s = f"{rate:.2f}" if rate is not None else " n/a"
        r2_s = f"{r2:.3f}" if r2 is not None else "  n/a"
        print(f"  {name:<18} {r1:>8.4f} {r2v:>8.4f} {r3v:>8.4f}"
              f" {lam_s:>11} {rate_s:>7} {r2_s:>6}")

    # ==============================================================
    # (3) EFFECTIVE EQUIDISTRIBUTION RATE of o_d mod M -> uniform
    # ==============================================================
    print("\n" + "=" * 68)
    print("(3) EFFECTIVE EQUIDISTRIBUTION RATE  o_d mod M -> uniform")
    print("=" * 68)
    print("  Per-crossing residue relaxation rate = |lambda_2| of the pooled")
    print("  residue transition operator P_M[r,s]=Pr(o_{d+1}=s | o_d=r).")
    print("  Exponential-in-d  =>  TV ~ |lambda_2|^d.  With size growing")
    print(f"  geometrically ( E[dlog size]={mean_dlog:.3f}/crossing ), a size N")
    print("  is reached in ~ln(N)/dlog crossings, so TV ~ N^(-alpha),")
    print("  alpha = -ln|lambda_2| / E[dlog size]  (poly-in-N; natural density).\n")

    print(f"  {'M':>4} {'k':>4} {'|l2(P)|':>9} {'rate':>7} {'alpha(N)':>9}"
          f" {'d@1e-3':>7} {'d@1e-6':>7} {'TVfloor':>8}")
    equidist_rows = []
    for M in MODS:
        res = admissible(M)
        k = len(res)
        ridx = {r: i for i, r in enumerate(res)}
        if k == 1:
            print(f"  {M:>4} {k:>4} {'--':>9} {'--':>7} {'--':>9}"
                  f" {'--':>7} {'--':>7}  (trivial: single residue)")
            continue
        # pooled residue transition matrix
        P = np.zeros((k, k))
        for cr in all_orbits:
            for i in range(len(cr) - 1):
                r0, r1 = cr[i][M], cr[i + 1][M]
                if r0 in ridx and r1 in ridx:
                    P[ridx[r0], ridx[r1]] += 1
        rs = P.sum(axis=1, keepdims=True)
        P = np.divide(P, rs, out=np.zeros_like(P), where=rs > 0)
        ev = np.sort(np.abs(np.linalg.eigvals(P)))[::-1]
        lam2 = ev[1] if len(ev) > 1 else 0.0
        rate = -math.log(lam2) if lam2 > 0 else float('inf')
        alpha = rate / mean_dlog if mean_dlog > 0 else 0.0
        # d to reach TV 1e-3, 1e-6 from a worst-case start (TV0=1-1/k)
        tv0 = 1 - 1.0 / k
        d3 = (math.log(1e-3) - math.log(tv0)) / math.log(lam2) if 0 < lam2 < 1 else 0
        d6 = (math.log(1e-6) - math.log(tv0)) / math.log(lam2) if 0 < lam2 < 1 else 0
        # empirical TV floor: TV of a truly-uniform multinomial of the
        # observed per-index sample size (estimate at a late index)
        floor = math.sqrt((k - 1) / (2 * math.pi)) / math.sqrt(max(1, len(seeds)))
        print(f"  {M:>4} {k:>4} {lam2:>9.4f} {rate:>7.3f} {alpha:>9.4f}"
              f" {d3:>7.1f} {d6:>7.1f} {floor:>8.4f}")
        equidist_rows.append((M, k, lam2, rate, alpha, P, res, ridx))

    # direct empirical TV(d): relaxation of P_M^d rows to uniform, and
    # the measured marginal TV at each crossing index (annealed).
    print("\n  DIRECT check (M=6): TV( P_6^d row , uniform ) vs d  "
          "[worst-case start]")
    for M, k, lam2, rate, alpha, P, res, ridx in equidist_rows:
        if M != 6:
            continue
        Pd = np.eye(k)
        u = np.ones(k) / k
        print("    d :  " + "  ".join(f"{d}" for d in range(0, 9)))
        tvs = []
        for d in range(0, 9):
            tv = 0.5 * np.abs(Pd - u).sum(axis=1).max()
            tvs.append(tv)
            Pd = Pd @ P
        print("   TV :  " + "  ".join(f"{t:.4f}" if t >= 1e-4 else f"{t:.0e}"
                                       for t in tvs))
        # fit
        xs = [d for d in range(1, 6)]
        ys = [math.log(tvs[d]) for d in xs if tvs[d] > 0]
        xs = xs[:len(ys)]
        if len(xs) >= 2:
            nn = len(xs)
            mx = sum(xs) / nn
            my = sum(ys) / nn
            sl = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / \
                sum((x - mx) ** 2 for x in xs)
            print(f"    fitted TV(d) ~ exp({sl:.3f} d) => rate {-sl:.3f}, "
                  f"|lambda| {math.exp(sl):.4f}  (matches |l2(P_6)|={lam2:.4f})")

    # annealed marginal TV at crossing index d, across the ensemble
    print("\n  ANNEALED marginal TV at crossing index d (across ensemble), "
          "M=6:")
    print("    (starts already near-uniform b/c seeds are varied; shown to "
          "expose the sampling floor)")
    maxd = 60
    idx_counts = [Counter() for _ in range(maxd)]
    for cr in all_orbits:
        for d in range(min(len(cr), maxd)):
            idx_counts[d][cr[d][6]] += 1
    res6 = admissible(6)
    print("    d :  " + "  ".join(f"{d:>6}" for d in (0, 1, 2, 5, 10, 20, 40)))
    row = []
    for d in (0, 1, 2, 5, 10, 20, 40):
        tv = tv_from_uniform(idx_counts[d], res6)
        row.append(f"{tv:.4f}" if tv is not None else "   n/a")
    print("   TV :  " + "  ".join(f"{x:>6}" for x in row))
    navg = sum(sum(idx_counts[d].values()) for d in range(maxd)) / maxd
    print(f"    (per-index sample ~{navg:.0f} orbits; uniform-sample TV floor "
          f"~{math.sqrt((len(res6)-1)/(2*math.pi))/math.sqrt(navg):.4f})")

    print("\n# done.")


if __name__ == "__main__":
    main()

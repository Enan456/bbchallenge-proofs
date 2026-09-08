"""Large-sieve / lattice-point route to natural density zero for the bb6
renewal map R.

EMPIRICAL MEASUREMENT + ANALYSIS -- NOT A PROOF.  Reproducible, deterministic
(exact enumeration + a fixed-seed PRNG for the large-N samples).  Companion
note: docs/results/2026-09-08-large-sieve-count.md.

What this does, following the four-part task:

 (1) Extracts the exact integer affine offset form  o_d(a,b) = p*a + q*b + r
     on each realized depth-d cylinder (d = number of diagonal/F crossings),
     by symbolic composition of the per-step affine maps, and reports the
     growth of |p|,|q| with depth.  Verified against the exact map.

 (2) Counts integer seeds (a,b) in the N-box on the fatal lines
     o_d in {1,3,5}, per cylinder, summed over cylinders and depths, and
     measures the scaling of #halting with N.

 (3) Assembles the exact quantities Montgomery's large sieve would need
     (sublattice indices Q_d = |det P| = 3^{#C+#F}, the N vs Q^2 comparison)
     and reports whether the sieve can beat the trivial main term.

 (4) Runs the elementary line-count: #points on a line <= length/step + 1;
     measures the sum of the "+1"s = number of (cylinder, fatal-line)
     incidences meeting the box, and whether THAT is o(N^2).
"""
import math
import random
from collections import defaultdict, Counter


# ---- verified map (verbatim from renewal_analysis3.py) ----
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


def symbol_of(a, b):
    if b % 2 == 0:
        return 'T'
    beta = (a - 1) if a % 2 == 1 else (a - 2)
    return ('d' if a % 2 == 1 else 'D') + ('C' if b < beta else 'F')


# ---- symbolic affine composition (state as forms in the seed) ----
# state: a_d = (pa,qa,ra).(a,b,1),  b_d = (pb,qb,rb).(a,b,1)
IDENT = ((1, 0, 0), (0, 1, 0))


def step_sym(A, s):
    (pa, qa, ra), (pb, qb, rb) = A
    if s == 'T':
        return ((pa, qa, ra + 6), (pb, qb, rb - 3))
    if s[0] == 'd':
        alpha, boff = 6, 1
    else:
        alpha, boff = 9, 2
    if s[1] == 'C':
        na = (3 * pb, 3 * qb, alpha + 3 * rb - 9)
        nb = (pa - pb, qa - qb, ra - boff - rb + 3)
    else:  # F
        na = (3 * pa, 3 * qa, alpha + 3 * ra - 3 * boff + 3)
        nb = (pb - pa, qb - qa, rb - ra + boff - 4)
    return (na, nb)


def offset_form(A, s):
    """offset o = b_d - beta at an F-event; beta = a_d - boff."""
    (pa, qa, ra), (pb, qb, rb) = A
    boff = 1 if s[0] == 'd' else 2
    return (pb - pa, qb - qa, rb - ra + boff)


def det_lin(A):
    (pa, qa, _), (pb, qb, _) = A
    return pa * qb - qa * pb


# =====================================================================
# (0) verification: symbolic form reproduces exact map + offsets
# =====================================================================
def verify():
    ok = True
    for (a0, b0) in [(6, 13), (10, 21), (7, 30), (9, 45), (14, 51),
                     (6, 101), (23, 200), (100, 401)]:
        A = IDENT
        a, b = a0, b0
        for _ in range(60):
            if fatal(a, b):
                break
            s = symbol_of(a, b)
            (pa, qa, ra), (pb, qb, rb) = A
            if (pa * a0 + qa * b0 + ra, pb * a0 + qb * b0 + rb) != (a, b):
                ok = False
            if s.endswith('F'):
                p, q, r = offset_form(A, s)
                beta = (a - 1) if a % 2 == 1 else (a - 2)
                if p * a0 + q * b0 + r != b - beta:
                    ok = False
            A = step_sym(A, s)
            a, b, _ = R(a, b)
    return ok


# =====================================================================
# run a seed to halt; return (halted, halt_depth_in_F, itinerary_symbols)
# depth counts F-events (diagonal returns).  cap steps for safety.
# =====================================================================
def run(a, b, maxsteps=400, sizecap=10 ** 18):
    syms = []
    for _ in range(maxsteps):
        f = fatal(a, b)
        if f:
            return True, syms, f
        s = symbol_of(a, b)
        syms.append(s)
        a, b, _ = R(a, b)
        if a > sizecap and b > sizecap:
            return False, syms, None
    return False, syms, None


# =====================================================================
# (1) coefficient growth of offset forms with depth
# =====================================================================
def coeff_growth():
    print("\n" + "=" * 68)
    print("(1) AFFINE OFFSET-FORM COEFFICIENT GROWTH WITH DEPTH d")
    print("    o_d(a,b) = p*a + q*b + r ; depth d = # of F (diagonal) events")
    print("=" * 68)
    # follow a family of seeds, collect (p,q,r) and |det| at each F-event
    seeds = [(6 + 4 * k, 13 + 8 * k) for k in range(60)]
    seeds += [(7 + 2 * k, 30 + 6 * k) for k in range(60)]
    by_depth = defaultdict(list)   # depth -> list of (maxpq, |det|, #C+#F)
    for (a0, b0) in seeds:
        A = IDENT
        a, b = a0, b0
        d = 0
        ncf = 0
        for _ in range(60):
            if fatal(a, b):
                break
            s = symbol_of(a, b)
            if s[1:] == 'C' or s[1:] == 'F':
                pass
            if s.endswith('F'):
                p, q, r = offset_form(A, s)
                d += 1
                by_depth[d].append((max(abs(p), abs(q)), abs(det_lin(A)),
                                    ncf + 1))
            if s != 'T':
                ncf += 1
            A = step_sym(A, s)
            a, b, _ = R(a, b)
    print(f"{'d':>3} {'n':>5} {'median max|p,q|':>16} {'ratio/prev':>11} "
          f"{'median|detP|':>14} {'|p,q|/sqrt|det|':>15}")
    prev = None
    for d in sorted(by_depth):
        vals = by_depth[d]
        if len(vals) < 5:
            continue
        mpq = sorted(v[0] for v in vals)[len(vals) // 2]
        mdet = sorted(v[1] for v in vals)[len(vals) // 2]
        ratio = (mpq / prev) if prev else float('nan')
        prev = mpq
        rel = mpq / math.sqrt(mdet) if mdet else float('nan')
        print(f"{d:>3} {len(vals):>5} {mpq:>16} {ratio:>11.3f} "
              f"{mdet:>14} {rel:>15.3f}")
    print("Interpretation: |det P| = 3^(#C+#F) exactly (sublattice index);")
    print("|p,q| grows geometrically, tracking sqrt|det| ~ 3^((#C+#F)/2).")


# =====================================================================
# (2) exact count of halting seeds in the N-box; scaling with N.
#     also decompose halts by depth and by cylinder.
# =====================================================================
def count_halting_exact(Ns):
    print("\n" + "=" * 68)
    print("(2) #HALTING SEEDS IN THE BOX, EXACT ENUMERATION")
    print("    region: 1<=a<=N, 1<=b<=N  (full box)")
    print("=" * 68)
    print(f"{'N':>6} {'#seeds':>10} {'#halting':>10} {'frac':>10} "
          f"{'#halt/N':>9} {'#halt/N^2':>11} {'maxFdepth':>9}")
    results = []
    for N in Ns:
        nseed = N * N
        nhalt = 0
        maxfd = 0
        for a in range(1, N + 1):
            for b in range(1, N + 1):
                halted, syms, _ = run(a, b)
                if halted:
                    nhalt += 1
                    fd = sum(1 for s in syms if s.endswith('F'))
                    if fd > maxfd:
                        maxfd = fd
        results.append((N, nseed, nhalt))
        print(f"{N:>6} {nseed:>10} {nhalt:>10} {nhalt / nseed:>10.5f} "
              f"{nhalt / N:>9.3f} {nhalt / nseed:>11.6f} {maxfd:>9}")
    return results


def count_halting_sampled(Ns, nsamp=200000, seed=12345):
    print("\n" + "=" * 68)
    print("(2b) #HALTING via uniform sampling in the box (large N)")
    print("=" * 68)
    rng = random.Random(seed)
    print(f"{'N':>8} {'#samp':>8} {'frac_halt':>11} {'frac*N':>9} "
          f"{'est#halt':>12} {'est/N':>9}")
    for N in Ns:
        h = 0
        for _ in range(nsamp):
            a = rng.randint(1, N)
            b = rng.randint(1, N)
            halted, _, _ = run(a, b)
            if halted:
                h += 1
        frac = h / nsamp
        est = frac * N * N
        print(f"{N:>8} {nsamp:>8} {frac:>11.6f} {frac * N:>9.2f} "
              f"{est:>12.1f} {est / N:>9.2f}")


# =====================================================================
# (2c)+(4) cylinder decomposition: distinct depth-d cylinders meeting
#          the box, and the elementary line-count "+1" budget.
# =====================================================================
def cylinder_count(Ns):
    print("\n" + "=" * 68)
    print("(2c/4) CYLINDER COUNT + ELEMENTARY LINE-COUNT BUDGET")
    print("  depth d = # F-events; cylinder = itinerary prefix up to d-th F.")
    print("  For each N: total distinct (cylinder) prefixes realized by box")
    print("  seeds, summed over all depths = the '+1' budget of the")
    print("  elementary line count.  Compare to N^2.")
    print("=" * 68)
    print(f"{'N':>6} {'#halt':>8} {'Sum_d #cyl(d)':>14} {'/N^2':>10} "
          f"{'/N':>9} {'/(N log N)':>11} {'maxd':>5}")
    for N in Ns:
        # for each seed, get the sequence of cylinder-prefixes (as tuples)
        # up to each F event; collect distinct prefixes per depth.
        cyl_by_depth = defaultdict(set)
        nhalt = 0
        for a in range(1, N + 1):
            for b in range(1, N + 1):
                halted, syms, _ = run(a, b)
                if halted:
                    nhalt += 1
                # build prefixes up to each F event
                pref = []
                d = 0
                for s in syms:
                    pref.append(s)
                    if s.endswith('F'):
                        d += 1
                        cyl_by_depth[d].add(tuple(pref))
        total_cyl = sum(len(v) for v in cyl_by_depth.values())
        maxd = max(cyl_by_depth) if cyl_by_depth else 0
        nn = N * N
        nlogn = N * math.log(N) if N > 1 else 1
        print(f"{N:>6} {nhalt:>8} {total_cyl:>14} {total_cyl / nn:>10.4f} "
              f"{total_cyl / N:>9.3f} {total_cyl / nlogn:>11.3f} {maxd:>5}")
        last_perdepth = cyl_by_depth
    # per-depth breakdown for the largest N (where does the count sit?)
    print(f"\nPer-depth #cylinders meeting box, N={Ns[-1]} "
          f"(#survivors-to-depth-d grows then the tree saturates):")
    print(f"{'d':>4} {'#cyl(d)':>10}")
    for d in sorted(last_perdepth):
        print(f"{d:>4} {len(last_perdepth[d]):>10}")
    print("\nElementary line count: #halting <= sum over (cyl,fatal-line)")
    print("meeting box of (segment/step + 1).  The '+1' total is bounded by")
    print("3 * (Sum_d #cyl(d) meeting box).  If that is o(N^2) the elementary")
    print("count gives a RIGOROUS o(N^2); the table shows its true growth.")


# =====================================================================
# (4b) "in-scale" cylinder count: only cylinders whose offset-form
#      coefficients are <= N (the FAT regime, where the fatal line has
#      lattice step <= N and the classical sector/lattice count is
#      rigorous with main term Leb*N^2 + O(N)).  Beyond this depth the
#      line has step > N: <=1 box point, generically 0 -- the THIN tail.
# =====================================================================
def inscale_cylinder_count(Ns):
    print("\n" + "=" * 68)
    print("(4b) IN-SCALE (FAT-REGIME) CYLINDER COUNT")
    print("  Count distinct depth-d cylinders realized by box seeds, but only")
    print("  up to the first F-event where the offset form max|p,q| > N")
    print("  (fatal-line lattice step exceeds N).  This is the regime where")
    print("  the per-cylinder lattice count is rigorous.  Compare to N^2.")
    print("=" * 68)
    print(f"{'N':>6} {'fat #cyl':>12} {'/N^2':>9} {'/N':>9} "
          f"{'/(N logN)':>10} {'max fat d':>10}")
    for N in Ns:
        fat = defaultdict(set)
        for a0 in range(1, N + 1):
            for b0 in range(1, N + 1):
                a, b = a0, b0
                A = IDENT
                pref = []
                d = 0
                for _ in range(400):
                    if fatal(a, b):
                        break
                    s = symbol_of(a, b)
                    pref.append(s)
                    if s.endswith('F'):
                        p, q, r = offset_form(A, s)
                        if max(abs(p), abs(q)) > N:
                            break  # entered thin regime; stop counting
                        d += 1
                        fat[d].add(tuple(pref))
                    A = step_sym(A, s)
                    a, b, _ = R(a, b)
        tot = sum(len(v) for v in fat.values())
        maxd = max(fat) if fat else 0
        nn = N * N
        nlogn = N * math.log(N)
        print(f"{N:>6} {tot:>12} {tot / nn:>9.4f} {tot / N:>9.3f} "
              f"{tot / nlogn:>10.3f} {maxd:>10}")
    print("\nIf fat #cyl = o(N^2): the fat regime is handled by rigorous")
    print("lattice counting, leaving ONLY the thin tail (offset step > N) as")
    print("the genuine obstruction -- matching the probe's thin-cylinder wall.")


# =====================================================================
# (3) large-sieve quantities: sublattice indices Q_d and N vs Q^2.
# =====================================================================
def large_sieve_quantities(N=2000):
    print("\n" + "=" * 68)
    print("(3) LARGE-SIEVE INPUT QUANTITIES")
    print("  Fatal condition o_d in {1,3,5} lives in cosets of the sublattice")
    print("  P_d Z^2 of index Q_d = |det P_d| = 3^(#C+#F).  Montgomery's")
    print("  large sieve threshold is (N + Q^2).  We tabulate, over cylinders")
    print("  realized by box seeds up to depth of first crossing into the")
    print("  fatal window, the indices Q_d and compare N vs Q_d and Q_d^2.")
    print("=" * 68)
    # gather, per depth d, the multiset of Q_d = |det P| at the d-th F-event
    # over a sweep of box seeds (sampled), plus the box-point count that the
    # 3 fatal cosets would trivially carry: ~ 3 N^2 / Q_d.
    rng = random.Random(999)
    q_by_depth = defaultdict(list)
    for _ in range(4000):
        a = rng.randint(1, N)
        b = rng.randint(1, N)
        A = IDENT
        d = 0
        for _ in range(50):
            if fatal(a, b):
                break
            s = symbol_of(a, b)
            if s.endswith('F'):
                d += 1
                q_by_depth[d].append(abs(det_lin(A)))
            A = step_sym(A, s)
            a, b, _ = R(a, b)
    print(f"N = {N}")
    print(f"{'d':>3} {'n':>5} {'median Q_d':>16} {'N/Q_d':>12} "
          f"{'N+Q^2 vs N^2':>16} {'triv 3N^2/Q_d':>14}")
    for d in sorted(q_by_depth):
        vals = q_by_depth[d]
        if len(vals) < 5:
            continue
        vals.sort()
        Q = vals[len(vals) // 2]
        nq = N / Q
        # large-sieve threshold N + Q^2 compared to the main term N^2
        thr = N + Q * Q
        triv = 3 * N * N / Q
        marker = "  <-- Q^2 >> N^2" if Q * Q > N * N else ""
        print(f"{d:>3} {len(vals):>5} {Q:>16} {nq:>12.4g} "
              f"{thr / (N * N):>16.4g} {triv:>14.4g}{marker}")
    print("\nReading: once Q_d > N (very shallow d), a single cylinder's 3")
    print("fatal cosets carry < 3N points in the box, and Q_d^2 >> N^2, so")
    print("the large-sieve threshold (N+Q^2) is ALREADY larger than the whole")
    print("box N^2 for one modulus -- the inequality is vacuous per cylinder.")


if __name__ == "__main__":
    print("verify symbolic affine forms vs exact map:", verify())
    coeff_growth()
    count_halting_exact([100, 200, 400, 600])
    count_halting_sampled([2000, 4000, 8000, 16000, 32000, 64000])
    cylinder_count([100, 200, 400, 600])
    inscale_cylinder_count([100, 200, 400, 600, 800])
    large_sieve_quantities(2000)
    print("\nSee docs/results/2026-09-08-large-sieve-count.md for the"
          " analysis and verdict.")

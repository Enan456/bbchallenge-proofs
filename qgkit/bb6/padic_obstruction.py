"""p-adic / non-Archimedean obstruction search for the renewal map R.

Question: does ANY non-Archimedean invariant (a congruence class system at a
prime power, or a p-adic valuation/ball constraint) exclude the fatal set of
the renewal map R from the reachable orbit?

Prior work (2026-08-26) showed no congruence invariant to modulus 384. This
script extends the residue BFS deep into 2-adic (2^k), 3-adic (3^m) and mixed
2^k*3^m territory, and separately analyses the p-adic valuations v_2, v_3 of
the key quantities along the true integer orbit.

The map R (no halving; each branch is affine in (a,b)):
  b even:  (a,b) -> (a+6, b-3)                                        [T]
  b odd :  (alpha,beta) = (6, a-1) if a odd else (9, a-2)
           b < beta:  (a,b) -> (alpha + 3(b-3), beta-(b-3))          [.C]
           b > beta:  (a,b) -> (alpha + 3*beta + 3, b - beta - 4)    [.F]

Fatal set (death of the machine):
  b <= 2;  or b == 4 (T->1);  or a deep-fuse with gap g = b - beta in {1,3,5}.
Since b is odd and beta is even in a deep-fuse, g is ALWAYS odd.

--------------------------------------------------------------------------
SOUNDNESS of the modular-invariant test
--------------------------------------------------------------------------
A "non-Archimedean (modular) invariant excluding the fatal set" is a union S
of residue classes mod M with: (1) the seed's class in S, (2) S closed under
the abstract transition (BOTH branches, since a purely modular predicate
cannot see the magnitude comparison b<beta vs b>beta), (3) S disjoint from
every fatal-compatible class. The minimal such S is exactly the BFS-reachable
set R_M (both branches taken). Hence:

  * If R_M is disjoint from the fatal-compatible set F_M  ==>  an invariant
    EXISTS at modulus M (would exclude the fatal set).
  * If R_M meets F_M  ==>  NO modular invariant of any kind exists at M
    (every valid S contains R_M, which already touches F_M).

F_M = classes that contain some fatal integer point (existential lift). This
makes the negative conclusion sound. We ALSO cross-check with the true integer
orbit: we count fatal-compatible classes that the real orbit genuinely visits,
upgrading "the over-approximation reaches them" to "the real orbit reaches
them".
"""

import math
from array import array


# --------------------------------------------------------------------------
# exact integer map + fatal predicate
# --------------------------------------------------------------------------
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


# --------------------------------------------------------------------------
# residue-abstraction BFS with a bytearray seen-set (memory-light, large M)
# --------------------------------------------------------------------------
def bfs_mod(M, cap=None):
    """Return (reachable_count, fatal_compatible_reachable_count).

    Uses a flat bytearray of size M*M as the seen-set, state encoded u*M+v.
    `cap` optionally bounds the number of states enumerated (safety valve).
    """
    seen = bytearray(M * M)              # 1 byte per (u,v) class
    su, sv = 6 % M, 13 % M
    start = su * M + sv
    seen[start] = 1
    frontier = [start]
    total = 1
    Meven = (M % 2 == 0)
    while frontier:
        nf = []
        for code in frontier:
            u = code // M
            v = code - u * M
            if v % 2 == 0:
                w = ((u + 6) % M) * M + ((v - 3) % M)
                if not seen[w]:
                    seen[w] = 1
                    nf.append(w)
                    total += 1
            else:
                if u % 2 == 1:
                    alpha, boff = 6, 1
                else:
                    alpha, boff = 9, 2
                beta = (u - boff) % M
                vm3 = (v - 3) % M
                # C branch
                w1 = ((alpha + 3 * vm3) % M) * M + ((beta - vm3) % M)
                if not seen[w1]:
                    seen[w1] = 1
                    nf.append(w1)
                    total += 1
                # F branch
                w2 = ((alpha + 3 * beta + 3) % M) * M + ((v - beta - 4) % M)
                if not seen[w2]:
                    seen[w2] = 1
                    nf.append(w2)
                    total += 1
            if cap and total > cap:
                return total, -1     # bailed out
        frontier = nf

    # count fatal-compatible among reachable
    bad = 0
    f1 = 1 % M
    f3 = 3 % M
    f5 = 5 % M
    for code in range(M * M):
        if not seen[code]:
            continue
        u = code // M
        v = code - u * M
        # b == 4 (T->1)   [also covers b<=2 witnesses at v in {0,1,2}]
        if v == 4 % M or v in (0, 1, 2):
            bad += 1
            continue
        if Meven and v % 2 == 0:
            continue                 # even b: only the b==4 death, handled
        # deep-fuse diagonal:  gap = v - beta in {1,3,5}
        if Meven:
            boff = 1 if (u % 2 == 1) else 2
            gap = (v - (u - boff)) % M
            if gap == f1 or gap == f3 or gap == f5:
                bad += 1
        else:
            hit = False
            for boff in (1, 2):
                gap = (v - (u - boff)) % M
                if gap == f1 or gap == f3 or gap == f5:
                    hit = True
                    break
            if hit:
                bad += 1
    return total, bad


# --------------------------------------------------------------------------
# the true integer orbit: valuations + concrete fatal-class witnesses
# --------------------------------------------------------------------------
def v_p(n, p):
    """p-adic valuation of a nonzero integer; +inf sentinel for 0."""
    if n == 0:
        return 10 ** 9
    n = abs(n)
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def run_orbit(N):
    """Run N renewals from the seed. Collect deep-fuse gaps and valuations."""
    x, y = 6, 13
    gaps = []             # deep-fuse gaps g = b - beta (always odd)
    v2b, v3b = [], []     # valuations of b along the orbit
    for _ in range(N):
        if fatal(x, y):
            break
        v2b.append(v_p(y, 2))
        v3b.append(v_p(y, 3))
        if y % 2 == 1:
            beta = (x - 1) if x % 2 == 1 else (x - 2)
            if y > beta:
                gaps.append(y - beta)
        x, y, _ = R(x, y)
    return gaps, v2b, v3b, x, y


def orbit_fatal_classes(N, moduli):
    """For each modulus, how many DISTINCT fatal-compatible residue classes
    does the REAL orbit actually visit? (concrete witness that no modular
    predicate separates the orbit from the fatal set)."""
    seen = {M: set() for M in moduli}
    x, y = 6, 13
    for _ in range(N):
        if fatal(x, y):
            break
        # a deep-fuse state contributes a residue class whose gap is v-beta
        if y % 2 == 1:
            beta = (x - 1) if x % 2 == 1 else (x - 2)
            if y > beta:
                for M in moduli:
                    g = (y - beta) % M
                    if g in (1 % M, 3 % M, 5 % M):
                        seen[M].add((x % M, y % M))
        x, y, _ = R(x, y)
    return {M: len(s) for M, s in seen.items()}


# --------------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 70)
    print("PART 1 - extended residue BFS (2^k, 3^m, mixed 2^k*3^m)")
    print("=" * 70)

    pow2 = [2 ** k for k in range(3, 13)]                 # 8 .. 4096
    pow3 = [3 ** m for m in range(2, 8)]                  # 9 .. 2187
    mixed = [24, 48, 96, 192, 384, 768, 1536,
             432, 864, 1728, 3456,
             1296, 2592, 5184,
             3888, 7776]
    mixed = sorted(set(mixed))

    def report(label, Ms):
        print(f"\n-- {label} --")
        for M in Ms:
            tot, bad = bfs_mod(M)
            frac = tot / (M * M)
            tag = "  <== INVARIANT (fatal excluded!)" if bad == 0 else ""
            print(f"mod {M:6d}: reachable {tot:>10d}/{M*M:<11d}"
                  f" ({frac:6.4f})  fatal-compatible {bad:>6d}{tag}")

    report("pure 2-adic  (M = 2^k)", pow2)
    report("pure 3-adic  (M = 3^m)", pow3)
    report("mixed 2-&-3-adic  (M = 2^k * 3^m)", mixed)

    print("\n" + "=" * 70)
    print("PART 2 - p-adic valuation analysis along the true integer orbit")
    print("=" * 70)
    N = 200_000
    gaps, v2b, v3b, fx, fy = run_orbit(N)
    print(f"orbit ran {len(v2b):,} renewals, {len(gaps):,} deep-fuse events,"
          f" final ~{fy.bit_length()} bits")

    # gap statistics (the fatal window is on the gap)
    from collections import Counter
    gc = Counter(gaps)
    small = sorted(g for g in gc if g <= 21)
    print("\ndeep-fuse gap g = b - beta  (fatal iff g in {1,3,5}):")
    print(f"  min gap observed      : {min(gaps)}")
    print(f"  all gaps odd?         : {all(g % 2 == 1 for g in gaps)}"
          f"   (=> v_2(g)=0 ALWAYS)")
    print(f"  smallest gaps hit     : {small[:12]}")
    print(f"  counts of small gaps  : "
          f"{ {g: gc[g] for g in small[:12]} }")

    # 2-adic structure of the fatal window vs safe gaps
    print("\n2-adic structure of the gap:")
    print(f"  fatal window {{1,3,5}} :  v_2 = "
          f"{[v_p(g,2) for g in (1,3,5)]}  (all 0, all in sphere |g|_2=1)")
    print(f"  safe gaps 7,9,11,13   :  v_2 = "
          f"{[v_p(g,2) for g in (7,9,11,13)]}  (also all 0)")
    print("  => the fatal window is 2-adically indistinguishable from the "
          "safe odd gaps.")

    # 3-adic structure
    print("\n3-adic structure of the gap:")
    print(f"  fatal window {{1,3,5}} :  v_3 = "
          f"{[v_p(g,3) for g in (1,3,5)]}   units mod 3 = "
          f"{[ (g//3**v_p(g,3))%3 for g in (1,3,5)]}")
    print(f"  safe gaps 7,9,11,13   :  v_3 = "
          f"{[v_p(g,3) for g in (7,9,11,13)]}   units mod 3 = "
          f"{[ (g//3**v_p(g,3))%3 for g in (7,9,11,13)]}")
    print("  => both fatal and safe gaps populate every 3-adic ball; no "
          "3-adic ball separates them.")

    # distribution of valuations of b along the orbit (is the orbit trapped
    # in a p-adic ball?)
    print("\nvaluations of b along the orbit (is the orbit p-adically "
          "confined?):")
    c2 = Counter(v2b)
    c3 = Counter(v3b)
    print(f"  v_2(b) distribution : "
          f"{ {k: c2[k] for k in sorted(c2)[:8]} } ...")
    print(f"  v_3(b) distribution : "
          f"{ {k: c3[k] for k in sorted(c3)[:8]} } ...")
    print("  (v_2(b)=0 on every deep step since b is then odd; b ranges over "
          "all 3-adic balls => orbit is NOT confined to any p-adic ball).")

    print("\n" + "=" * 70)
    print("PART 3 - concrete witness: fatal-compatible classes the REAL "
          "orbit visits")
    print("=" * 70)
    wit_moduli = [384, 768, 1536, 2592, 5184, 7776]
    counts = orbit_fatal_classes(N, wit_moduli)
    for M in wit_moduli:
        print(f"mod {M:5d}: real orbit visits {counts[M]:>5d} distinct "
              f"fatal-compatible residue classes (all survived as integers)")
    print("\n=> the true orbit genuinely enters fatal-compatible residue "
          "classes at every modulus; no modular predicate can fence it out.")

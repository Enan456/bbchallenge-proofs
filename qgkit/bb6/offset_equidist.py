"""Offset-equidistribution measurement for the renewal map R (bb6).

Empirical experiment (NOT a proof). Measures whether the diagonal-crossing
offset  o = b - beta  equidistributes finely enough that the fraction of
crossings landing in the width-3 fatal window {1,3,5} is summable along
almost every orbit.

Reproducible: fixed explicit integer seeds, native arbitrary-precision ints,
no randomness. See docs/results/2026-09-04-offset-equidistribution.md.
"""
import math
from collections import Counter, defaultdict


# ---- the verified map (copied verbatim from renewal_analysis3.py) ----
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


# ---- reproducible seed ensemble ----
def make_seeds():
    seeds = []
    # deterministic family (a even, b odd): (6+4k, 13+8k)
    for k in range(300):
        seeds.append((6 + 4 * k, 13 + 8 * k))
    # "large" seeds: iterate R a fixed number of steps from the family,
    # then use the resulting state as a fresh seed (deterministic, big).
    for k in range(0, 300):
        a, b = 6 + 4 * k, 13 + 8 * k
        alive = True
        for _ in range(40):
            if fatal(a, b):
                alive = False
                break
            a, b, _ = R(a, b)
        if alive and b % 2 == 1:      # keep only usable odd-b states
            seeds.append((a, b))
    return seeds


MAX_RENEWALS = 3000


def run():
    seeds = make_seeds()
    print(f"# ensemble: {len(seeds)} seeds, up to {MAX_RENEWALS} renewals each")

    # accumulators -----------------------------------------------------
    offsets = []                       # o at every above-diagonal event (survivors)
    off_by_bitbin = defaultdict(list)  # bitlen(a) -> list of o
    ratio_o_over_beta = []
    ratio_o_over_b = []
    sym_counts = Counter()
    trun_lengths = Counter()

    total_crossings = 0                # above-diagonal events incl. terminal fatal
    diagonal_deaths = 0
    axis_deaths = 0
    survived = 0

    # per-orbit model-hazard sums (summability)
    per_orbit_hazard_sum = []
    tail_after = defaultdict(float)    # k -> summed hazard for crossings index>=k

    # residue coverage between consecutive F-crossings (mechanism check)
    gap_steps = []                     # #renewals between consecutive crossings
    residues_between = []              # for M=6: set of o-mod-6 seen (trivial: single)
    # global mod-M tallies
    modM_list = [2, 4, 6, 8, 16, 384]
    modM_tally = {M: Counter() for M in modM_list}

    # certified-seed specifics
    cert_offsets = []
    cert_min_offset = None

    for (a0, b0) in seeds:
        a, b = a0, b0
        crossing_idx = 0
        hz_sum = 0.0
        last_cross_step = None
        run_t = 0
        cert = (a0, b0) == (6, 13)
        died = None
        for step in range(MAX_RENEWALS):
            f = fatal(a, b)
            if f:
                if f == 'diagonal':
                    total_crossings += 1
                    diagonal_deaths += 1
                else:
                    axis_deaths += 1
                died = f
                break
            # above-diagonal (potential-fatal) event: b odd, b>beta  (F-branch)
            if b % 2 == 1:
                beta = beta_of(a)
                if b > beta:
                    o = b - beta               # odd, >=7 for a survivor here
                    total_crossings += 1
                    offsets.append(o)
                    off_by_bitbin[a.bit_length()].append(o)
                    ratio_o_over_beta.append(o / beta if beta > 0 else 0)
                    ratio_o_over_b.append(o / b)
                    for M in modM_list:
                        modM_tally[M][o % M] += 1
                    # model hazard for THIS crossing under equidistribution:
                    # o ~ uniform over odd values in its admissible range;
                    # scale of that range measured below as ~ 0.5*beta (see report).
                    # p = 3 fatal odds / (#odd values up to range)
                    rng = beta                 # conservative admissible range for o
                    n_odd = max(1, rng // 2)
                    p = min(1.0, 3.0 / n_odd)
                    hz_sum += p
                    tail_after[crossing_idx] += p
                    if last_cross_step is not None:
                        gap_steps.append(step - last_cross_step)
                    last_cross_step = step
                    crossing_idx += 1
                    if cert:
                        cert_offsets.append(o)
                        cert_min_offset = o if cert_min_offset is None \
                            else min(cert_min_offset, o)
            a, b, s = R(a, b)
            base = s if s == 'T' else s[-1]
            sym_counts[base] += 1
            if base == 'T':
                run_t += 1
            else:
                if run_t:
                    trun_lengths[run_t] += 1
                run_t = 0
        else:
            survived += 1
        if run_t:
            trun_lengths[run_t] += 1
        per_orbit_hazard_sum.append(hz_sum)

    # ================= REPORTS =================
    print("\n## symbols / mechanism")
    print("symbol counts:", dict(sym_counts))
    print("T-run length distribution:", dict(trun_lengths))
    if gap_steps:
        gs = sorted(gap_steps)
        print(f"gap (renewals) between consecutive above-diagonal events: "
              f"min {gs[0]}, median {gs[len(gs)//2]}, "
              f"mean {sum(gs)/len(gs):.2f}, max {gs[-1]}")

    print("\n## crossing / death census")
    print(f"total above-diagonal events: {total_crossings:,}")
    print(f"diagonal (offset) deaths:    {diagonal_deaths}")
    print(f"axis (b<=2 / b==4) deaths:   {axis_deaths}")
    print(f"orbits surviving {MAX_RENEWALS} renewals: {survived}/{len(seeds)}")
    if total_crossings:
        print(f"empirical per-crossing diagonal-death fraction: "
              f"{diagonal_deaths/total_crossings:.3e}")

    print("\n## (1) offset mod-M uniformity over admissible (odd) residues")
    for M in modM_list:
        tally = modM_tally[M]
        n = sum(tally.values())
        admissible = [r for r in range(M) if r % 2 == 1] if M % 2 == 0 \
            else list(range(M))
        # o is always odd; for even M admissible = odd residues.
        k = len(admissible)
        exp = n / k
        chi2 = sum((tally.get(r, 0) - exp) ** 2 / exp for r in admissible) \
            if exp > 0 else 0
        # max relative deviation of any admissible residue from uniform frac
        fracs = [tally.get(r, 0) / n for r in admissible] if n else []
        unif = 1.0 / k
        maxdev = max(abs(fr - unif) for fr in fracs) if fracs else 0
        print(f"  mod {M:>3}: {k:>3} admissible residues, N={n:,}, "
              f"chi2={chi2:,.1f} (dof {k-1}), "
              f"chi2/dof={chi2/max(1,k-1):.3f}, "
              f"max|frac-1/k|={maxdev:.4f} (1/k={unif:.4f})")
        # spot-print the residue fractions for the small moduli
        if M <= 8 and n:
            print("        residue fractions:",
                  {r: round(tally.get(r, 0) / n, 4) for r in admissible})

    print("\n## (2) fatal-window scale & hit fraction")
    if offsets:
        os_ = sorted(offsets)
        n = len(os_)
        print(f"survivor offsets recorded: {n:,}")
        print(f"  min {os_[0]}, p1 {os_[n//100]}, median {os_[n//2]}, "
              f"p99 {os_[min(n-1,99*n//100)]}, max {os_[-1]}")
        print(f"  smallest 12 offsets seen: {os_[:12]}")
        # low-window occupancy: fraction with o in successive width-3 odd windows
        def frac_window(lo):                    # {lo, lo+2, lo+4}
            return sum(1 for o in offsets if o in (lo, lo+2, lo+4)) / n
        print("  survivor occupancy of width-3 odd windows (equidist => flat "
              "near 0, minus the deleted fatal window):")
        for lo in (1, 7, 13, 19, 25, 31):
            tag = "  <- FATAL {1,3,5} (survivors never here)" if lo == 1 else ""
            print(f"    o in {{{lo},{lo+2},{lo+4}}}: "
                  f"{frac_window(lo):.5f}{tag}")
        # offset scale relative to size
        rb = ratio_o_over_beta
        rB = ratio_o_over_b
        rb.sort(); rB.sort()
        print(f"  o/beta : median {rb[len(rb)//2]:.3f}, "
              f"mean {sum(rb)/len(rb):.3f}, max {rb[-1]:.3f}")
        print(f"  o/b    : median {rB[len(rB)//2]:.3f}, "
              f"mean {sum(rB)/len(rB):.3f}, max {rB[-1]:.3f}")
        # density of odds near 0 -> predicted hit fraction 3*rho.
        # estimate rho from the flat low-window occupancy just above the window
        rho = frac_window(7) / 3.0        # per-odd-integer prob near 0
        print(f"  estimated per-odd-integer density near 0 (rho, from window "
              f"{{7,9,11}}): {rho:.3e}")
        print(f"  => predicted per-crossing fatal prob 3*rho = {3*rho:.3e}")
        # C in hazard ~ C/size : fit against median beta-scale
        # hit prob ~ 3/(scale/2)=6/scale; using o/beta median m, scale~m*beta,
        med_ob = rb[len(rb)//2]
        print(f"  median o/beta = {med_ob:.3f}; if o~Uniform(0,{med_ob:.2f}*beta] "
              f"then hit ~ 6/({med_ob:.2f}*beta) = {6/med_ob:.2f}/beta "
              f"=> C≈{6/med_ob:.2f} vs known ~1.74/size")

    print("\n## (2b) hit fraction vs size (bit-length bins)")
    print("  bitlen(a) | #crossings | mean o | mean o/beta | model p=6/beta")
    for bl in sorted(off_by_bitbin):
        lst = off_by_bitbin[bl]
        if len(lst) < 30:
            continue
        mo = sum(lst) / len(lst)
        # beta ~ a ~ 2^bl; model p per crossing = 6/beta ~ 6/2^bl
        approx_beta = 2 ** (bl - 1)
        print(f"    {bl:>6}   | {len(lst):>9,} | {mo:>10.1f} | "
              f"{mo/approx_beta:>10.3f} | {6/approx_beta:.2e}")

    print("\n## (3) summability of per-orbit model hazard sum")
    hs = sorted(per_orbit_hazard_sum)
    m = len(hs)
    print(f"per-orbit sum of model fatal-probabilities (sum 3/(beta/2) over "
          f"crossings):")
    print(f"  min {hs[0]:.4f}, median {hs[m//2]:.4f}, "
          f"mean {sum(hs)/m:.4f}, p99 {hs[min(m-1,99*m//100)]:.4f}, "
          f"max {hs[-1]:.4f}")
    # tail: summed hazard for crossings at index >= k, averaged per orbit
    print("  geometric tail (avg over orbits of summed hazard for crossing "
          "index >= k):")
    tot_orbits = len(seeds)
    for k in (0, 1, 2, 5, 10, 20, 40, 80):
        tail = sum(v for idx, v in tail_after.items() if idx >= k) / tot_orbits
        print(f"    k={k:>3}:  {tail:.4e}")

    print("\n## (5) certified seed (6,13) vs ensemble")
    if cert_offsets:
        co = sorted(cert_offsets)
        cn = len(co)
        print(f"(6,13): {cn} above-diagonal events over its run")
        print(f"  min offset {co[0]}, median {co[cn//2]}, max {co[-1]}")
        print(f"  smallest 10 offsets: {co[:10]}")
        print(f"  min offset stays >= {cert_min_offset} (fatal window is 1,3,5)")
        # compare mod-6 residue split to ensemble
        c6 = Counter(o % 6 for o in cert_offsets)
        print(f"  (6,13) offset mod 6 split: "
              f"{{{','.join(f'{r}:{c6.get(r,0)/cn:.3f}' for r in (1,3,5))}}}")
        e6 = modM_tally[6]
        en = sum(e6.values())
        print(f"  ensemble  offset mod 6 split: "
              f"{{{','.join(f'{r}:{e6.get(r,0)/en:.3f}' for r in (1,3,5))}}}")


if __name__ == "__main__":
    run()

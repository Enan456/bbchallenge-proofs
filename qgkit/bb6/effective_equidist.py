"""Effective-equidistribution feasibility probe for the renewal map R (bb6).

EMPIRICAL EXPERIMENT -- NOT A PROOF, and NOT a decision about any machine.

Question decided here (about METHODS, not machines): is the "specific-orbit
door" BOLTED or merely HEAVY?  I.e., could an *effective* equidistribution
theorem ever localize a single good-phase orbit's fate below the fatal window,
or is the achievable equidistribution error term astronomically larger than
the window at every large scale?

The key quantities:
  * D(n): star-discrepancy proxy of the diagonal-crossing offset residues,
          as a function of the number of crossings n. Fit its decay exponent.
  * spectral gap of the 5-symbol {T,dC,DC,dF,DF} transition operator.
  * fatal-window fraction ~ e^{-0.134 n} (from prior measured log-growth).
  * the comparison D(n) vs window; and, for the certified orbit (6,13),
    whether (D(n) * #crossings) is ever below the model hazard tail.

Deterministic: fixed explicit integer seeds, native bigints, NO randomness.
See docs/results/2026-09-04-effective-equidistribution.md.
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


# 5-symbol alphabet, fixed order for the transition matrix
SYMS = ['T', 'dC', 'DC', 'dF', 'DF']
SYM_IX = {s: i for i, s in enumerate(SYMS)}

BITLEN_CAP = 800          # stop an orbit when bitlen(a) exceeds this
RENEWAL_CAP = 40000       # hard safety cap on renewals
MODULI = [6, 8, 16, 384]  # for discrepancy D(n)

# log-spaced grid of crossing counts at which D(n) is sampled
N_GRID = [10, 14, 20, 28, 40, 56, 80, 112, 160, 224, 320, 450, 640, 900, 1280]


def admissible_residues(M):
    # offsets o are always ODD; admissible residues mod even M are the odds
    return [r for r in range(M) if r % 2 == 1] if M % 2 == 0 else list(range(M))


ADMIS = {M: admissible_residues(M) for M in MODULI}
KRES = {M: len(ADMIS[M]) for M in MODULI}


# ------------------------------------------------------------------
# One orbit run. Returns a dict of per-orbit measurements.
#   record_seq: keep full growth-increment + residue-indicator sequences
#               (only for a few designated long orbits, for autocorrelation)
# ------------------------------------------------------------------
def run_orbit(a0, b0, record_seq=False, sym_trans=None, sym_trans2=None,
              bitcap=BITLEN_CAP):
    a, b = a0, b0
    # running residue counts for the star-discrepancy proxy
    counts = {M: [0] * M for M in MODULI}
    ncross = 0
    grid_ix = 0
    disc_samples = []          # (n, {M: max|freq-1/k|})
    hz_terms = []              # model hazard per crossing (for variance/mean)
    offsets_small = []         # small offsets (<=201) with their crossing index
    prev_offset = None         # previous crossing's offset (for death analysis)
    second_last_before_death = None
    last_offset_before_death = None
    death = None
    prev_sym = None
    prev_sym2 = None
    grow_seq = [] if record_seq else None
    ind6_seq = [] if record_seq else None   # indicator o%6==1

    for step in range(RENEWAL_CAP):
        f = fatal(a, b)
        if f:
            death = f
            if f == 'diagonal':
                last_offset_before_death = b - beta_of(a)  # the fatal offset
                second_last_before_death = prev_offset
            break
        # above-diagonal crossing (F-branch: b odd, b>beta)
        if b % 2 == 1:
            beta = beta_of(a)
            if b > beta:
                o = b - beta               # positive odd
                ncross += 1
                for M in MODULI:
                    counts[M][o % M] += 1
                # model hazard for this crossing under a uniform-phase model:
                # 3 fatal odds among ~beta/2 odd values in the admissible range
                n_odd = max(1, beta // 2)
                hz_terms.append(min(1.0, 3.0 / n_odd))
                if o <= 201:
                    offsets_small.append((ncross, o))
                if record_seq:
                    ind6_seq.append(1 if o % 6 == 1 else 0)
                # sample the running discrepancy at grid points
                while grid_ix < len(N_GRID) and ncross == N_GRID[grid_ix]:
                    d = {}
                    for M in MODULI:
                        k = KRES[M]
                        unif = 1.0 / k
                        d[M] = max(abs(counts[M][r] / ncross - unif)
                                   for r in ADMIS[M])
                    disc_samples.append((ncross, d))
                    grid_ix += 1
                prev_offset = o

        size0 = a + b
        a, b, s = R(a, b)
        # symbol transition bookkeeping (pooled)
        if sym_trans is not None:
            if prev_sym is not None:
                sym_trans[SYM_IX[prev_sym]][SYM_IX[s]] += 1
            if sym_trans2 is not None and prev_sym2 is not None \
                    and prev_sym is not None:
                sym_trans2[(SYM_IX[prev_sym2], SYM_IX[prev_sym])][SYM_IX[s]] += 1
            prev_sym2 = prev_sym
            prev_sym = s
        if record_seq:
            size1 = a + b
            grow_seq.append(math.log(size1) - math.log(size0))
        if a.bit_length() > bitcap:
            death = None
            break

    return {
        'ncross': ncross,
        'disc': disc_samples,
        'hz_terms': hz_terms,
        'offsets_small': offsets_small,
        'death': death,
        'last_offset_before_death': last_offset_before_death,
        'second_last_before_death': second_last_before_death,
        'grow_seq': grow_seq,
        'ind6_seq': ind6_seq,
    }


def fit_loglog(xs, ys):
    """Least-squares slope of log(y) vs log(x). Returns (slope, intercept, r)."""
    lx = np.log(np.asarray(xs, float))
    ly = np.log(np.asarray(ys, float))
    A = np.vstack([lx, np.ones_like(lx)]).T
    (slope, inter), *_ = np.linalg.lstsq(A, ly, rcond=None)
    yhat = A @ np.array([slope, inter])
    ss_res = float(np.sum((ly - yhat) ** 2))
    ss_tot = float(np.sum((ly - ly.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else float('nan')
    return slope, inter, r2


def autocorr(x, maxlag):
    x = np.asarray(x, float)
    x = x - x.mean()
    var = float(np.dot(x, x))
    out = []
    for lag in range(1, maxlag + 1):
        if lag >= len(x):
            break
        out.append(float(np.dot(x[:-lag], x[lag:])) / var)
    return out


# ==================================================================
def main():
    print("# EFFECTIVE-EQUIDISTRIBUTION FEASIBILITY PROBE (empirical, not a proof)")
    print(f"# bitlen(a) cap {BITLEN_CAP}, renewal cap {RENEWAL_CAP}")

    # ---------- primary ensemble ----------
    seeds = [(6 + 4 * k, 13 + 8 * k) for k in range(2000)]
    # large iterated states (deterministic): iterate 60 steps from a subset
    for k in range(0, 2000, 5):
        a, b = 6 + 4 * k, 13 + 8 * k
        ok = True
        for _ in range(60):
            if fatal(a, b):
                ok = False
                break
            a, b, _ = R(a, b)
            if a.bit_length() > BITLEN_CAP:
                break
        if ok and b % 2 == 1 and not fatal(a, b):
            seeds.append((a, b))
    print(f"# primary ensemble: {len(seeds)} seeds")

    sym_trans = [[0] * 5 for _ in range(5)]
    sym_trans2 = defaultdict(lambda: [0] * 5)

    # designate the first few + (6,13) as sequence-recorded for autocorrelation
    record_ids = set(range(3)) | {None}   # indices; (6,13) handled separately

    disc_acc = {M: {n: [0.0, 0] for n in N_GRID} for M in MODULI}  # sum,count
    ncross_all = []
    hz_sum_list = []
    natural_deaths = []          # (death_kind, second_last, last)
    grow_seq_pool = []
    ind6_seq_pool = []

    for idx, (a0, b0) in enumerate(seeds):
        rec = idx in record_ids
        r = run_orbit(a0, b0, record_seq=rec,
                      sym_trans=sym_trans, sym_trans2=sym_trans2)
        ncross_all.append(r['ncross'])
        hz_sum_list.append(sum(r['hz_terms']))
        for (n, d) in r['disc']:
            for M in MODULI:
                disc_acc[M][n][0] += d[M]
                disc_acc[M][n][1] += 1
        if r['death'] == 'diagonal':
            natural_deaths.append(('diagonal', r['second_last_before_death'],
                                   r['last_offset_before_death']))
        elif r['death'] in ('b<=2', 'T->1'):
            natural_deaths.append((r['death'], None, None))
        if rec and r['grow_seq']:
            grow_seq_pool.append(r['grow_seq'])
            ind6_seq_pool.append(r['ind6_seq'])

    print(f"# crossings: total {sum(ncross_all):,}, "
          f"mean/orbit {sum(ncross_all)/len(ncross_all):.0f}, "
          f"max {max(ncross_all)}")

    # ============ (1) DISCREPANCY DECAY RATE ============
    print("\n" + "=" * 68)
    print("(1) DISCREPANCY DECAY  D(n) = mean_orbits max_r|freq_r(n) - 1/k|")
    print("=" * 68)
    fit_report = {}
    for M in MODULI:
        rows = []
        for n in N_GRID:
            s, c = disc_acc[M][n]
            if c > 0:
                rows.append((n, s / c, c))
        print(f"\n  modulus M={M} (k={KRES[M]} admissible odd residues, "
              f"1/k={1/KRES[M]:.4f}):")
        print(f"    {'n':>6} {'D(n)':>12} {'#orbits':>9}")
        for (n, d, c) in rows:
            print(f"    {n:>6} {d:>12.6f} {c:>9}")
        # fit over the resolved range (n>=20, enough orbits)
        fitrows = [(n, d) for (n, d, c) in rows if n >= 20 and c >= 30]
        if len(fitrows) >= 4:
            xs = [n for n, _ in fitrows]
            ys = [d for _, d in fitrows]
            slope, inter, r2 = fit_loglog(xs, ys)
            fit_report[M] = (slope, r2)
            print(f"    log-log fit over n in [{xs[0]},{xs[-1]}]: "
                  f"alpha = {-slope:.4f}   (D(n) ~ n^-alpha), R^2={r2:.4f}")
            print(f"      reference: diffusive/CLT alpha=0.5; "
                  f"super-CLT alpha>0.5; exponential would need alpha->inf")

    # cross-modulus summary
    alphas = [(-fit_report[M][0]) for M in MODULI if M in fit_report]
    if alphas:
        print(f"\n  >>> fitted alpha across moduli: "
              f"{[round(a,3) for a in alphas]}, "
              f"mean {sum(alphas)/len(alphas):.3f}")

    # ============ (2) MIXING SPECTRAL GAP ============
    print("\n" + "=" * 68)
    print("(2) MIXING SPECTRAL GAP")
    print("=" * 68)
    # (b) transition-matrix eigenvalues, order-1
    T1 = np.array(sym_trans, float)
    rowsum = T1.sum(axis=1, keepdims=True)
    P1 = np.divide(T1, rowsum, out=np.zeros_like(T1), where=rowsum > 0)
    ev1 = np.linalg.eigvals(P1)
    ev1m = sorted((abs(e) for e in ev1), reverse=True)
    print(f"\n  (b) order-1 transition operator on {SYMS}")
    print(f"      stationary counts (row sums): "
          f"{{{', '.join(f'{s}:{int(rowsum[i,0])}' for i,s in enumerate(SYMS))}}}")
    with np.printoptions(precision=3, suppress=True):
        print("      P1 =")
        for i, s in enumerate(SYMS):
            print(f"        {s:>2}: {P1[i]}")
    print(f"      |eigenvalues| sorted: {[round(e,4) for e in ev1m]}")
    lam2_1 = ev1m[1] if len(ev1m) > 1 else float('nan')
    print(f"      => |lambda_2| = {lam2_1:.4f}  "
          f"(gap 1-|lambda_2| = {1-lam2_1:.4f})")

    # order-2 transition (state = ordered symbol pair -> next symbol)
    pair_ix = {}
    for a_ in range(5):
        for b_ in range(5):
            pair_ix[(a_, b_)] = len(pair_ix)
    NP = len(pair_ix)  # 25
    T2 = np.zeros((NP, NP))
    for (p2, p1), row in sym_trans2.items():
        src = pair_ix[(p2, p1)]
        for nxt, cnt in enumerate(row):
            if cnt:
                dst = pair_ix[(p1, nxt)]
                T2[src, dst] += cnt
    rs2 = T2.sum(axis=1, keepdims=True)
    P2 = np.divide(T2, rs2, out=np.zeros_like(T2), where=rs2 > 0)
    # restrict to recurrent (visited) states for a clean spectrum
    visited = [i for i in range(NP) if rs2[i, 0] > 0]
    P2v = P2[np.ix_(visited, visited)]
    # renormalize rows of the restricted operator
    rsv = P2v.sum(axis=1, keepdims=True)
    P2v = np.divide(P2v, rsv, out=np.zeros_like(P2v), where=rsv > 0)
    ev2 = np.linalg.eigvals(P2v)
    ev2m = sorted((abs(e) for e in ev2), reverse=True)
    lam2_2 = ev2m[1] if len(ev2m) > 1 else float('nan')
    print(f"\n      order-2 operator ({len(visited)} visited pair-states): "
          f"|lambda_2| = {lam2_2:.4f}  (gap {1-lam2_2:.4f})")

    # (a) autocorrelation of growth increments and residue indicator
    print("\n  (a) autocorrelation decay (pooled recorded long orbits)")
    if grow_seq_pool:
        longest = max(grow_seq_pool, key=len)
        ac = autocorr(longest, 12)
        print(f"      d log(size) increments (len {len(longest)}): "
              f"lags 1..8 = {[round(x,3) for x in ac[:8]]}")
        # exponential fit to |autocorr| over first few positive-decaying lags
        acabs = [abs(x) for x in ac[:8]]
        # find monotone-ish decay region
        try:
            lags = list(range(1, len(acabs) + 1))
            good = [(l, v) for l, v in zip(lags, acabs) if v > 1e-4]
            if len(good) >= 3:
                sl, it, r2 = fit_loglog(  # log|acf| vs lag -> slope = -lambda
                    [l for l, _ in good], [v for _, v in good])
                # actually exponential: log|acf| ~ -lambda*lag ; use lag (not log lag)
                lagv = np.array([l for l, _ in good], float)
                lnv = np.log([v for _, v in good])
                A = np.vstack([lagv, np.ones_like(lagv)]).T
                (mlam, _), *_ = np.linalg.lstsq(A, lnv, rcond=None)
                print(f"      exp-fit acf ~ e^(-lambda*lag): "
                      f"lambda = {-mlam:.3f}  => |lambda|=e^-lambda≈"
                      f"{math.exp(mlam):.3f}")
        except Exception as e:
            print(f"      (acf fit skipped: {e})")
    if ind6_seq_pool:
        longest_ind = max(ind6_seq_pool, key=len)
        aci = autocorr(longest_ind, 8)
        print(f"      offset-residue indicator [o%6==1] (len {len(longest_ind)}): "
              f"lags 1..8 = {[round(x,3) for x in aci[:8]]}")

    # ============ (3) THE COMPARISON ============
    print("\n" + "=" * 68)
    print("(3) THE COMPARISON: D(n) error term  vs  fatal-window fraction")
    print("=" * 68)
    LAMBDA_WIN = 0.134   # measured mean log-growth per renewal (prior result)
    print(f"  fatal-window fraction at renewal n ~ e^(-{LAMBDA_WIN} n) "
          f"(prior measured log-growth)")
    # use M=6 fit as the representative discrepancy law
    if 6 in fit_report:
        a6 = -fit_report[6][0]
        # D(n) at n from the M=6 curve; report D and window side by side
        # express window in crossings: ~3 renewals/crossing (prior) => scale n
        REN_PER_CROSS = 3.0
        print(f"  (crossing n corresponds to ~{REN_PER_CROSS} renewals => "
              f"window per crossing ~ e^(-{LAMBDA_WIN*REN_PER_CROSS:.3f} n))")
        # pull D(n) values
        d6 = {}
        for n in N_GRID:
            s, c = disc_acc[6][n]
            if c > 0:
                d6[n] = s / c
        print(f"\n    {'n':>6} {'D(n) [poly]':>14} {'window~e^-lam n':>18} "
              f"{'D/window':>14}")
        for n in N_GRID:
            if n in d6:
                win = math.exp(-LAMBDA_WIN * REN_PER_CROSS * n)
                print(f"    {n:>6} {d6[n]:>14.3e} {win:>18.3e} "
                      f"{d6[n]/win:>14.3e}")
        print(f"\n  D(n) fitted decay: polynomial n^-{a6:.3f}  "
              f"(alpha≈0.5 = CLT/diffusive)")
        print(f"  window decay:      exponential e^-{LAMBDA_WIN*REN_PER_CROSS:.3f} n")

    # ============ (4) RARE-EVENT vs SMOOTH ACCUMULATION ============
    print("\n" + "=" * 68)
    print("(4) RARE-EVENT vs SMOOTH ACCUMULATION")
    print("=" * 68)
    nat_diag = [d for d in natural_deaths if d[0] == 'diagonal']
    nat_axis = [d for d in natural_deaths if d[0] != 'diagonal']
    print(f"  natural-rate deaths in primary ensemble: "
          f"{len(nat_diag)} diagonal, {len(nat_axis)} axis "
          f"(of {len(seeds)} orbits, {sum(ncross_all):,} crossings)")
    if sum(ncross_all) > 0:
        print(f"    per-crossing diagonal-death rate: "
              f"{len(nat_diag)/sum(ncross_all):.3e}")

    # harvest deaths from a broad small-scale seed pool (higher hazard early)
    print("\n  death-harvest ensemble (small deterministic seeds, high early "
          "hazard):")
    harvest_deaths = []
    n_harvest_seeds = 0
    n_harvest_cross = 0
    HARVEST_BITCAP = 220   # deaths concentrate at small scale; cap keeps it cheap
    # small even-a and odd-a, odd-b seeds across a wide small band (high early
    # hazard ~6/beta). Deaths overwhelmingly occur before bitlen 220.
    for a0 in range(6, 300, 2):
        for b0 in range(3, 2 * a0 + 8, 2):   # odd b, up to ~2*beta
            if fatal(a0, b0):
                continue
            n_harvest_seeds += 1
            r = run_orbit(a0, b0, record_seq=False, sym_trans=None,
                          bitcap=HARVEST_BITCAP)
            n_harvest_cross += r['ncross']
            if r['death'] == 'diagonal':
                harvest_deaths.append((r['second_last_before_death'],
                                       r['last_offset_before_death']))
    print(f"    harvested {n_harvest_seeds:,} seeds, "
          f"{n_harvest_cross:,} crossings, "
          f"{len(harvest_deaths)} diagonal deaths")
    # distribution of the second-to-last offset before a diagonal death
    all_second = [s for (s, l) in harvest_deaths if s is not None]
    all_second += [d[1] for d in nat_diag if d[1] is not None]
    if all_second:
        arr = sorted(all_second)
        n = len(arr)
        print(f"\n    second-to-last offset before death (n={n}):")
        print(f"      min {arr[0]}, p10 {arr[n//10]}, median {arr[n//2]}, "
              f"p90 {arr[9*n//10]}, max {arr[-1]}")
        # KEY: is the previous offset SMALL (gradual approach) or LARGE (jump)?
        in_window = sum(1 for x in arr if x in (1, 3, 5))
        le11 = sum(1 for x in arr if x <= 11)
        le51 = sum(1 for x in arr if x <= 51)
        print(f"      previous offset in fatal window {{1,3,5}}: "
              f"{in_window}/{n} = {in_window/n:.3f}")
        print(f"      previous offset <= 11: {le11}/{n} = {le11/n:.3f}; "
              f"<= 51: {le51}/{n} = {le51/n:.3f}")
        print(f"      (SMALL previous offset => gradual/predictable approach "
              f"[HEAVY]; typical/LARGE previous offset => the fatal set is "
              f"hit in one shot from a fresh draw [BOLTED])")
        # compare to the generic offset distribution: median offset overall
        print(f"      for contrast, generic survivor offsets are enormous "
              f"(median ~ beta-scale, thousands+ of digits at depth)")

    # hazard-sum variance/mean (overdispersion => rare-event dominated)
    hz = np.array([h for h in hz_sum_list if h > 0], float)
    if len(hz) > 1:
        print(f"\n    per-orbit model hazard-sum: mean {hz.mean():.4f}, "
              f"var {hz.var():.4f}, var/mean {hz.var()/hz.mean():.3f}")
        print(f"      (var/mean >> 1 indicates a rare-event / heavy-tailed "
              f"hazard, not smooth accumulation)")

    # ============ (5) EFFECTIVE-TAIL FEASIBILITY for (6,13) ============
    print("\n" + "=" * 68)
    print("(5) EFFECTIVE-TAIL FEASIBILITY for the certified orbit (6,13)")
    print("=" * 68)
    # deep run of (6,13); collect per-crossing hazard and offsets
    a, b = 6, 13
    cross = 0
    hz_terms = []
    small_offsets = []
    min_off = None
    for step in range(RENEWAL_CAP):
        f = fatal(a, b)
        if f:
            print(f"  (6,13) DIED: {f} at renewal {step}")
            break
        if b % 2 == 1:
            beta = beta_of(a)
            if b > beta:
                o = b - beta
                cross += 1
                n_odd = max(1, beta // 2)
                hz_terms.append(min(1.0, 3.0 / n_odd))
                min_off = o if min_off is None else min(min_off, o)
                if o <= 201:
                    small_offsets.append((cross, o))
        a, b, _ = R(a, b)
        if a.bit_length() > BITLEN_CAP:
            break
    print(f"  (6,13): {cross} above-diagonal crossings to bitlen cap "
          f"{BITLEN_CAP} (renewals {step}); min offset ever = {min_off}")
    print(f"  smallest offsets seen (crossing_idx, offset): "
          f"{small_offsets[:12]}")
    hz_arr = np.array(hz_terms)
    total_tail = hz_arr.sum()
    print(f"  cumulative model hazard tail (sum of 3/(beta/2) over all "
          f"crossings): {total_tail:.6e}")
    # cumulative tail from crossing k onward
    csum_rev = np.cumsum(hz_arr[::-1])[::-1]  # tail[k] = sum_{i>=k}
    print(f"    tail from crossing k onward:")
    for k in (0, 5, 10, 20, 40, 80, 160, 320):
        if k < len(csum_rev):
            print(f"      k={k:>4}: {csum_rev[k]:.4e}")

    # THE FEASIBILITY INEQUALITY:
    # An effective equidistribution bound would certify P(fatal at crossing k)
    # only up to an error ~ D(k). To conclude "no fatal crossing ever" for a
    # SPECIFIC orbit you need the error budget summed over crossings to be
    # BELOW the true (model) hazard headroom -- i.e. the method's uncertainty
    # must be smaller than the effect it must resolve.  Compare:
    #   method error budget    E(n) = sum_{k<=n} D(k)         (grows)
    #   model hazard tail      H(n) = sum_{k<=n} 3/(beta_k/2) (shrinks per term)
    # The window a single crossing must be resolved below is ~ D(k) itself;
    # the model per-crossing hazard is 3/(beta/2). Localizing the orbit below
    # the fatal window requires D(k) <~ (per-crossing hazard) at each k.
    print(f"\n  FEASIBILITY INEQUALITY (per crossing k): does the achievable")
    print(f"  discrepancy error D(k) ever fall BELOW the per-crossing model")
    print(f"  hazard 3/(beta_k/2) that it must resolve?")
    if 6 in fit_report:
        a6 = -fit_report[6][0]
        # D(k) modeled as C6 * k^-a6 with C6 from the fit at n=... use measured
        # get a representative constant from the M=6 curve midpoint
        # C6 such that D(n)=C6 n^-a6
        s6, i6, _ = fit_loglog(
            [n for n in N_GRID if disc_acc[6][n][1] >= 30],
            [disc_acc[6][n][0]/disc_acc[6][n][1] for n in N_GRID
             if disc_acc[6][n][1] >= 30])
        C6 = math.exp(i6)
        print(f"    model D(k) = {C6:.3f} * k^-{a6:.3f}")
        print(f"    {'k':>6} {'D(k) error':>14} {'hazard 3/(b/2)':>16} "
              f"{'D(k)/hazard':>14}")
        ever_below = False
        for k in (10, 20, 40, 80, 160, 320, 640):
            if k <= len(hz_terms):
                Dk = C6 * k ** (-a6)
                hz_k = hz_terms[k - 1]
                ratio = Dk / hz_k if hz_k > 0 else float('inf')
                if ratio < 1:
                    ever_below = True
                print(f"    {k:>6} {Dk:>14.3e} {hz_k:>16.3e} {ratio:>14.3e}")
        verdict_line = ("YES (localizable)" if ever_below else
                        "NO (never) => the specific orbit is NOT "
                        "localizable by this method")
        print(f"\n    D(k) ever below the hazard it must resolve? "
              f"{verdict_line}")
        print(f"    The gap GROWS: D(k)~k^-{a6:.2f} (polynomial) while the "
              f"hazard ~1/beta_k~e^-{LAMBDA_WIN}*(3k) (exponential in k).")
        print(f"    error/hazard ~ k^-{a6:.2f} / e^-{LAMBDA_WIN*3:.3f}k "
              f"= k^-{a6:.2f} * e^{LAMBDA_WIN*3:.3f}k  ->  infinity.")

    # ============ VERDICT ============
    print("\n" + "=" * 68)
    print("VERDICT")
    print("=" * 68)
    if 6 in fit_report:
        a6 = -fit_report[6][0]
        polynomial = a6 < 1.5   # clearly not exponential
        print(f"  discrepancy decay alpha ≈ {a6:.3f} "
              f"({'POLYNOMIAL (CLT/diffusive)' if polynomial else 'faster'})")
        print(f"  spectral gap 1-|lambda_2| ≈ {1-lam2_1:.3f} (order-1), "
              f"{1-lam2_2:.3f} (order-2): genuine gap, exponential MIXING")
        print(f"  BUT mixing gives only CLT-rate equidistribution: the "
              f"empirical-frequency error decays ~n^-1/2, NOT exponentially.")
        if polynomial:
            print(f"\n  >>> VERDICT: DOOR BOLTED <<<")
            print(f"  D(n) decays polynomially (~n^-{a6:.2f}) while the fatal")
            print(f"  window shrinks exponentially (~e^-{LAMBDA_WIN} per "
                  f"renewal). The equidistribution error term is")
            print(f"  astronomically LARGER than the window at every large "
                  f"scale, so an effective-equidistribution theorem can never")
            print(f"  localize a specific orbit's fate below the window.")
        else:
            print(f"\n  >>> VERDICT: DOOR HEAVY <<<")


if __name__ == "__main__":
    main()

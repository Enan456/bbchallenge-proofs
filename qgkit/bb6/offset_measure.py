"""Ergodic-theory probes for the dossier-2/3 renewal map R.

The renewal map R (C-entries as the renewal section, verified in
docs/results/2026-08-26-renewal-map-analysis.md):

    T    (b even):  (a, b) -> (a + 6, b - 3)
    deep (b odd):   alpha, beta = (6, a-1) if a odd else (9, a-2)
        b < beta (branch C):  (alpha + 3(b-3), beta - (b-3))
        b > beta (branch F):  (alpha + 3 beta + 3, b - beta - 4)

Fatal set (death): b <= 2; or b == 4 (before a terminate); or a deep
fuse (branch F) with offset u = b - beta in {1, 3, 5}.  The offset is
u = b - beta at every odd-b renewal; u is always odd (b odd, beta even).

This module estimates the invariant behaviour of the offset process,
tests mixing of the branch-symbol sequence, probes for a supermartingale
that would bound the fatal hitting probability, and characterises the
specific dossier-2/3 orbit.  Everything here is rigorous numerics on the
exact integer map; none of it is a proof.  Use /usr/bin/python3.

Functions return plain dicts of numbers so callers can reuse them.
"""

import math
import random
import statistics
from collections import Counter, defaultdict

# ----------------------------------------------------------------------
# The exact map, the fatal set, the offset
# ----------------------------------------------------------------------

SYMBOL = {'T': 'T', 'dC': 'c', 'DC': 'C', 'dF': 'f', 'DF': 'F'}


def R(a, b):
    """One renewal step. Returns (a', b', branch symbol)."""
    if b % 2 == 0:
        return a + 6, b - 3, 'T'
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    sym = 'd' if a % 2 == 1 else 'D'
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3), sym + 'C'
    return alpha + 3 * beta + 3, b - beta - 4, sym + 'F'


def beta_of(a):
    """The companion counter beta at an odd-b renewal (always even)."""
    return (a - 1) if a % 2 == 1 else (a - 2)


def offset(a, b):
    """u = b - beta at an odd-b renewal, else None. Always odd when defined."""
    if b % 2 == 0:
        return None
    return b - beta_of(a)


def fatal(a, b):
    """Reason string if (a, b) is fatal, else None."""
    if b <= 2:
        return 'b<=2'
    if b % 2 == 0:
        return 'T->1' if b == 4 else None
    beta = beta_of(a)
    if b > beta and b - beta in (1, 3, 5):
        return 'diagonal'
    return None


# ----------------------------------------------------------------------
# Experiment 1: the offset invariant measure and the fatal-band measure
# ----------------------------------------------------------------------

def offset_low_histogram(n_orbits=200_000, seed_hi=2000, horizon=400,
                         window=41, rng_seed=1):
    """Ensemble low-end fuse-offset histogram, INCLUDING fatal offsets.

    Offsets are recorded at entry (before the fatal check) over an
    ensemble of independent orbits, so fatal offsets in {1,3,5} appear
    and the count is unbiased (no survivorship bias).  Confirms the
    fatal band carries exactly the local-uniform measure of its three
    odd values.
    """
    rng = random.Random(rng_seed)
    hist = Counter()
    deaths = Counter()
    total_fuse = 0
    odd_ok = True
    for _ in range(n_orbits):
        a = rng.randrange(4, seed_hi)
        b = rng.randrange(4, seed_hi)
        for _ in range(horizon):
            if b % 2 == 1:
                u = b - beta_of(a)
                if u % 2 != 1:
                    odd_ok = False
                if u > 0:
                    total_fuse += 1
                    if u <= window:
                        hist[u] += 1
            f = fatal(a, b)
            if f:
                deaths[f] += 1
                break
            a, b, _ = R(a, b)
    return {'hist': dict(hist), 'deaths': dict(deaths),
            'total_fuse': total_fuse, 'u_always_odd': odd_ok,
            'fatal_band_events': hist.get(1, 0) + hist.get(3, 0) + hist.get(5, 0)}


def hazard_scaling(scales=(8, 12, 16, 20), n_per=30_000, window_hi=99,
                   rng_seed=5):
    """Per-fuse fatal-band hazard as a function of size.

    For seeds at scale ~2^n, record only the FIRST fuse of each orbit so
    beta is controlled at the seed scale.  Estimates c = P(u in a small
    odd window) * beta / (#odd slots); c ~ const means P(u = specific
    odd value) ~ c/beta, hence fatal-band hazard P(u in {1,3,5}) ~ 3c/beta.
    """
    rng = random.Random(rng_seed)
    n_slots = len(range(7, window_hi + 1, 2))
    rows = []
    for n in scales:
        lo, hi = 2 ** n, 2 ** (n + 1)
        nf = small = 0
        betas = []
        while nf < n_per:
            a = rng.randrange(lo, hi)
            b = rng.randrange(lo, hi)
            for _ in range(60):
                if b % 2 == 1:
                    u = b - beta_of(a)
                    if u > 0:
                        nf += 1
                        betas.append(beta_of(a))
                        if 7 <= u <= window_hi:
                            small += 1
                        break
                a, b, _ = R(a, b)
        mb = statistics.mean(betas)
        P = small / nf
        c = P * mb / n_slots
        rows.append({'n': n, 'mean_beta': mb, 'P_window': P, 'c': c,
                     'hazard_pred_per_fuse': 3 * c / mb})
    return rows


def normalized_offset(n=100_000, rng_seed=9, target_scale=2 ** 40):
    """Distribution of the normalized fuse offset u / beta in (0, .).

    The raw offset u is transient (scales with beta); u/beta is the
    scale-free object.  Returns quantiles of u/beta over first fuses at
    a fixed large scale.
    """
    rng = random.Random(rng_seed)
    vals = []
    while len(vals) < n:
        a = rng.randrange(target_scale, 2 * target_scale)
        b = rng.randrange(target_scale, 2 * target_scale)
        for _ in range(60):
            if b % 2 == 1:
                bb = beta_of(a)
                u = b - bb
                if u > 0:
                    vals.append(u / bb)
                    break
            a, b, _ = R(a, b)
    vals.sort()
    q = lambda p: vals[int(p * (len(vals) - 1))]
    return {'n': len(vals), 'mean': statistics.mean(vals),
            'quantiles': {p: round(q(p), 4)
                          for p in (0.05, 0.25, 0.5, 0.75, 0.95)},
            'max': round(vals[-1], 4)}


# ----------------------------------------------------------------------
# Experiment 2: mixing of the branch-symbol sequence
# ----------------------------------------------------------------------

def _block_entropy(S, k):
    c = Counter(S[i:i + k] for i in range(len(S) - k + 1))
    m = sum(c.values())
    return -sum((v / m) * math.log(v / m) for v in c.values())


def mixing_analysis(seed=(6, 13), n=200_000, max_block=12, acf_lags=10):
    """Stationary law, entropy rate, factor complexity, autocorrelation.

    A finite entropy-rate plateau plus fast autocorrelation decay is the
    signature of a finitely-mixing process (Borel-Cantelli reachable in
    principle).  Long-range structure would show as a non-plateauing
    conditional entropy or a slowly decaying autocorrelation.
    """
    x, y = seed
    sym = []
    dlog = []
    for _ in range(n):
        s0 = x + y
        x, y, s = R(x, y)
        sym.append(SYMBOL[s])
        dlog.append(math.log((x + y) / s0))
    S = ''.join(sym)
    stationary = {k: v / len(S) for k, v in Counter(S).items()}
    H = [0.0] + [_block_entropy(S, k) for k in range(1, max_block + 1)]
    hcond = [H[k] - H[k - 1] for k in range(1, max_block + 1)]
    pcx = [len(set(S[i:i + k] for i in range(len(S) - k)))
           for k in range(1, 15)]
    mean = statistics.mean(dlog)
    var = statistics.pvariance(dlog)
    acf = []
    for lag in range(1, acf_lags + 1):
        cov = sum((dlog[i] - mean) * (dlog[i + lag] - mean)
                  for i in range(len(dlog) - lag)) / (len(dlog) - lag)
        acf.append(cov / var)
    # KL of empirical 3-gram vs order-1 Markov prediction
    tr = defaultdict(Counter)
    for i in range(len(S) - 1):
        tr[S[i]][S[i + 1]] += 1
    P = {a: {b: tr[a][b] / sum(tr[a].values()) for b in tr[a]} for a in tr}
    p1 = Counter(S)
    pi = {a: p1[a] / len(S) for a in p1}
    c3 = Counter(S[i:i + 3] for i in range(len(S) - 3))
    m3 = sum(c3.values())
    kl1 = 0.0
    for w, cnt in c3.items():
        pe = cnt / m3
        pm = pi[w[0]] * P[w[0]].get(w[1], 1e-12) * P[w[1]].get(w[2], 1e-12)
        kl1 += pe * math.log(pe / pm)
    return {'stationary': {k: round(v, 4) for k, v in stationary.items()},
            'cond_entropy': [round(h, 4) for h in hcond],
            'entropy_rate_est': round(hcond[-1], 4),
            'topological_log_1.6': round(math.log(1.6), 4),
            'factor_complexity': pcx,
            'dlog_mean': round(mean, 4), 'dlog_std': round(math.sqrt(var), 4),
            'acf_dlog': [round(v, 4) for v in acf],
            'kl_vs_markov1_3gram': round(kl1, 5)}


# ----------------------------------------------------------------------
# Experiment 3: martingale / drift probe
# ----------------------------------------------------------------------

def size_increment_lemma(n=2_000_000, hi=10 ** 6, rng_seed=7):
    """Check that size = a+b strictly increases from every non-fatal state.

    Reports the minimum size increment observed per branch.  Analytically
    T: +3; C: b-1 (a odd) or b+1 (a even); F: a+3 (a odd) or a+4 (a even);
    all strictly positive off the fatal set.  This makes 1/size a pathwise
    supermartingale, but the growth is only ADDITIVE (>= 2), which gives a
    divergent hazard sum -- not enough on its own.
    """
    rng = random.Random(rng_seed)
    mins = {'T': None, 'C': None, 'F': None}
    for _ in range(n):
        a = rng.randrange(6, hi)
        b = rng.randrange(6, hi)
        if fatal(a, b):
            continue
        s0 = a + b
        a2, b2, s = R(a, b)
        inc = (a2 + b2) - s0
        k = s[-1]
        if mins[k] is None or inc < mins[k]:
            mins[k] = inc
    return mins


def drift_probe(seed=(6, 13), n=300_000, thetas=(0.25, 0.5, 1.0, 1.5, 2.0)):
    """Multiplicative-drift / supermartingale test on the true orbit.

    Estimates E[G^{-theta}] with G = size'/size, size = a+b.  If < 1 for
    some theta, then size^{-theta} has the supermartingale drift needed
    for a geometric hazard bound.  Combined with hazard ~ 6/size this
    yields P(ever fatal) <~ 6/(size_0 (1 - e^{-mean dlog})).
    """
    x, y = seed
    dlog = []
    for _ in range(n):
        s0 = x + y
        x, y, _ = R(x, y)
        dlog.append(math.log((x + y) / s0))
    mean = statistics.mean(dlog)

    def mean_exp(vals):
        m = max(vals)
        return math.exp(m) * sum(math.exp(v - m) for v in vals) / len(vals)

    egt = {}
    for th in thetas:
        egt[th] = mean_exp([-th * d for d in dlog])
    geom_ratio = math.exp(-mean)
    return {'dlog_mean': round(mean, 5),
            'dlog_std': round(statistics.stdev(dlog), 5),
            'frac_size_shrinks': sum(1 for d in dlog if d < 0) / len(dlog),
            'E_Gneg_theta': {th: round(v, 5) for th, v in egt.items()},
            'geom_ratio_e_minus_meandlog': round(geom_ratio, 5),
            'hitting_bound_const_over_size0':
                round(6 / (1 - geom_ratio), 2)}


def barrier_probe(seed=(6, 13), n=200_000, lags=8):
    """Why no barrier supermartingale exists: offsets are independent draws.

    A barrier supermartingale would require the fatal set (small offset)
    to be APPROACHED gradually, so a nonneg supermartingale could be forced
    across a level.  Instead the fatal set is hit in one shot: at each fuse
    the offset is a fresh draw from the (size-dependent) offset law with a
    finite density near zero, and consecutive fuse offsets are essentially
    independent.  This measures the autocorrelation of log(u/beta) over
    fuse events; ~0 at all lags means there is nothing to cross a barrier.
    """
    x, y = seed
    seq = []
    for _ in range(n):
        if y % 2 == 1:
            bb = beta_of(x)
            u = y - bb
            if u > 0:
                seq.append(math.log(u / bb))
        x, y, _ = R(x, y)
    m = statistics.mean(seq)
    v = statistics.pvariance(seq)
    acf = []
    for lag in range(1, lags + 1):
        cov = sum((seq[i] - m) * (seq[i + lag] - m)
                  for i in range(len(seq) - lag)) / (len(seq) - lag)
        acf.append(round(cov / v, 4))
    return {'n_fuse': len(seq), 'mean_log_u_over_beta': round(m, 4),
            'acf_log_offset': acf}


# ----------------------------------------------------------------------
# Experiment 4: the specific dossier-2/3 orbit
# ----------------------------------------------------------------------

def specific_orbit(seed=(6, 13), n=1_000_000, windows=(7, 9, 11, 15, 51)):
    """Margin distribution and genericity for the actual orbit.

    Margin above the fatal band = u - 5 for a fuse with offset u.  Returns
    the smallest offset seen, how often the orbit comes within each window,
    and its mean log-growth (compare to the ensemble 0.134 for genericity).
    """
    x, y = seed
    min_u = None
    n_fuse = 0
    within = {w: 0 for w in windows}
    dlogsum = 0.0
    for i in range(n):
        f = fatal(x, y)
        if f:
            return {'status': 'FATAL', 'reason': f, 'renewal': i}
        if y % 2 == 1:
            u = y - beta_of(x)
            if u > 0:
                n_fuse += 1
                if min_u is None or u < min_u:
                    min_u = u
                for w in windows:
                    if u <= w:
                        within[w] += 1
        s0 = x + y
        x, y, _ = R(x, y)
        dlogsum += math.log((x + y) / s0)
    return {'status': 'ALIVE', 'renewals': n, 'final_bits': x.bit_length(),
            'n_fuse': n_fuse, 'min_offset': min_u,
            'min_margin_above_band': (min_u - 5) if min_u else None,
            'within_window': within, 'mean_dlog': round(dlogsum / n, 5)}


if __name__ == '__main__':
    import json
    print('=== offset low histogram (fatal band measure) ===')
    print(json.dumps(offset_low_histogram(n_orbits=50_000), indent=0))
    print('\n=== hazard scaling (per-fuse fatal hazard ~ 6/size) ===')
    for r in hazard_scaling():
        print(r)
    print('\n=== mixing ===')
    print(json.dumps(mixing_analysis(n=100_000), indent=0))
    print('\n=== size-increment lemma ===')
    print(size_increment_lemma(n=500_000))
    print('\n=== drift probe ===')
    print(json.dumps(drift_probe(n=100_000), indent=0))
    print('\n=== barrier probe (offset autocorrelation) ===')
    print(barrier_probe(n=100_000))
    print('\n=== specific orbit (6,13) ===')
    print(json.dumps(specific_orbit(n=200_000), indent=0))

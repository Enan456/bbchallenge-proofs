"""Foster-Lyapunov drift and tail-hazard scaffold for the dossier-2/3 renewal map R.

This is a NUMERICAL SCAFFOLD, not a proof. Every routine reports a horizon.
It measures one-step drift of candidate Lyapunov functions, the per-renewal
tail hazard h(s), and the tail-sum along the true orbit. See the companion
write-up docs/results/2026-09-04-invariant-measure-drift.md for the honest
gap-to-rigor discussion.

The renewal map (verified against metaStep; see renewal_analysis3.py):

    b even            :  (a, b) -> (a + 6,           b - 3)              [T]
    b odd, a odd      :  (alpha, beta) = (6, a - 1)
    b odd, a even     :  (alpha, beta) = (9, a - 2)
      b < beta        :  (a, b) -> (alpha + 3(b-3),  beta - (b-3))       [C]
      b > beta        :  (a, b) -> (alpha + 3 beta+3, b - beta - 4)      [F, fuse]

Fatal set: b <= 2; or b == 4; or a deep-fuse with b - beta in {1, 3, 5}.

Run:  /usr/bin/python3 qgkit/bb6/lyapunov_search.py
"""
import math
import random
import statistics
from collections import Counter, defaultdict

SEED = (6, 13)  # the dossier-2/3 orbit seed


def R(a, b):
    """One renewal. Returns (a', b', symbol)."""
    if b % 2 == 0:
        return a + 6, b - 3, 'T'
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    sym = 'd' if a % 2 == 1 else 'D'
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3), sym + 'C'
    return alpha + 3 * beta + 3, b - beta - 4, sym + 'F'


def fatal(a, b):
    """Death cause at (a, b), or None if alive."""
    if b <= 2:
        return 'b<=2'
    if b % 2 == 0:
        return 'T->1' if b == 4 else None
    beta = (a - 1) if a % 2 == 1 else (a - 2)
    if b > beta and b - beta in (1, 3, 5):
        return 'diagonal'
    return None


def safe_log(n):
    """math.log for arbitrarily large ints (float conversion would overflow)."""
    if n <= 0:
        raise ValueError
    k = n.bit_length()
    if k <= 900:
        return math.log(n)
    shift = k - 800
    return shift * math.log(2) + math.log(n >> shift)


def beta_of(a):
    return (a - 1) if a % 2 == 1 else (a - 2)


def is_fuse(a, b):
    """Deep-fuse renewal: b odd and b > beta."""
    return b % 2 == 1 and b > beta_of(a)


def offset(a, b):
    """Fuse offset u = b - beta (meaningful only on a fuse)."""
    return b - beta_of(a)


# ---------------------------------------------------------------------------
# 0. Growth rate on the true orbit (exact bigint arithmetic).
# ---------------------------------------------------------------------------
def growth_rate(nren=200_000):
    x, y = SEED
    lg = []
    for _ in range(nren):
        if fatal(x, y):
            return None
        s0 = x + y
        x, y, _ = R(x, y)
        lg.append(math.log((x + y) / s0))
    return {
        'renewals': len(lg),
        'final_bits': x.bit_length(),
        'mean': statistics.mean(lg),
        'std': statistics.stdev(lg),
        'min': min(lg),
        'max': max(lg),
    }


# ---------------------------------------------------------------------------
# 1. Foster-Lyapunov drift search.
# ---------------------------------------------------------------------------
# Candidate Lyapunov functions and the one-step drift metrics we report.
# All metrics are computed through EXACT ratios so they stay overflow-safe at
# astronomical size (Python true division of bigints yields a correct float).
#   rho          = s'/s                 (per-renewal size ratio)
#   rho-1        = drift of size, normalized by size
#   log(rho)     = drift of V = log(size)
#   s*D(1/s)     = 1/rho - 1  = size * drift of V = 1/size   (Foster transience)
#   D(u/s)       = drift of the normalized fuse offset u/(a+b) in [-1,1]
METRICS = ('rho-1', 'log_rho', 's*D(1/s)', 'D(u/s)')


def _step_metrics(a, b, na, nb):
    s = a + b
    ns = na + nb
    rho = ns / s  # exact-ratio float, overflow-safe
    m = {'rho-1': rho - 1.0,
         'log_rho': math.log(rho),
         's*D(1/s)': (1.0 / rho) - 1.0}
    u = offset(a, b)
    nu = offset(na, nb)
    uf = (u / s) if u > 0 else 0.0
    nuf = (nu / ns) if nu > 0 else 0.0
    m['D(u/s)'] = nuf - uf
    return m


def drift_on_orbit(nren=200_000):
    """Mean one-step drift metrics along the true orbit, by size band (bits)."""
    x, y = SEED
    acc = {name: defaultdict(list) for name in METRICS}
    for _ in range(nren):
        if fatal(x, y):
            break
        nx, ny, _ = R(x, y)
        bits = (x + y).bit_length()
        m = _step_metrics(x, y, nx, ny)
        for name in METRICS:
            acc[name][bits].append(m[name])
        x, y = nx, ny
    return acc


def drift_on_ensemble(sizes, nsamp=4000):
    """Mean one-step drift metrics over a visited-state ensemble at each target
    size band [s, 2s). The ensemble is the typical measure the process explores:
    states are harvested by running R from many random seeds and binning."""
    bins = {s: [] for s in sizes}
    band = {s: (s, 2 * s) for s in sizes}
    rng = random.Random(20260904)
    tries = 0
    need = nsamp
    while tries < 200000 and any(len(v) < need for v in bins.values()):
        tries += 1
        cap = rng.choice([3_000, 60_000, 200_000, 4_000_000])
        a = rng.randrange(6, cap)
        b = rng.randrange(3, cap)
        x, y = a, b
        for _ in range(400):
            if fatal(x, y):
                break
            sz = x + y
            for s in sizes:
                lo, hi = band[s]
                if lo <= sz < hi and len(bins[s]) < need:
                    bins[s].append((x, y))
            x, y, _ = R(x, y)
    out = {}
    for s in sizes:
        acc = {name: [] for name in METRICS}
        for (a, b) in bins[s]:
            if fatal(a, b):
                continue
            nx, ny, _ = R(a, b)
            m = _step_metrics(a, b, nx, ny)
            for name in METRICS:
                acc[name].append(m[name])
        out[s] = {name: (statistics.mean(vs) if vs else float('nan'),
                         len(vs)) for name, vs in acc.items()}
        out[s]['_n'] = len(bins[s])
    return out


# ---------------------------------------------------------------------------
# 2. Tail hazard h(s).
# ---------------------------------------------------------------------------
def hazard_exact(s):
    """EXACT per-renewal hazard at scale s by full enumeration of every state
    (a, b), a >= 5, b >= 3, with a + b in [s, 2s). Returns (h, C=h*s, counts).
    h = fraction of alive states whose NEXT renewal lands in the fatal set."""
    alive = 0
    dies_next = 0
    fuse_alive = 0
    fuse_dies = 0
    for a in range(5, 2 * s):
        for b in range(3, 2 * s - a + 1):
            sz = a + b
            if sz < s or sz >= 2 * s:
                continue
            if fatal(a, b):
                continue
            alive += 1
            nx, ny, _ = R(a, b)
            f = is_fuse(a, b)
            if f:
                fuse_alive += 1
            if fatal(nx, ny):
                dies_next += 1
                if f:
                    fuse_dies += 1
    h = dies_next / alive if alive else 0.0
    return {
        'h': h, 'C': h * s, 'alive': alive, 'dies_next': dies_next,
        'fuse_alive': fuse_alive, 'fuse_dies': fuse_dies,
        'fuse_frac': fuse_alive / alive if alive else 0.0,
        'h_given_fuse': fuse_dies / fuse_alive if fuse_alive else 0.0,
    }


def hazard_sampled(s, nsamp=2_000_000, rng=None):
    """Sampled per-renewal hazard at scale s (for s beyond exact reach)."""
    rng = rng or random.Random(12345 + s)
    alive = 0
    dies_next = 0
    for _ in range(nsamp):
        # uniform (a, b) with a + b in [s, 2s), a >= 5, b >= 3
        sz = rng.randrange(s, 2 * s)
        a = rng.randrange(5, sz - 2)
        b = sz - a
        if b < 3:
            continue
        if fatal(a, b):
            continue
        alive += 1
        nx, ny, _ = R(a, b)
        if fatal(nx, ny):
            dies_next += 1
    h = dies_next / alive if alive else 0.0
    return {'h': h, 'C': h * s, 'alive': alive, 'dies_next': dies_next}


# ---------------------------------------------------------------------------
# 3. Tail-sum along the true orbit under the measured hazard law.
# ---------------------------------------------------------------------------
def tail_sum(C, r=0.134, s_start=None, nren=200_000):
    """Given hazard model h(s) <= C/s and multiplicative growth s_k ~ s0 e^{r k},
    the tail sum from renewal K is sum_k C/s_k <= (C/s_K) * 1/(1 - e^{-r}).
    Also compute the EXACT sum of C/s_k along the true orbit's actual sizes."""
    x, y = SEED
    sizes = []
    for _ in range(nren):
        if fatal(x, y):
            break
        sizes.append(x + y)
        x, y, _ = R(x, y)
    logC = math.log(C)
    exact_tail = {}
    for K in (0, 10, 50, 100, 1000):
        if K < len(sizes):
            exact_tail[K] = sum(math.exp(logC - safe_log(s)) for s in sizes[K:])
    geom_bound = {}
    for K in (0, 10, 50, 100, 1000):
        if K < len(sizes):
            geom_bound[K] = (math.exp(logC - safe_log(sizes[K]))
                             / (1 - math.exp(-r)))
    return {'exact_tail': exact_tail, 'geom_bound': geom_bound,
            'nren': len(sizes), 's0': sizes[0] if sizes else None}


# ---------------------------------------------------------------------------
def main():
    print('=' * 70)
    print('FOSTER-LYAPUNOV / TAIL-HAZARD SCAFFOLD  (numerics, NOT a proof)')
    print('=' * 70)

    print('\n[0] GROWTH RATE on true orbit (horizon 200k renewals)')
    g = growth_rate(200_000)
    print(f"    renewals={g['renewals']}  final_bits={g['final_bits']}")
    print(f"    log-growth/renewal: mean={g['mean']:.5f} std={g['std']:.5f} "
          f"min={g['min']:.4f} max={g['max']:.4f}")
    r = g['mean']

    print('\n[1a] DRIFT metrics along true orbit, by size band (bits)')
    acc = drift_on_orbit(200_000)
    bands = sorted({b for name in acc for b in acc[name]})
    show_bits = [b for b in bands if b in (16, 64, 256, 1024, 4096, 16384)]
    if not show_bits:
        show_bits = bands[::max(1, len(bands)//6)]
    hdr = 'metric'.ljust(12) + ''.join(f'{b}b'.rjust(13) for b in show_bits)
    print('    ' + hdr)
    for name in METRICS:
        row = name.ljust(12)
        for b in show_bits:
            vs = acc[name].get(b, [])
            row += (f'{statistics.mean(vs):+.4e}'.rjust(13) if vs
                    else 'na'.rjust(13))
        print('    ' + row)
    print('    sign guide: log_rho>0 => size escapes (transient);')
    print('    s*D(1/s)<0 => V=1/size is a supermartingale (Foster transience)')

    print('\n[1b] DRIFT over visited-state ensemble at fixed size bands')
    ens = drift_on_ensemble([1000, 10_000, 100_000, 1_000_000], nsamp=3000)
    for s in [1000, 10_000, 100_000, 1_000_000]:
        print(f'    size band [{s}, {2*s}):  n_states={ens[s]["_n"]}')
        for name in METRICS:
            m, n = ens[s][name]
            print(f'        {name.ljust(10)} mean drift = {m:+.4e}  (n={n})')

    print('\n[2a] EXACT hazard by full enumeration, size bands [s,2s)')
    print('     h = frac of alive states whose NEXT renewal is fatal; C = h*s')
    Cs_exact = []
    for s in (64, 128, 256, 512, 1024, 2048, 4096):
        d = hazard_exact(s)
        Cs_exact.append(d['C'])
        print(f"     s={s:5d}  alive={d['alive']:9d}  dies={d['dies_next']:6d}"
              f"  h={d['h']:.3e}  C=h*s={d['C']:.3f}"
              f"  fuse_frac={d['fuse_frac']:.3f}"
              f"  h|fuse={d['h_given_fuse']:.3e}")
    Cmax = max(Cs_exact)  # empirical envelope from the reliable exact scan
    print(f'     exact C is monotone decreasing {Cs_exact[0]:.3f} -> '
          f'{Cs_exact[-1]:.3f}; envelope C_emp = {Cmax:.3f} (sup over s>=64)')

    print('\n[2b] SAMPLED hazard (consistency check at larger s; Poisson noisy)')
    for s, ns in ((10_000, 3_000_000), (100_000, 12_000_000)):
        d = hazard_sampled(s, ns)
        err = d['C'] / max(d['dies_next'], 1) ** 0.5
        print(f"     s={s:9d}  samples={ns:>10d}  dies={d['dies_next']:5d}"
              f"  C=h*s={d['C']:.3f} +/- {err:.3f}")

    print(f'\n     => empirical hazard bound  h(s) <= C_emp/s  with C_emp ~ '
          f'{Cmax:.2f}  (s >= 64, all horizons tested)')

    print('\n[3] TAIL-SUM along true orbit under h(s) <= C/s, r = mean growth')
    ts = tail_sum(Cmax, r=r, nren=200_000)
    print(f"     s0={ts['s0']}  orbit horizon={ts['nren']} renewals")
    print('     from renewal K:   exact sum C/s_k        geometric bound')
    for K in (0, 10, 50, 100, 1000):
        if K in ts['exact_tail']:
            print(f"       K={K:5d}   {ts['exact_tail'][K]:.6e}"
                  f"        {ts['geom_bound'][K]:.6e}")
    print('     tail converges (geometric); residual hazard from renewal K')
    print('     is bounded by (C/s_K)/(1-e^{-r}); with C~%.0f, 1/(1-e^{-r})'
          '~%.2f' % (Cmax, 1 / (1 - math.exp(-r))))


if __name__ == '__main__':
    main()

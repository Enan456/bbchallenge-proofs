"""Almost-all-seeds analysis for Antihydra's certified abstract map.

Seed space: triples (a, m, c) under the exact mirror of
AntihydraRawTM.astep (hydra / drop / merge; dying = drop with a < 2,
or m = 0).  Volley-compressed iteration (one volley = the hydra run
down to m in {1, 2} plus the boundary rule).

1. Exact death-density in growing boxes [X, 2X)^3 and [1, X]^3.
2. The a-marginal: dying fraction as a function of the counter alone,
   against the gambler's-ruin prediction rho^a with
   rho = (sqrt(5) - 1) / 2 (steps -1 / +2 with fair parities).
3. Death mechanism: death-volley distribution (early game only?).
4. Drift: merge fraction, E[delta a] per volley, log-growth of m.
5. The certified seed (2, 7, 2): model hazard, actual a-trajectory,
   residual Borel-Cantelli tail.
"""
import random
from math import sqrt, log

RHO = (sqrt(5) - 1) / 2          # ruin root of r^3 - 2r + 1
A_SAFE = 60                      # residual model hazard rho^60 ~ 3e-13
VMAX = 4000


def volley(a, m, c):
    """One volley of the certified map: hydra to the boundary, then
    drop or merge.  Returns None on death (exact astep dying set)."""
    if m == 0:
        return None
    if m >= 3:
        k = (m - 2) // 2 if m % 2 == 0 else (m - 1) // 2
        c += 3 * k
        m = 2 if m % 2 == 0 else 1
    if m == 2:
        if a < 2:
            return None
        return (a - 1, c + 3, 2)
    return (a + 2, c + 2, 2)


def run_seed(a, m, c):
    """('died', v) / ('survived', v) with the a >= A_SAFE cap."""
    for v in range(VMAX):
        if a >= A_SAFE:
            return ('survived', v)
        s = volley(a, m, c)
        if s is None:
            return ('died', v)
        a, m, c = s
    return ('survived', VMAX)


if __name__ == '__main__':
    print("== exact death-density in seed boxes")
    print(f"{'box':>16} {'seeds':>7} {'died':>6} {'p_die':>8} "
          f"{'max death volley':>17}")
    for X in (2, 4, 8, 16, 32):
        died, worst = 0, -1
        n = 0
        for a in range(X, 2 * X):
            for m in range(X, 2 * X):
                for c in range(X, 2 * X):
                    n += 1
                    res, v = run_seed(a, m, c)
                    if res == 'died':
                        died += 1
                        worst = max(worst, v)
        print(f"  [{X:>3},{2 * X:>3})^3 {n:>7} {died:>6} "
              f"{died / n:>8.4f} {worst:>17}")
    for X in (8, 16, 32):
        died, worst = 0, -1
        n = 0
        for a in range(1, X + 1):
            for m in range(1, X + 1):
                for c in range(1, X + 1):
                    n += 1
                    res, v = run_seed(a, m, c)
                    if res == 'died':
                        died += 1
                        worst = max(worst, v)
        print(f"  [1,{X:>3}]^3   {n:>7} {died:>6} {died / n:>8.4f} "
              f"{worst:>17}")

    print("\n== a-marginal: dying fraction vs counter, (m,c) in [1,48]^2")
    print(f"{'a':>3} {'p_die':>8} {'ratio':>7}   [ruin model rho = "
          f"{RHO:.4f}, prediction rho^a]")
    prev = None
    for a in range(1, 25):
        died = sum(1 for m in range(1, 49) for c in range(1, 49)
                   if run_seed(a, m, c)[0] == 'died')
        p = died / (48 * 48)
        ratio = f"{p / prev:>7.3f}" if prev and p else f"{'-':>7}"
        print(f"{a:>3} {p:>8.4f} {ratio}   rho^a = {RHO ** a:.4f}")
        prev = p

    print("\n== death mechanism: death-volley distribution "
          "(10^5 random seeds in [1,64]^3)")
    rng = random.Random(8)
    vols = []
    for _ in range(100_000):
        a, m, c = (rng.randrange(1, 65) for _ in range(3))
        res, v = run_seed(a, m, c)
        if res == 'died':
            vols.append(v)
    vols.sort()
    q = lambda p: vols[int(p * (len(vols) - 1))]
    print(f"  deaths: {len(vols)}; death volley quantiles "
          f"10/50/90/99/100%: {q(.1)}/{q(.5)}/{q(.9)}/{q(.99)}/"
          f"{vols[-1]}")

    print("\n== drift along surviving orbits (500 random seeds, "
          "300 volleys each)")
    nm, nd, dv = 0, 0, 0
    lg = 0.0
    for _ in range(500):
        a, m, c = (rng.randrange(1, 65) for _ in range(3))
        for _v in range(300):
            s = volley(a, m, c)
            if s is None:
                break
            a2, m2, c2 = s
            if a2 > a:
                nm += 1
            else:
                nd += 1
            dv += a2 - a
            lg += log(m2 / m) if m else 0
            a, m, c = a2, m2, c2
    tot = nm + nd
    print(f"  volleys: {tot}; merge fraction {nm / tot:.4f}; "
          f"E[delta a] per volley {dv / tot:+.4f}; mean log-growth of "
          f"m per volley {lg / tot:.4f} (log 3/2 = {log(1.5):.4f})")

    print("\n== the certified seed (2, 7, 2)")
    a, m, c = 2, 7, 2
    traj = [(0, a)]
    resid_from = []
    for v in range(1, 301):
        s = volley(a, m, c)
        assert s is not None, "certified orbit died?!"
        a, m, c = s
        traj.append((v, a))
    a_at = dict(traj)
    print(f"  model death probability from a = 2: rho^2 = "
          f"{RHO ** 2:.4f}  (38%: a hazardous early game)")
    print(f"  counter trajectory a(v), v = 0..12: "
          f"{[a_at[v] for v in range(13)]}")
    drops = [(v, av) for (v, av), (v2, av2) in zip(traj, traj[1:])
             if av2 < av]
    min_drop = min(av for v, av in drops)
    print(f"  drops in 300 volleys: {len(drops)}; minimum counter "
          f"at a drop: {min_drop} (death needs a <= 1)")
    resid = sum(RHO ** av for v, av in traj[30:])
    print(f"  a(30) = {a_at[30]}, a(300) = {a_at[300]}; "
          f"Borel-Cantelli residual sum_(v>=30) rho^a(v) = {resid:.3e}")

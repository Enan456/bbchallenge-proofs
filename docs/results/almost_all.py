"""Almost-all-seeds analysis for the renewal map R.

1. Death-density sweep: fraction of seeds in [2^j, 2^{j+1})^2 whose
   orbit ever dies, vs j. Borel-Cantelli predicts ~ C * 2^-j.
2. Hazard measurement: at each deep-fuse, the offset b - beta lands on
   an odd value in (0, size]; fatal iff in {1,3,5}. Equidistribution
   predicts per-fuse hazard ~ 3 / (#odd offsets) ~ 6/size.
3. Offset-uniformity check: distribution of small offsets vs uniform.
"""
import random

random.seed(42)


def R(a, b):
    if b % 2 == 0:
        return a + 6, b - 3, 'T', None
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3), 'C', None
    return alpha + 3 * beta + 3, b - beta - 4, 'F', (b - beta, beta)


def fatal(a, b):
    if b <= 2:
        return True
    if b % 2 == 0 and b == 4:
        return True
    beta = (a - 1) if a % 2 == 1 else (a - 2)
    return b % 2 == 1 and b > beta and b - beta in (1, 3, 5)


SIZE_CAP = 1 << 44          # survival threshold: residual hazard
                            # sum < 6/2^44 / (1 - e^-0.134) ~ 3e-12
KMAX = 20000

def run_seed(a, b):
    """Return ('died', k) or ('survived', k) with size-cap justification."""
    offsets = []
    for k in range(KMAX):
        if fatal(a, b):
            return 'died', k, offsets
        if a + b > SIZE_CAP:
            return 'survived', k, offsets
        a2, b2, s, fuse = R(a, b)
        if fuse:
            offsets.append(fuse)
        a, b = a2, b2
    return 'survived', KMAX, offsets


print("== death-density sweep over seed boxes [2^j, 2^{j+1})^2")
print(f"{'j':>3} {'samples':>8} {'died':>6} {'p_die':>9} {'p*2^j':>8}")
all_offsets = []
for j in range(4, 17):
    lo, hi = 1 << j, 1 << (j + 1)
    n = 400
    died = 0
    for _ in range(n):
        a = random.randrange(lo, hi)
        b = random.randrange(lo, hi)
        res, k, offs = run_seed(a, b)
        all_offsets.extend(offs)
        if res == 'died':
            died += 1
    p = died / n
    print(f"{j:>3} {n:>8} {died:>6} {p:>9.4f} {p * (1 << j):>8.2f}")

print()
print("== per-fuse hazard vs equidistribution prediction")
small_hits = sum(1 for off, beta in all_offsets if off in (1, 3, 5))
tot = len(all_offsets)
# empirical expected hits under uniformity: sum over fuses of 3/((beta_range)/2)
pred = sum(min(1.0, 6.0 / max(beta, 1)) for off, beta in all_offsets)
print(f"fuse events observed: {tot:,}")
print(f"fatal-window hits: {small_hits}  |  equidistribution "
      f"prediction: {pred:.1f}")

print()
print("== offset uniformity: P(offset <= t) vs t/range for small t")
import collections
small = collections.Counter()
norm = 0
for off, beta in all_offsets:
    if beta >= 64:
        norm += 1
        if off <= 25:
            small[off] += 1
print("offset counts (odd offsets 1..25, beta >= 64):")
print("  ", dict(sorted(small.items())))
exp_each = sum(2.0 / max(beta, 1) for off, beta in all_offsets if beta >= 64)
print(f"  uniform prediction per odd offset value: ~{exp_each:.1f}")

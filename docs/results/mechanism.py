"""Death-mode instrumentation + local invariant hunt.

Hypothesis from the a.a. run: the diagonal fatal mode (fuse offset in
{1,3,5}) is unreachable; all deaths flow through small-b boundary
modes. If true, the needed invariant is about |b - beta| near the
diagonal, checkable by finite predecessor analysis.
"""
import random
from collections import Counter

random.seed(7)


def beta_of(a):
    return (a - 1) if a % 2 == 1 else (a - 2)


def R(a, b):
    if b % 2 == 0:
        return a + 6, b - 3, 'T'
    beta = beta_of(a)
    alpha = 6 if a % 2 == 1 else 9
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3), 'C'
    return alpha + 3 * beta + 3, b - beta - 4, 'F'


def death_mode(a, b):
    if b <= 2:
        return 'b<=2'
    if b % 2 == 0 and b == 4:
        return 'b=4'
    beta = beta_of(a)
    if b % 2 == 1 and b > beta and b - beta in (1, 3, 5):
        return 'diagonal'
    return None


modes = Counter()
below_margins = Counter()   # gamma = b - beta < 0 at loopC entries
above_small = Counter()     # offset = b - beta > 0 at fuse entries
n_deep = 0
for trial in range(30000):
    a = random.randrange(3, 1 << 14)
    b = random.randrange(3, 1 << 14)
    for k in range(4000):
        m = death_mode(a, b)
        if m:
            modes[m] += 1
            break
        if a + b > (1 << 40):
            break
        if b % 2 == 1:
            n_deep += 1
            g = b - beta_of(a)
            if g < 0 and g >= -15:
                below_margins[g] += 1
            if 0 < g <= 15:
                above_small[g] += 1
        a, b, _ = R(a, b)
print("death modes over 30k random seeds:", dict(modes))
print(f"deep entries: {n_deep:,}")
print("small ABOVE-diagonal offsets (fatal {1,3,5}):",
      dict(sorted(above_small.items())))
print("small BELOW-diagonal gammas (-1 feeds b=4 death):",
      dict(sorted(below_margins.items())))
print()

# ---- backward analysis: can offset t in {1,3,5} have a predecessor?
# deep-entry (a, b odd). Predecessor classes:
#  (P-T) previous step was T from (a-6, b+3)
#  (P-F) previous was fuse-output: a = alpha0+3*beta0+3, b = t0-4
#  (P-C) previous was loopC-output: a = alpha0+3*(b0-3), b = beta0-(b0-3)
# For target offset t = b - beta_of(a):
def analyze_target(t):
    out = []
    # (P-F): b = t0-4 odd -> t0 odd; a determined by (alpha0, beta0):
    #   a odd case: a = 3*beta0+9, beta = a-1 = 3*beta0+8
    #        t = (t0-4) - (3*beta0+8) => t0 = t + 3*beta0 + 12
    #   a even case: a = 3*beta0+12, beta = 3*beta0+10
    #        t0 = t + 3*beta0 + 14
    out.append(f"  from fuse-output: needs prior offset t0 = t + 3*beta0"
               f" + 12 or 14 (huge, and recurses upward)")
    # (P-T): pre-state (a-6, b+3), b+3 even. That pre-state's own
    # predecessor must have produced b_pre = b+3 even, which only
    # loopC-outputs do (T flips parity; fuse-outputs are odd).
    #   loopC-output: b+3 = beta0 - (b0-3), a-6 = alpha0 + 3*(b0-3)
    #   with gamma0 = b0 - beta0 <= -1 (loopC guard), b0 odd.
    # Solve: let d = b0 - 3 >= ?; beta0 = b + 3 + d; a = alpha0+3d+6.
    #   beta_of(a): alpha0=6 -> a = 3d+12 even -> beta = 3d+10
    #               alpha0=9 -> a = 3d+15 odd  -> beta = 3d+14
    #   t = b - beta = (beta0 - d - 3) - (3d+10 or 3d+14)
    #     = beta0 - 4d - 13 or beta0 - 4d - 17
    out.append(f"  from T-of-loopC: t = beta0 - 4*d - 13 (a even) or "
               f"beta0 - 4*d - 17 (a odd), with constraint "
               f"gamma0 = (d+3) - beta0 <= -1  i.e. beta0 >= d + 4")
    return out

for t in (1, 3, 5, 7, 9):
    print(f"target fuse offset t = {t}:")
    for line in analyze_target(t):
        print(line)
    # T-of-loopC feasibility: t = beta0 - 4d - 13 => beta0 = t+4d+13
    #   constraint beta0 >= d+4 always satisfiable; also parity:
    #   beta0 even (it's a beta), d = b0-3 with b0 odd -> d even.
    #   beta0 = t + 4d + 13: t odd -> t+13 even ✓ consistent.
    print(f"    e.g. d=0: beta0 = {13 + t} (even ✓), b0 = 3, "
          f"gamma0 = {3 - (13 + t)} <= -1 ✓ FEASIBLE unless b0=3 "
          f"state itself unreachable")

"""Verified renewal map R: complexity, growth, margins, residue BFS."""
import math, statistics
from collections import Counter


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


N = 100_000
x, y = 6, 13
syms = []
min_margin = 10**9
n_fuse = 0
for i in range(N):
    f = fatal(x, y)
    if f:
        print(f"FATAL ({f}) at renewal {i}: ({x}, {y})")
        break
    if y % 2 == 1:
        beta = (x - 1) if x % 2 == 1 else (x - 2)
        if y > beta:
            n_fuse += 1
            min_margin = min(min_margin, (y - beta) - 5)
    x, y, s = R(x, y)
    syms.append(s)
print(f"orbit alive {len(syms):,} renewals (final ~{x.bit_length()} bits)")
print(f"deep-fuse events {n_fuse:,}; min margin above fatal window: "
      f"{min_margin}")
print("symbols:", dict(Counter(syms)))

symstr = ''.join({'T': 'T', 'dC': 'c', 'DC': 'C', 'dF': 'f',
                  'DF': 'F'}[s] for s in syms)
p = [len(set(symstr[i:i + n] for i in range(len(symstr) - n)))
     for n in range(1, 15)]
print("factor complexity p(n) n=1..14:", p)
print("Sturmian would be              :", [n + 1 for n in range(1, 15)])

x, y = 6, 13
lg = []
for i in range(30000):
    s0 = x + y
    x, y, _ = R(x, y)
    lg.append(math.log((x + y) / s0))
print(f"log-growth/renewal: mean {statistics.mean(lg):.4f}  "
      f"std {statistics.stdev(lg):.4f}")


def bfs_mod(M):
    """Sound residue abstraction: halving handled by 2-lift."""
    seen = {(6 % M, 13 % M)}
    frontier = list(seen)
    while frontier:
        nf = []
        for (u, v) in frontier:
            outs = []
            if v % 2 == 0:
                outs.append(((u + 6) % M, (v - 3) % M))
            else:
                alpha, boff = (6, 1) if u % 2 == 1 else (9, 2)
                beta = (u - boff) % M
                # both exit branches are affine in (u, v) mod M —
                # no halving actually appears in R itself!
                outs.append(((alpha + 3 * ((v - 3) % M)) % M,
                             (beta - ((v - 3) % M)) % M))
                outs.append(((alpha + 3 * beta + 3) % M,
                             (v - beta - 4) % M))
            for w in outs:
                if w not in seen:
                    seen.add(w)
                    nf.append(w)
        frontier = nf
    bad = 0
    for (u, v) in seen:
        if v == 4 % M:
            bad += 1
            continue
        if M % 2 == 0 and v % 2 == 0:
            continue
        boff = 1 if (M % 2 == 0 and u % 2 == 1) else 2
        if M % 2 == 0:
            beta = (u - boff) % M
            if (v - beta) % M in (1 % M, 3 % M, 5 % M):
                bad += 1
        else:
            for boff2 in (1, 2):
                if (v - (u - boff2)) % M in (1 % M, 3 % M, 5 % M):
                    bad += 1
                    break
    return len(seen), bad


for M in (8, 16, 24, 48, 96, 192, 384):
    tot, bad = bfs_mod(M)
    tag = "  <== INVARIANT CANDIDATE!" if bad == 0 else ""
    print(f"mod {M}: reachable {tot}/{M * M}, fatal-compatible {bad}{tag}")

"""Two-ended emulation for dossier-3 (MIP*-inspired alignment).

A: forward machine — the certified renewal orbit (normalized).
B: ending machine — the halt cone, two forms:
   B1 raw: predecessor constraint-patterns of the halting
      configuration under dossier-3's actual step function.
   B2 abstract: the exact dying-at-depth-k line families under R
      (symbolic preimages of the fatal set, integer-parametrized).
Verifier: alignment checks between A and B at both levels.
"""
import sys
sys.path.insert(0, '.')
from metastep_check import meta_step

# ================= B1: raw backward cone for dossier-3 ==============
# table: 1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE
TBL = {('A', 0): (1, 'R', 'B'), ('A', 1): (1, 'R', 'B'),
       ('B', 0): (1, 'L', 'C'), ('B', 1): (0, 'R', 'E'),
       ('C', 1): (1, 'L', 'D'),
       ('D', 0): (0, 'R', 'A'), ('D', 1): (1, 'L', 'B'),
       ('E', 0): (1, 'R', 'A'), ('E', 1): (1, 'L', 'F'),
       ('F', 0): (0, 'L', 'E'), ('F', 1): (1, 'L', 'E')}
# halt: state C reading 0. Backward config = (state, head, constraints)
# constraints: dict pos -> bit that the PRE-tape must satisfy.

def preds(state, head, cons):
    out = []
    for (s, b), (w, d, ns) in TBL.items():
        if ns != state:
            continue
        ph = head - (1 if d == 'R' else -1)
        # the step wrote w at ph; post-tape[ph] = w must be consistent
        # with cons; pre-tape[ph] = b.
        if ph in cons and cons[ph] != w:
            continue
        nc = dict(cons)
        nc.pop(ph, None)
        if ph in nc and nc[ph] != b:
            continue
        nc[ph] = b
        out.append((s, ph, nc))
    return out


def raw_cone(depth):
    level = [('C', 0, {0: 0})]
    counts = [1]
    for d in range(depth):
        nxt = []
        for st, h, c in level:
            nxt.extend(preds(st, h, c))
        # dedup
        seen = set()
        ded = []
        for st, h, c in nxt:
            k = (st, h, tuple(sorted(c.items())))
            if k not in seen:
                seen.add(k)
                ded.append((st, h, c))
        level = ded
        counts.append(len(level))
    return counts, level


counts, frontier = raw_cone(24)
print("B1 raw halt-cone family counts by depth:")
print("  ", counts)
# alignment check: a certified forward spawn-entry has tape
# ...1 1 1... around the head with holes only at h1,h2: check whether
# any cone pattern at depth 24 is satisfiable by a holeTape shape.
# A pattern is holeTape-compatible if its constrained cells can be
# 1s except at <=2 positions that are 0 with everything left of the
# spawn edge 0. Quick necessary test: count 0-constraints in a window
# of width 6 (holeTape has at most 1 hole per 4 cells near the head
# in certified shapes... use: >=3 zeros within any 6-window impossible)
def max_zeros_in_window(c, w=6):
    zs = sorted(p for p, v in c.items() if v == 0)
    best = 0
    for i in range(len(zs)):
        j = i
        while j < len(zs) and zs[j] - zs[i] < w:
            j += 1
        best = max(best, j - i)
    return best

viol = sum(1 for st, h, c in frontier if max_zeros_in_window(c) >= 3)
print(f"  depth-24 families: {len(frontier)}; with >=3 zeros in a "
      f"6-window (impossible in certified shapes): {viol}")

# ================ B2: abstract dying-at-k line families =============
# family: (a, b) = (A0 + A1*s, B0 + B1*s), s in Z_{>=0}
class F:
    __slots__ = ('A0', 'A1', 'B0', 'B1')

    def __init__(self, A0, A1, B0, B1):
        self.A0, self.A1, self.B0, self.B1 = A0, A1, B0, B1

    def key(self):
        return (self.A0, self.A1, self.B0, self.B1)


def sub_param(f, mult, off):
    """s -> mult*s + off"""
    return F(f.A0 + f.A1 * off, f.A1 * mult,
             f.B0 + f.B1 * off, f.B1 * mult)


def with_parity(f, which, want):
    """restrict so that a(s) (which='a') or b(s) has parity `want`;
    returns list of reparametrized families."""
    C0, C1 = (f.A0, f.A1) if which == 'a' else (f.B0, f.B1)
    out = []
    for off in (0, 1):
        if (C0 + C1 * off) % 2 == want and (C1 * 2) % 2 == 0:
            out.append(sub_param(f, 2, off))
    if C1 % 2 == 0:
        return out[:1] if out and (C0 % 2 == want) else \
            ([sub_param(f, 1, 0)] if C0 % 2 == want else [])
    return out


def positive_part(f):
    """None if a(s), b(s) can never both be >= 1 for s >= 0 (coarse)."""
    if f.A1 < 0 and f.A0 < 1:
        return None
    if f.B1 < 0 and f.B0 < 1:
        return None
    return f


def preimages(f):
    out = []
    # T-inverse: (a, b) = (a' - 6, b' + 3); guard pre-b even
    g = F(f.A0 - 6, f.A1, f.B0 + 3, f.B1)
    out.extend(with_parity(g, 'b', 0))
    # C-inverse and F-inverse per alpha case; both need a' ≡ alpha or
    # alpha+3 (mod 3) — i.e. divisibility of a linear form by 3:
    for alpha, aoff, parity_a in ((6, 1, 1), (9, 2, 0)):
        for br in ('C', 'Fu'):
            need = alpha % 3 if br == 'C' else (alpha + 3) % 3
            # reparametrize to make a'(s) ≡ need mod 3
            cands = []
            if f.A1 % 3 == 0:
                if f.A0 % 3 == need:
                    cands.append(sub_param(f, 1, 0))
            else:
                for off in (0, 1, 2):
                    if (f.A0 + f.A1 * off) % 3 == need:
                        cands.append(sub_param(f, 3, off))
            for h in cands:
                if br == 'C':
                    # b = (a'-alpha)/3 + 3 ; beta = b' + (a'-alpha)/3
                    dA0, dA1 = (h.A0 - alpha) // 3, h.A1 // 3
                    b0, b1 = dA0 + 3, dA1
                    beta0, beta1 = h.B0 + dA0, h.B1 + dA1
                    a0, a1 = beta0 + aoff, beta1
                else:
                    # beta = (a'-alpha-3)/3 ; b = b'+beta+4
                    beta0, beta1 = (h.A0 - alpha - 3) // 3, h.A1 // 3
                    b0, b1 = h.B0 + beta0 + 4, h.B1 + beta1
                    a0, a1 = beta0 + aoff, beta1
                g2 = F(a0, a1, b0, b1)
                # guards: b odd; a parity == parity_a
                for g3 in with_parity(g2, 'b', 1):
                    for g4 in with_parity(g3, 'a', parity_a):
                        if positive_part(g4):
                            out.append(g4)
    return out


# fatal set as families (b constant lines): b in {1,2,4} any a;
# diagonal: a odd: (2s+1, 2s+d) d in {0,2,4}; a even: (2s+2, 2s+d)
fatal_fams = [F(1, 1, 1, 0), F(1, 1, 2, 0), F(1, 1, 4, 0)]
for d in (0, 2, 4):
    fatal_fams.append(F(1, 2, 1 + d, 2))     # a=2s+1, b=(a-1)+d = 2s+d
for d in (-1, 1, 3):
    fatal_fams.append(F(2, 2, 2 + d + 0, 2))  # a=2s+2, b=(a-2)+d+... 

level = fatal_fams
print("\nB2 abstract dying-at-depth-k line-family counts:")
tot = len(level)
print(f"  depth 0: {len(level)}")
all_levels = [list(level)]
for k in range(1, 13):
    nxt = []
    seen = set()
    for f in level:
        for g in preimages(f):
            if g.key() not in seen:
                seen.add(g.key())
                nxt.append(g)
    level = nxt
    all_levels.append(list(level))
    print(f"  depth {k}: {len(level)}")

# ---- verifier: alignment of forward D3 orbit vs the abstract cone
def member(pt, f):
    a, b = pt
    if f.A1 == 0:
        if a != f.A0:
            return False
        return (b - f.B0) % f.B1 == 0 and (b - f.B0) // f.B1 >= 0 \
            if f.B1 else b == f.B0
    if (a - f.A0) % f.A1 != 0:
        return False
    s = (a - f.A0) // f.A1
    return s >= 0 and f.B0 + f.B1 * s == b


# D3 forward orbit (normalized == R) from its first C-entry
def mirror_step(ms):
    return meta_step(*ms)

ms = (False, -17, -11, 39, 40)   # D3 s0, normalized
while True:
    three, l, h1, h2, r = ms
    if (not three) and h2 == r - 3:
        break
    ms = mirror_step(ms)
a0, b0 = h1 - l, h2 - h1
print(f"\nA: dossier-3 first C-entry (normalized): (a, b) = ({a0}, {b0})")


def Rmap(a, b):
    if b % 2 == 0:
        return a + 6, b - 3
    alpha, beta = (6, a - 1) if a % 2 == 1 else (9, a - 2)
    if b < beta:
        return alpha + 3 * (b - 3), beta - (b - 3)
    return alpha + 3 * beta + 3, b - beta - 4


hits = 0
x, y = a0, b0
NF = sum(len(lv) for lv in all_levels)
for n in range(20000):
    for lv in all_levels:
        for f in lv:
            if member((x, y), f):
                hits += 1
    x, y = Rmap(x, y)
print(f"verifier: 20,000 forward D3 renewal states tested against "
      f"{NF} cone families (depths 0-12): alignments found: {hits}")
print("=> every tested forward state is > 12 renewals from death, "
      "verified two-endedly" if hits == 0 else "!! alignment found")

"""Two-ended sweep across open machines.

Per machine: backward halt-cone BFS (constraint-pattern families from
every undefined transition), fitted backward branching ratio, forward
raw run with sampled exact alignment checks, and the cone's
constraint-density statistic.
"""
import sys
from math import log


def parse(code):
    tbl = {}
    halts = []
    for si, block in enumerate(code.split('_')):
        st = 'ABCDEF'[si][:1]
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            if tr == '---':
                tbl[(st, b)] = None
                halts.append((st, b))
            else:
                tbl[(st, b)] = (int(tr[0]), tr[1], tr[2])
    return tbl, halts


def preds(tbl, state, head, cons):
    out = []
    for (s, b), tr in tbl.items():
        if tr is None:
            continue
        w, d, ns = tr
        if ns != state:
            continue
        ph = head - (1 if d == 'R' else -1)
        if ph in cons and cons[ph] != w:
            continue
        nc = dict(cons)
        nc.pop(ph, None)
        nc[ph] = b
        out.append((s, ph, nc))
    return out


def cone(tbl, halts, depth):
    level = [(s, 0, {0: b}) for (s, b) in halts]
    counts = [len(level)]
    levels = [list(level)]
    for d in range(depth):
        nxt = []
        seen = set()
        for st, h, c in level:
            for p in preds(tbl, st, h, c):
                k = (p[0], p[1], tuple(sorted(p[2].items())))
                if k not in seen:
                    seen.add(k)
                    nxt.append(p)
        level = nxt
        counts.append(len(level))
        levels.append(list(level))
        if len(level) > 20000:
            break
    return counts, levels


def zeros_stat(levels):
    """max zeros in a 6-window across deepest level's families (min
    over families = the weakest constraint pattern)."""
    lv = levels[-1]
    if not lv:
        return None
    vals = []
    for st, h, c in lv:
        zs = sorted(p for p, v in c.items() if v == 0)
        best = 0
        for i in range(len(zs)):
            j = i
            while j < len(zs) and zs[j] - zs[i] < 6:
                j += 1
            best = max(best, j - i)
        vals.append(best)
    return min(vals), max(vals)


def align_run(tbl, levels, steps, sample_every):
    """Forward run; at sampled times check exact membership in any cone
    family (match = dies in exactly that depth). Returns matches."""
    by_state = {}
    for d, lv in enumerate(levels):
        for st, h, c in lv:
            by_state.setdefault(st, []).append((d, h, c))
    tape = {}
    st, hd = 'A', 0
    matches = []
    for t in range(steps):
        if t % sample_every == 0:
            for d, ph, c in by_state.get(st, []):
                ok = all(tape.get(hd + (pos - ph), 0) == bit
                         for pos, bit in c.items())
                if ok:
                    matches.append((t, d))
                    break
        tr = tbl[(st, tape.get(hd, 0))]
        if tr is None:
            return matches, t
        w, dv, ns = tr
        tape[hd] = w
        hd += 1 if dv == 'R' else -1
        st = ns
    return matches, None


QUEUE = [ln.strip() for ln in open(
    '/Users/enan/Documents/bbchallenge-proofs/experiments/outputs/'
    'stage753_queue.txt') if ln.strip()]

print(f"== full two-ended pipeline: {len(QUEUE)} queue machines")
print(f"{'machine':<44} {'lam_back':>8} {'cone@d':>8} {'z6':>7} "
      f"{'aligns':>7} {'halt@':>7}")
for code in QUEUE:
    tbl, halts = parse(code)
    counts, levels = cone(tbl, halts, 22)
    lam = (counts[-1] / counts[-5]) ** 0.25 if counts[-5] else 0
    zst = zeros_stat(levels)
    matches, halted = align_run(tbl, levels, 300000, 25)
    print(f"{code:<44} {lam:>8.3f} {counts[-1]:>8} "
          f"{str(zst):>7} {len(matches):>7} "
          f"{str(halted) if halted is not None else '-':>7}")

print()
print("== cone-only sweep: 1094 holdouts, depth 16")
H = [ln.strip() for ln in open(
    '/Users/enan/Documents/bbchallenge-proofs/experiments/outputs/'
    'BB6_holdouts_1094.txt') if ln.strip()]
import collections
lams = []
weird = []
for code in H:
    try:
        tbl, halts = parse(code)
        counts, levels = cone(tbl, halts, 16)
        if len(counts) >= 6 and counts[-5] > 0:
            lam = (counts[-1] / counts[-5]) ** 0.25
        else:
            lam = 0.0
        lams.append(lam)
        if lam > 2.2 or lam < 1.01:
            weird.append((code, lam, counts[-1]))
    except Exception as e:
        weird.append((code, 'ERR', str(e)[:30]))
hist = collections.Counter(round(l, 1) for l in lams if isinstance(l, float))
print("lambda_back histogram (rounded to 0.1):")
for k in sorted(hist):
    print(f"  {k:>4}: {'#' * min(hist[k], 60)} {hist[k]}")
print(f"outliers (lam > 2.2 or < 1.01): {len(weird)}")
for w in weird[:10]:
    print("  ", w)

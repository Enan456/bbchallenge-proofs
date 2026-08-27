"""Dossier-4: the three-machine verdict harness.

Machine 1 (START):  blank-tape startup — steps until the first stable
                    regime is established.
Machine 2 (REGIME): the regime-change emulator — segments the record-
                    event sequence into maximal runs governed by one
                    affine law (constant second difference of event
                    times); regime changes are the law switches.
Machine 3 (END):    the backward halt cone — family growth lambda and
                    exact alignment of the forward run against it.

Verdict compilation: HALTS(t) | NONHALT-certified-conditional |
OPEN(start, regimes, cone margin).
"""
import sys
sys.path.insert(0, '.')
from cone_sweep import parse, cone, align_run

CERTIFIED = {
    '1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA':
        'NONHALT if HydraSafe (certified reduction)',
    '1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB':
        'NONHALT if SafeOrbit (certified reduction)',
    '1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD':
        'NONHALT if SafeMetaOrbit (certified closure)',
    '1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE':
        'NONHALT if SafeMetaOrbit (certified closure)',
}


def regimes(code, steps):
    tbl, halts = parse(code)
    tape = {}
    st, hd = 'A', 0
    lo = hi = 0
    events = []
    for t in range(steps):
        if hd > hi or hd < lo:
            events.append(t)
            lo, hi = min(lo, hd), max(hi, hd)
        tr = tbl[(st, tape.get(hd, 0))]
        if tr is None:
            return None, t
        w, d, ns = tr
        tape[hd] = w
        hd += 1 if d == 'R' else -1
        st = ns
    # segment with stride detection: laws may act on every s-th event
    best = ([], 1, 0.0)
    for stride in (1, 2, 3, 4):
        cov = 0
        regs = []
        for ph in range(stride):
            sub = events[ph::stride]
            dts = [sub[i + 1] - sub[i] for i in range(len(sub) - 1)]
            sd = [dts[i + 1] - dts[i] for i in range(len(dts) - 1)]
            i = 0
            while i < len(sd):
                j = i
                while j < len(sd) and sd[j] == sd[i]:
                    j += 1
                if j - i >= 3:
                    regs.append((ph + i * stride, (j - i) * stride,
                                 sd[i], stride))
                    cov += (j - i) * stride
                i = max(j, i + 1)
        frac = cov / max(len(events), 1)
        if frac > best[2]:
            best = (regs, stride, frac)
    regs, stride, frac = best
    regs.sort()
    return regs, None


QUEUE = [ln.strip() for ln in open(
    '/Users/enan/Documents/bbchallenge-proofs/experiments/outputs/'
    'stage753_queue.txt') if ln.strip()]

print("DOSSIER-4 VERDICT TABLE (start | regimes | end-cone | verdict)")
print("=" * 100)
for code in QUEUE:
    tbl, halts = parse(code)
    regs, halted = regimes(code, 250000)
    counts, levels = cone(tbl, halts, 20)
    lam = (counts[-1] / counts[-5]) ** 0.25 if len(counts) > 5 and \
        counts[-5] else 0
    matches, h2 = align_run(tbl, levels, 250000, 50)
    if halted is not None:
        verdict = f"HALTS at step {halted}"
    elif code in CERTIFIED:
        verdict = CERTIFIED[code]
    else:
        verdict = "OPEN"
    if regs:
        start_len = regs[0][0]
        nreg = len(regs)
        mean_len = sum(r[1] for r in regs) / nreg
        laws = len(set(r[2] for r in regs))
        stride = regs[0][3]
        reg_s = (f"startup<=evt{start_len}, {nreg} regimes "
                 f"(stride {stride}), mean len {mean_len:.0f} evts, "
                 f"{laws} distinct laws")
    else:
        reg_s = "no stable regimes found"
    print(f"{code}")
    print(f"  START : blank -> first regime after event {regs[0][0] if regs else '?'}")
    print(f"  REGIME: {reg_s}")
    print(f"  END   : cone lam={lam:.3f}, families@20={counts[-1]}, "
          f"alignments in 250k steps: {len(matches)}")
    print(f"  VERDICT: {verdict}")
    print()

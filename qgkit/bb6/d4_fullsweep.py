"""Dossier-4 full sweep: START/REGIME/END + verdict for all 1,094
holdouts. Resumable JSONL output."""
import sys, json, os
sys.path.insert(0, '.')
from cone_sweep import parse, cone, align_run
from dossier4 import regimes

OUT = '/Users/enan/Documents/bbchallenge-proofs/experiments/outputs/d4_fullsweep.jsonl'
H = [ln.strip() for ln in open(
    '/Users/enan/Documents/bbchallenge-proofs/experiments/outputs/'
    'BB6_holdouts_1094.txt') if ln.strip()]

done = set()
if os.path.exists(OUT):
    for ln in open(OUT):
        try:
            done.add(json.loads(ln)['code'])
        except Exception:
            pass

with open(OUT, 'a') as f:
    for i, code in enumerate(H):
        if code in done:
            continue
        try:
            tbl, halts = parse(code)
            regs, halted = regimes(code, 120000)
            counts, levels = cone(tbl, halts, 18)
            lam = (counts[-1] / counts[-5]) ** 0.25 \
                if len(counts) > 5 and counts[-5] else 0.0
            matches, h2 = align_run(tbl, levels, 120000, 100)
            row = dict(code=code, halted=halted or h2,
                       lam=round(lam, 4), cone=counts[-1],
                       cone_depth=len(counts) - 1,
                       nreg=len(regs) if regs else 0,
                       stride=regs[0][3] if regs else 0,
                       laws=len(set(r[2] for r in regs)) if regs else 0,
                       reg_cov=round(sum(r[1] for r in regs) /
                                     max(1, 1) / 1, 1) if regs else 0,
                       startup=regs[0][0] if regs else -1,
                       aligns=len(matches))
        except Exception as e:
            row = dict(code=code, error=str(e)[:60])
        f.write(json.dumps(row) + '\n')
        f.flush()
        if i % 50 == 0:
            print(f"progress {i}/{len(H)}", flush=True)
print("SWEEPDONE")

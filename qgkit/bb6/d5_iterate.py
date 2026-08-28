"""Fail-closed orbit extension: iterate the v2 calculus at word level
far beyond the raw-validated horizon.  Any unmatched context aborts
(Unexplained) -- nothing is guessed.

Usage: python3 d5_iterate.py [n_segments] [learn_steps]
"""
import sys, time
sys.path.insert(0, '.')
from d5_calculus2 import stream_segments2, Calculus2
from d5_calculus import Unexplained

N_SEG = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
LEARN = int(sys.argv[2]) if len(sys.argv) > 2 else 8_000_000

calc = Calculus2()
last = None
for (sg, t0, t1) in stream_segments2(LEARN):
    if sg is None:
        raise SystemExit(f"extraction failure at t={t0}")
    calc.learn([sg])
    last = sg
rec = last['rec']
cells = (('.' + rec['s_out']) if rec['kind_next'] == 'full'
         else rec['s_out'])
poff = rec['poff_out'] + (1 if rec['kind_next'] == 'full' else 0)
arr = rec['arr_out']
kind = rec['kind_next']
t_pred = rec['t'] + rec['dt']
print(f"seed: raw t={t_pred:,} width={len(cells)} kind={kind}")

t0w = time.time()
n_mini = 0
ones3 = cells.count('###')
for k in range(N_SEG):
    try:
        cells2, arr, dt, poff2, kind2 = calc.step(cells, arr, poff,
                                                  kind)
    except Unexplained as e:
        print(f"FRONTIER at segment {k}, predicted raw "
              f"t={t_pred:,}: {str(e)[:200]}")
        break
    t_pred += dt
    if kind2 == 'full':
        cells = '.' + cells2
        poff = poff2 + 1
    else:
        cells = cells2
        poff = poff2
        n_mini += 1
    kind = kind2
    if (k + 1) % 2000 == 0:
        print(f"[{time.time()-t0w:6.0f}s] seg {k+1}: predicted raw "
              f"t={t_pred:,} width={len(cells)} minis={n_mini} "
              f"threes={cells.count('###')}", flush=True)
else:
    print()
    print(f"COMPLETE: {N_SEG} segments iterated fail-closed, "
          f"0 unexplained")
print(f"final predicted raw t={t_pred:,} width={len(cells)} "
      f"minis={n_mini} wall={time.time()-t0w:.0f}s")

"""Learn on ALL of 200M: does the 20-cell decision window stay
single-valued once every context is absorbed?  Conflicts would mean
the window is genuinely insufficient (aliasing); zero conflicts mean
the three frozen-phase mismatches were resolvable novelty."""
import sys
sys.path.insert(0, '.')
from d5_calculus2 import stream_segments2, Calculus2
from d5_calculus import Unexplained

calc = Calculus2()
n = 0
conf = []
for (sg, t0, t1) in stream_segments2(200_000_000):
    if sg is None:
        conf.append((t0, 'extract'))
        continue
    try:
        calc.learn([sg])
        n += 1
    except Unexplained as e:
        conf.append((sg['rec']['t'], str(e)[:200]))
print(f"learned {n} segments; conflicts: {len(conf)}")
for c in conf[:10]:
    print("  CONFLICT", c)
print(f"tables: heads={len(calc.heads)} ctx={len(calc.ctx)} "
      f"tails={len(calc.tails)}")

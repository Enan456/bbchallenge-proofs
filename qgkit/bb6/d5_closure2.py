"""v2 closure protocol: learn [0, LEARN), frozen validation
[LEARN, TOTAL).  Fail-closed; exact words, step counts, arrival
types, head offsets, kinds; continuous chain verification."""
import sys, pickle, time
sys.path.insert(0, '.')
from d5_calculus2 import stream_segments2, Calculus2, validate2
from d5_calculus import Unexplained

LEARN = int(sys.argv[1]) if len(sys.argv) > 1 else 40_000_000
TOTAL = int(sys.argv[2]) if len(sys.argv) > 2 else 200_000_000

t_start = time.time()
calc = Calculus2()
n_learn = n_val = n_fail = n_x = chain_bad = 0
prev = None
fail_log = []

for (sg, t0, t1) in stream_segments2(TOTAL):
    if sg is None:
        n_x += 1
        fail_log.append((t0, 'extract', f'{t0}..{t1}'))
        prev = None
        continue
    rec = sg['rec']
    if prev is not None and prev[0] == rec['t']:
        exp = (('.' + prev[1]) if rec['kind'] == 'full' else prev[1])
        expo = prev[2] + (1 if rec['kind'] == 'full' else 0)
        if (rec['s_in'] != exp or rec['poff_in'] != expo
                or rec['kind'] != prev[3]):
            chain_bad += 1
    prev = (rec['t'] + rec['dt'], rec['s_out'], rec['poff_out'],
            rec['kind_next'])
    if rec['t'] < LEARN:
        try:
            calc.learn([sg])
            n_learn += 1
        except Unexplained as e:
            n_fail += 1
            fail_log.append((rec['t'], 'learn-conflict', str(e)[:300]))
    else:
        n_val += 1
        try:
            s_out, arr_out, dt, poff, kn = calc.step(
                rec['s_in'], rec['arr_in'], rec['poff_in'],
                rec['kind'])
            if (s_out != rec['s_out'] or arr_out != rec['arr_out']
                    or dt != rec['dt'] or poff != rec['poff_out']
                    or kn != rec['kind_next']):
                n_fail += 1
                fail_log.append((rec['t'], 'mismatch',
                                 f"dt {dt}/{rec['dt']} poff {poff}/"
                                 f"{rec['poff_out']} kind {kn}/"
                                 f"{rec['kind_next']} word_eq="
                                 f"{s_out == rec['s_out']}"))
        except Unexplained as e:
            n_fail += 1
            fail_log.append((rec['t'], 'unexplained', str(e)[:300]))
    if (n_learn + n_val) % 200 == 0:
        print(f"[{time.time()-t_start:7.0f}s] t={rec['t']:>12,} "
              f"learn={n_learn} val={n_val} fail={n_fail} "
              f"chain_bad={chain_bad}", flush=True)

print()
print(f"=== V2 CLOSURE REPORT (learn<{LEARN:,}, total {TOTAL:,}) ===")
print(f"learned segments : {n_learn}")
print(f"validated frozen : {n_val}")
print(f"failures         : {n_fail}")
print(f"extract failures : {n_x}")
print(f"chain violations : {chain_bad}")
print(f"tables: heads={len(calc.heads)} ctx={len(calc.ctx)} "
      f"tails={len(calc.tails)}")
for (t, kind, msg) in fail_log[:25]:
    print(f"  FAIL t={t} [{kind}] {msg}")
with open('d5_calc2_tables.pkl', 'wb') as f:
    pickle.dump(dict(heads=calc.heads, ctx=calc.ctx,
                     tails=calc.tails), f)
print(f"done; wall {time.time()-t_start:.0f}s")

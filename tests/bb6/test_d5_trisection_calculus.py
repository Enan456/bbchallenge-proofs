"""Differential validation of the dossier-5 trisection calculus (v2).

The calculus is a fail-closed word-rewrite system for the rank-1
array-class machine 1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC:
tape configurations at "arrival" events are words of 1-blocks
(lengths 1/2/3) with single-0 gaps; one segment (left shoot +
rightward transducer pass) maps word -> word with exact step count.

This test learns the rule tables on a training horizon and then
requires EXACT reproduction (output word, arrival type, step count,
head offset, next-segment kind) of every segment in a held-out
horizon, plus perfect configuration chaining throughout.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]
                       / 'qgkit' / 'bb6'))

from d5_calculus2 import stream_segments2, Calculus2   # noqa: E402
from d5_calculus import Unexplained                    # noqa: E402

TRAIN = 2_000_000
TOTAL = 4_000_000


def test_trisection_calculus_exact():
    calc = Calculus2()
    n_learn = n_val = n_none = chain_bad = 0
    prev = None
    fails = []
    for (sg, t0, t1) in stream_segments2(TOTAL):
        assert sg is not None, f"extraction failed at t={t0}"
        rec = sg['rec']
        if prev is not None and prev[0] == rec['t']:
            exp = (('.' + prev[1]) if rec['kind'] == 'full'
                   else prev[1])
            expo = prev[2] + (1 if rec['kind'] == 'full' else 0)
            assert rec['s_in'] == exp and rec['poff_in'] == expo \
                and rec['kind'] == prev[3], \
                f"chain broken at t={rec['t']}"
        prev = (rec['t'] + rec['dt'], rec['s_out'],
                rec['poff_out'], rec['kind_next'])
        if rec['t'] < TRAIN:
            calc.learn([sg])
            n_learn += 1
        else:
            n_val += 1
            s_out, arr_out, dt, poff, kn = calc.step(
                rec['s_in'], rec['arr_in'], rec['poff_in'],
                rec['kind'])
            assert s_out == rec['s_out'], f"word at t={rec['t']}"
            assert arr_out == rec['arr_out'], f"arr at t={rec['t']}"
            assert dt == rec['dt'], f"dt at t={rec['t']}"
            assert poff == rec['poff_out'], f"poff at t={rec['t']}"
            assert kn == rec['kind_next'], f"kind at t={rec['t']}"
    assert n_learn > 100 and n_val > 100


if __name__ == '__main__':
    test_trisection_calculus_exact()
    print("trisection calculus: exact on held-out horizon")

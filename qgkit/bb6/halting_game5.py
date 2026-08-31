"""The halting game over the dossier-5 word calculus.

Same protocol as halting_game.py, on the rank-1 array-class machine
1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC:

  state   : word configuration (cells, arrival, head offset, kind)
  law     : one calc.step evaluation of the learned v2 calculus
            (fail-closed: an Unexplained context is a rejection)
  terminal: the claimed halt word, materialized as a literal tape and
            run on the raw machine, must actually halt (bounded run)

Forged terminals are built from the machine's own backward halt cone:
a constraint pattern with control state B, stamped around the head of
a true orbit word, halts within its cone depth by construction.
Prover B in the forgery is literally the end machine.
"""

import sys, random, pathlib
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from d5_calculus2 import stream_segments2, Calculus2
from d5_calculus import TBL, Unexplained

SEED_STEPS = 40_000_000     # learning horizon for the calculus


def build(K):
    """Learn the calculus, take the last raw-validated config as the
    game seed, iterate K segments fail-closed."""
    calc = Calculus2()
    last = None
    for (sg, t0, t1) in stream_segments2(SEED_STEPS):
        if sg is None:
            raise SystemExit("extraction failure")
        calc.learn([sg])
        last = sg
    rec = last['rec']
    cells = (('.' + rec['s_out']) if rec['kind_next'] == 'full'
             else rec['s_out'])
    poff = rec['poff_out'] + (1 if rec['kind_next'] == 'full' else 0)
    cfg = (cells, rec['arr_out'], poff, rec['kind_next'])
    orbit = [cfg]
    for k in range(K):
        cells, arr, poff, kind = orbit[-1]
        try:
            c2, a2, dt, p2, k2 = calc.step(cells, arr, poff, kind)
        except Unexplained:
            print(f"[orbit truncated at fail-closed frontier, "
                  f"segment {k}]")
            break
        if k2 == 'full':
            orbit.append(('.' + c2, a2, p2 + 1, k2))
        else:
            orbit.append((c2, a2, p2, k2))
    return calc, orbit


def raw_halts(cells, poff, max_steps=100_000):
    tape = {i: (1 if c == '#' else 0) for i, c in enumerate(cells)}
    pos, st = poff, 'B'
    for t in range(max_steps):
        r = tape.get(pos, 0)
        tr = TBL[(st, r)]
        if tr is None:
            return t
        w, d, ns = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
    return None


def cone_families(depth, want_state='B'):
    """Backward constraint-pattern BFS from the halt (E reads 1);
    returns patterns with the wanted control state."""
    def preds(state, pat):
        out = []
        for (st0, r0), tr in TBL.items():
            if tr is None or tr[2] != state:
                continue
            w, d, ns = tr
            cell = -(1 if d == 'R' else -1)
            if cell in pat and pat[cell] != w:
                continue
            np_ = dict(pat)
            np_[cell] = r0
            out.append((st0, {k - cell: v for k, v in np_.items()}))
        return out
    frontier = [('E', {0: 1})]
    seen = {('E', ((0, 1),))}
    hits = []
    for _ in range(depth):
        nxt = []
        for (st, pat) in frontier:
            for (s0, p0) in preds(st, pat):
                c = (s0, tuple(sorted(p0.items())))
                if c not in seen:
                    seen.add(c)
                    nxt.append((s0, p0))
                    if s0 == want_state:
                        hits.append(p0)
        frontier = nxt
    return hits


class Honest:
    def __init__(self, orbit):
        self.orbit = orbit

    def snapshot(self, j):
        return self.orbit[j]

    def halt_index(self):
        return None                 # verified below: no fatal words


class ConeForger(Honest):
    """True orbit to seam m; at m+1, the true word stamped with a
    halt-cone pattern around the head (state B preserved)."""

    def __init__(self, orbit, m, pat):
        super().__init__(orbit)
        self.m = m
        cells, arr, poff, kind = orbit[m + 1]
        cl = list(cells)
        ok = True
        for off, bit in pat.items():
            i = poff + off
            if not (0 <= i < len(cl)):
                ok = False
                break
            cl[i] = '#' if bit else '.'
        self.ok = ok
        self.forged = (''.join(cl), arr, poff, kind)

    def snapshot(self, j):
        return self.forged if j == self.m + 1 else self.orbit[j]

    def halt_index(self):
        return self.m + 1


def play(calc, pa, pb, K, r, rng):
    if pa.snapshot(0) != pb.snapshot(0):
        return False, 'seed'
    k = pa.halt_index()
    if k is None or k != pb.halt_index():
        return False, 'no-halt-claim'
    ck, ak, pk, kk = pa.snapshot(k)
    if pa.snapshot(k) != pb.snapshot(k):
        return False, 'terminal-cross'
    if raw_halts(ck, pk) is None:
        return False, 'terminal-not-fatal'
    for _ in range(r):
        j = rng.randrange(K)
        sj = pa.snapshot(j)
        s1a = pa.snapshot(j + 1)
        if s1a != pb.snapshot(j + 1):
            return False, 'cross'
        try:
            c2, a2, dt, p2, k2 = calc.step(*sj)
        except Unexplained:
            return False, f'law-unexplained@{j}'
        nxt = (('.' + c2, a2, p2 + 1, k2) if k2 == 'full'
               else (c2, a2, p2, k2))
        if nxt != s1a:
            return False, f'law@{j}'
    return True, 'accept'


if __name__ == '__main__':
    K_REQ = 1200
    rng = random.Random(11)
    print("learning calculus + building word orbit "
          f"(learn {SEED_STEPS:,} raw steps)...", flush=True)
    calc, orbit = build(K_REQ)
    K = len(orbit) - 1
    print(f"orbit: {K} segments fail-closed, widths "
          f"{len(orbit[0][0])} -> {len(orbit[-1][0])}")

    # no word on the true orbit is fatal (spot-verify a sample raw)
    n_fatal = 0
    for (c, a, p, kk) in orbit[::max(1, K // 60)]:
        if raw_halts(c, p, 50_000) is not None:
            n_fatal += 1
    print(f"fatal words on true orbit (sampled): {n_fatal}")

    pats = cone_families(24, 'B')
    print(f"cone families with state B at depth<=24: {len(pats)}")

    # confirm a stamped forgery really halts
    demo = ConeForger(orbit, K // 2, pats[0])
    t_halt = raw_halts(demo.forged[0], demo.forged[2])
    print(f"demo forged terminal halts in {t_halt} raw steps")

    honest = Honest(orbit)
    print("honest provers:", play(calc, honest, honest, K, 8, rng))

    print(f"{'r':>7} {'accept':>8} {'(1-1/K)^r':>10}  trials")
    for r, trials in ((4, 300), (32, 300), (256, 120), (2048, 30),
                      (8192, 10)):
        n_acc = 0
        for t in range(trials):
            f = None
            while f is None or not f.ok:
                f = ConeForger(orbit, rng.randrange(K - 1),
                               pats[rng.randrange(len(pats))])
            acc, why = play(calc, f, f, K, r, rng)
            n_acc += acc
        print(f"{r:>7} {n_acc/trials:>8.3f} {(1-1/K)**r:>10.4f}  "
              f"{trials}", flush=True)

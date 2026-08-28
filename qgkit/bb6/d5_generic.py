"""Generic certification ladder for array-class machines.

For each machine: (auto-mirror to right-growing) -> arrival
segmentation -> unit tiling (architecture test) -> literal calculus
learn -> held-out exact validation.  All fail-closed; the verdict is
how far up the ladder the machine gets.

Rungs:
  ARCH   : arrivals found and >=90% of segments tile exactly
  LEARN  : deterministic literal rule tables (20-cell lookahead)
  EXACT  : held-out segments reproduced exactly (word+dt+offset)
"""
import sys
from collections import Counter

MINI_DEPTH = 8


def parse(code):
    tbl = {}
    for i, blk in enumerate(code.split('_')):
        st = chr(ord('A') + i)
        for r in (0, 1):
            e = blk[3 * r:3 * r + 3]
            tbl[(st, r)] = (None if e == '---'
                            else (int(e[0]), e[1], e[2]))
    return tbl


def mirror(tbl):
    return {k: (None if v is None else
                (v[0], 'L' if v[1] == 'R' else 'R', v[2]))
            for k, v in tbl.items()}


def growth_dir(tbl, steps=200000):
    tape = {}
    pos, st = 0, 'A'
    for _ in range(steps):
        r = tape.get(pos, 0)
        tr = tbl[(st, r)]
        if tr is None:
            return 'HALT'
        w, d, ns = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
    ones = [p for p in tape if tape[p]]
    if not ones:
        return 'R'
    lo, hi = min(ones), max(ones)
    return 'R' if hi >= -lo else 'L'


def cellstr(tp, a, b):
    return ''.join('#' if tp.get(p) else '.' for p in range(a, b + 1))


def stream_segments(tbl, steps):
    tape = {}
    pos, st = 0, 'A'
    lastd = None
    lo = 0
    buf = []
    pend = None
    cur_arr = None
    for t in range(steps):
        r = tape.get(pos, 0)
        tr = tbl[(st, r)]
        if tr is None:
            yield ('HALT', t, None)
            return
        w, d, ns = tr
        if lastd is not None and d != lastd:
            kind = 'M' if lastd == 'R' else 'm'
            buf.append((t, pos, st, r, kind))
            if kind == 'M':
                pend = (t, pos, st, r, dict(tape), lo)
            elif pend is not None:
                akind = None
                if pos < lo:
                    akind = 'full'
                elif pend[1] - pos >= MINI_DEPTH:
                    akind = 'mini'
                if akind is not None:
                    snap = (pend[4], pend[5], pend[1], pend[2],
                            pend[3])
                    t_arr = pend[0]
                    if cur_arr is not None:
                        t0, snap0, k0 = cur_arr
                        seg_turns = [u for u in buf
                                     if t0 < u[0] <= t_arr]
                        yield (_process(t0, t_arr, snap0, snap,
                                        seg_turns, k0, akind),
                               t0, t_arr)
                        buf = [u for u in buf if u[0] > t_arr]
                    cur_arr = (t_arr, snap, akind)
                    pend = None
        tape[pos] = w
        lo = min(lo, pos)
        lastd = d
        pos += 1 if d == 'R' else -1
        st = ns


def _process(t0, t1, snap0, snap1, seg_turns, kind0, kind1):
    tp0, lo0, p0, st0, r0 = snap0
    tp1, lo1, p1, st1, r1 = snap1
    base = lo1
    hi0 = max([p for p in tp0 if tp0[p]] + [p0])
    hi1 = max([p for p in tp1 if tp1[p]] + [p1])
    s_in = cellstr(tp0, lo1, max(p0, hi0))
    s_out = cellstr(tp1, lo1, max(p1, hi1))
    rec = dict(t=t0, dt=t1 - t0, arr_in=(st0, r0),
               arr_out=(st1, r1), s_in=s_in, s_out=s_out,
               poff_in=p0 - base, poff_out=p1 - base,
               kind=kind0, kind_next=kind1)
    if kind0 == 'full':
        far = next((u for u in seg_turns
                    if u[4] == 'm' and u[1] < lo0), None)
    else:
        far = next((u for u in seg_turns
                    if u[4] == 'm' and p0 - u[1] >= MINI_DEPTH), None)
    if far is None:
        return None
    fl = far[1] - base
    if kind0 == 'mini' and s_in[:fl] != s_out[:fl]:
        return None
    maxima = [u for u in seg_turns if u[4] == 'M'
              and far[0] < u[0] < t1]
    minima = [u for u in seg_turns if u[4] == 'm'
              and u[0] > far[0]]
    events = []
    prevp = prevt = None
    prev_trail = far[1] - 1
    mi = 0
    head = None
    for (t, p, s, r, k) in maxima:
        if prevp is not None and p <= prevp:
            break
        while mi < len(minima) and minima[mi][0] < t:
            mi += 1
        trail = minima[mi][1] if mi < len(minima) else p
        cons = (s_in[prevp - base + 1: p - base + 1]
                if prevp is not None
                else s_in[fl: p - base + 1])
        emit = s_out[prev_trail - base + 1: trail - base + 1]
        dt = t - (prevt if prevt is not None else far[0])
        if prevp is None:
            head = (f"{s}{r}", cons, emit, dt)
        else:
            events.append((f"{s}{r}", cons, emit, dt))
        prevp, prevt, prev_trail = p, t, trail
        mi += 1
    if prevp is None:
        return None
    i_tail = prevp - base + 1
    tail_cons = s_in[i_tail:]
    tail_emit = s_out[prev_trail - base + 1:]
    tail_dt = t1 - prevt
    tail_rel = p1 - prev_trail - 1
    tin = s_in[:fl] + head[1] + ''.join(e[1] for e in events) \
        + tail_cons
    tout = s_out[:fl] + head[2] + ''.join(e[2] for e in events) \
        + tail_emit
    dtsum = (far[0] - t0) + head[3] + sum(e[3] for e in events) \
        + tail_dt
    if tin != s_in or tout != s_out or dtsum != rec['dt']:
        return None
    return dict(rec=rec, shoot_dt=far[0] - t0, floor=fl, head=head,
                events=events,
                tail=(tail_cons, tail_emit, tail_dt, tail_rel))


class LiteralCalc:
    """Pure-literal calculus: no machine-specific parametrics.
    Tail rules store kind_next and the mini floor distance."""

    def __init__(self):
        self.heads = {}
        self.ctx = {}
        self.tails = {}
        self.conflicts = 0

    @staticmethod
    def _look(s, i):
        return s[i:i + 20].ljust(20, '_')

    def _put(self, table, key, val):
        if key in table and table[key] != val:
            self.conflicts += 1
            return False
        table[key] = val
        return True

    def learn(self, sg):
        rec = sg['rec']
        kind = rec['kind']
        fl = sg['floor']
        lab_h, cons_h, emit_h, dt_h = sg['head']
        self._put(self.heads, (kind, rec['arr_in'], cons_h),
                  sg['head'])
        s_in = rec['s_in']
        i = fl + len(cons_h)
        prev = 'HEAD:' + lab_h
        for ev in sg['events']:
            lab, cons, emit, dt = ev
            self._put(self.ctx, (prev, self._look(s_in, i)), ev)
            i += len(cons)
            prev = lab
        tail_cons, tail_emit, tail_dt, tail_rel = sg['tail']
        self._put(self.tails, (prev, tail_cons),
                  (tail_emit, tail_dt, rec['arr_out'], tail_rel,
                   rec['kind_next']))

    def step(self, cells, arr, poff, kind, floor):
        """floor supplied externally for minis (from extraction) --
        validation of full sweeps is self-contained."""
        fl = 0 if kind == 'full' else floor
        dt = poff - fl
        out = [cells[:fl]] if fl else []
        hit = None
        for (k, a, cons_h), val in self.heads.items():
            if k == kind and a == arr and cells.startswith(cons_h, fl):
                if hit is None or len(cons_h) > len(hit[0]):
                    hit = (cons_h, val)
        if hit is None:
            return None
        cons_h, (lab_h, _c, emit_h, dt_h) = hit
        out.append(emit_h)
        dt += dt_h
        i = fl + len(cons_h)
        prev = 'HEAD:' + lab_h
        for _ in range(len(cells) * 4 + 50):
            rest = cells[i:]
            if (prev, rest) in self.tails:
                emit_t, dt_t, arr_out, rel, kn = \
                    self.tails[(prev, rest)]
                out_len = sum(len(x) for x in out)
                out.append(emit_t)
                return (''.join(out), arr_out, dt + dt_t,
                        out_len + rel, kn)
            key = (prev, self._look(cells, i))
            if key not in self.ctx:
                return None
            lab, cons, emit, dtu = self.ctx[key]
            if cons and not cells.startswith(cons, i):
                return None
            out.append(emit)
            dt += dtu
            i += len(cons)
            prev = lab
        return None


def ladder(code, train_steps, total_steps):
    tbl = parse(code)
    gd = growth_dir(tbl)
    if gd == 'HALT':
        return dict(code=code, verdict='HALTS?')
    if gd == 'L':
        tbl = mirror(tbl)
    n_seg = n_none = 0
    calc = LiteralCalc()
    n_val = n_exact = 0
    halted = False
    for item in stream_segments(tbl, total_steps):
        if item[0] == 'HALT':
            halted = True
            break
        sg, t0, t1 = item
        if sg is None:
            n_none += 1
            continue
        n_seg += 1
        rec = sg['rec']
        if rec['t'] < train_steps:
            calc.learn(sg)
        else:
            n_val += 1
            res = calc.step(rec['s_in'], rec['arr_in'],
                            rec['poff_in'], rec['kind'], sg['floor'])
            if res is not None:
                s_out, arr_out, dt, poff, kn = res
                if (s_out == rec['s_out'] and dt == rec['dt']
                        and poff == rec['poff_out']
                        and kn == rec['kind_next']):
                    n_exact += 1
    total = n_seg + n_none
    arch = n_seg / total if total else 0.0
    return dict(code=code, mirrored=(gd == 'L'), segments=total,
                tiled=n_seg, arch=arch, conflicts=calc.conflicts,
                ctx=len(calc.ctx), tails=len(calc.tails),
                validated=n_val, exact=n_exact, halted=halted)


if __name__ == '__main__':
    machines = [
        '1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD',
        '1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE',
        '1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB',
        '1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC',
        '1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---',
        '1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB',
        '1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF',
        '1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC',
        '1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---',
        '1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE',
    ]
    for code in machines:
        r = ladder(code, 2_000_000, 4_000_000)
        if r.get('verdict'):
            print(f"{code}  {r['verdict']}")
            continue
        pct = (100 * r['exact'] / r['validated']
               if r['validated'] else 0)
        print(f"{code}  mir={int(r['mirrored'])} "
              f"segs={r['segments']:>5} tiled={r['arch']*100:5.1f}% "
              f"conflicts={r['conflicts']:>3} ctx={r['ctx']:>4} "
              f"tails={r['tails']:>3} heldout={r['exact']}/"
              f"{r['validated']} ({pct:5.1f}%)", flush=True)

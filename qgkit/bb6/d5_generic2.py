"""Dip-aware certification ladder for the nested-dip array-class
machines.

Modified copy of d5_generic.py for the two LAW-EXACT machines whose
leftward excursions carry nested unit dips (depth families 3+6k /
5+6k).  The fixed-depth segmenter loses 45-60% of segments on them;
diagnosis (2026-08-31, MINI_DEPTH=24) shows three failure modes:

  idprefix   the excursion descends past the first threshold-deep
             dip via a staircase of unit dips, so the assumed floor
             sits above the true minimum (dominant, ~60% of loss);
  nonmono    a structured rebuild dip mid-ascent (straight drop,
             cascade rebuilt from below the launch maximum) breaks
             the strictly ascending maxima chain;
  trailorder a nested V-dip revisits cells below an emitted trail.

Dip-aware changes relative to d5_generic:

  1. floor := the earliest m-turn attaining the segment's true
     minimum (not the first threshold-deep dip);
  2. shoots := the staircase surplus of the shoot (steps beyond the
     geometric distance) is a literal function of the 48-cell tape
     window above the floor (measured single-valued on both
     machines); DipCalc learns it in a fourth table and replays it
     at validation, fail-closed on unseen windows;
  3. rebuild trigger := an m-turn whose straight dip from the
     preceding maximum is >= REBUILD_DEPTH, whose rebound maximum
     stays below the launch maximum, and whose segment minimum is
     already established (>= MIN_AGE maxima old) commits a
     mini-arrival at the launch maximum: nested rebuilds are
     restarts at every depth, not only above MINI_DEPTH;
  4. chain restart := when the maxima chain breaks (non-ascending
     maximum or descending trail) the head/event chain restarts at
     the breaking maximum, folding the post-floor spike into the
     head rule (coverage and step counts still checked exactly);
  5. tail cap := segments whose cascade collapses into a memorized
     tail chunk longer than TAIL_CAP fail closed.

Everything else (literal 20-cell context rules, exact tiling
identities, held-out exact validation) is inherited from d5_generic.
"""
import sys
from collections import Counter

from d5_generic import parse, mirror, growth_dir, cellstr, \
    LiteralCalc

MINI_DEPTH = 24     # plunge trigger, as in d5_generic
REBUILD_DEPTH = 4   # rebuild trigger: minimum straight dip
MIN_AGE = 4         # rebuild trigger: maxima since last new minimum
SHOOT_WIN = 48      # shoot-surplus window above the floor
TAIL_CAP = 64       # maximum literal tail length
MAX_RESTART = 8     # chain restarts per segment
ENABLE_T2 = False   # rebuild trigger (ablation: injects a second,
                    # ambiguous vocabulary; net negative; off)
ENABLE_RESTART = False  # chain restart (ablation: net negative; off)
ENABLE_RESUME = True    # resume chain at next record maximum


def stream_segments(tbl, steps):
    tape = {}
    pos, st = 0, 'A'
    lastd = None
    lo = 0
    buf = []
    pend = None
    cur_arr = None
    seg_min = None      # running minimum of the current segment
    min_age = 0         # maxima seen since seg_min last decreased
    t2cand = None       # (launch pend, launch age) armed rebuild
    for t in range(steps):
        r = tape.get(pos, 0)
        tr = tbl[(st, r)]
        if tr is None:
            yield ('HALT', t, None)
            return
        w, d, ns = tr

        def commit(arr_pend, akind):
            nonlocal cur_arr, buf, seg_min, min_age, t2cand
            snap = (arr_pend[4], arr_pend[5], arr_pend[1],
                    arr_pend[2], arr_pend[3])
            t_arr = arr_pend[0]
            out = None
            if cur_arr is not None:
                t0, snap0, k0 = cur_arr
                seg_turns = [u for u in buf if t0 < u[0] <= t_arr]
                out = (_process(t0, t_arr, snap0, snap,
                                seg_turns, k0, akind), t0, t_arr)
                buf = [u for u in buf if u[0] > t_arr]
            cur_arr = (t_arr, snap, akind)
            seg_min = None
            min_age = 0
            t2cand = None
            return out

        if lastd is not None and d != lastd:
            kind = 'M' if lastd == 'R' else 'm'
            buf.append((t, pos, st, r, kind))
            if kind == 'M':
                min_age += 1
                if (ENABLE_T2 and t2cand is not None
                        and pos < t2cand[0][1]
                        and t2cand[1] >= MIN_AGE):
                    out = commit(t2cand[0], 'mini')
                    if out is not None:
                        yield out
                t2cand = None
                pend = (t, pos, st, r, dict(tape), lo)
            else:
                launch = pend
                akind = None
                if pos < lo:
                    akind = 'full'
                elif (launch is not None
                        and launch[1] - pos >= MINI_DEPTH):
                    akind = 'mini'
                if akind is not None:
                    out = commit(launch, akind)
                    pend = None
                    if out is not None:
                        yield out
                elif (launch is not None
                        and launch[1] - pos >= REBUILD_DEPTH
                        and cur_arr is not None
                        and launch[1] <= cur_arr[1][2] - MINI_DEPTH):
                    t2cand = (launch, min_age)
                if seg_min is None or pos < seg_min:
                    seg_min = pos
                    min_age = 0
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
    minima = [u for u in seg_turns if u[4] == 'm']
    if not minima:
        return None, 'no_far'
    fmin = min(u[1] for u in minima)
    far = next(u for u in minima if u[1] == fmin)
    if kind0 == 'full':
        if fmin >= lo0:
            return None, 'no_far'
    else:
        if p0 - fmin < 3:
            return None, 'no_far'
    fl = far[1] - base
    if kind0 == 'mini' and s_in[:fl] != s_out[:fl]:
        return None, 'idprefix'
    shoot_extra = (far[0] - t0) - (p0 - far[1])
    maxima = [u for u in seg_turns if u[4] == 'M'
              and far[0] < u[0] < t1]
    aftmin = [u for u in minima if u[0] > far[0]]
    events = []
    prevp = prevt = None
    prev_trail = far[1] - 1
    mi = 0
    head = None
    restarts = 0
    for (t, p, s, r, k) in maxima:
        while mi < len(aftmin) and aftmin[mi][0] < t:
            mi += 1
        trail = aftmin[mi][1] if mi < len(aftmin) else p
        if head is not None and (p <= prevp or trail < prev_trail):
            if ENABLE_RESUME and p <= prevp:
                continue    # fold the rebuild into the next record
            if not ENABLE_RESTART:
                if p <= prevp:
                    break
                return None, 'trail_order'
            # nested structure: restart the chain at this maximum,
            # folding everything so far into the head rule
            restarts += 1
            if restarts > MAX_RESTART:
                return None, 'restart_cap'
            head = None
            events = []
            prevp = prevt = None
            prev_trail = far[1] - 1
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
    if head is None:
        return None, 'no_maxima'
    i_tail = prevp - base + 1
    tail_cons = s_in[i_tail:]
    if len(tail_cons) > TAIL_CAP:
        return None, 'long_tail'
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
        return None, 'tiling'
    return dict(rec=rec, shoot_dt=far[0] - t0, floor=fl, head=head,
                shoot_extra=shoot_extra, events=events,
                tail=(tail_cons, tail_emit, tail_dt, tail_rel)), 'ok'


class DipCalc(LiteralCalc):
    """LiteralCalc plus a shoots table: the staircase surplus of the
    shoot (extra steps beyond the geometric arrival-to-floor
    distance) keyed by the SHOOT_WIN-cell tape window above the
    floor.  Fail-closed: validation returns None on unseen windows.
    Everything else inherited verbatim."""

    def __init__(self):
        super().__init__()
        self.shoots = {}

    @staticmethod
    def _swin(s, fl):
        return s[fl:fl + SHOOT_WIN].ljust(SHOOT_WIN, '_')

    def learn(self, sg):
        rec = sg['rec']
        self._put(self.shoots,
                  (rec['kind'], rec['arr_in'],
                   self._swin(rec['s_in'], sg['floor'])),
                  sg['shoot_extra'])
        super().learn(sg)

    def step(self, cells, arr, poff, kind, floor):
        fl = 0 if kind == 'full' else floor
        key = (kind, arr, self._swin(cells, fl))
        if key not in self.shoots:
            return None
        extra = self.shoots[key]
        res = super().step(cells, arr, poff, kind, floor)
        if res is None:
            return None
        s_out, arr_out, dt, poff_out, kn = res
        return s_out, arr_out, dt + extra, poff_out, kn


def ladder(code, train_steps, total_steps):
    tbl = parse(code)
    gd = growth_dir(tbl)
    if gd == 'HALT':
        return dict(code=code, verdict='HALTS?')
    if gd == 'L':
        tbl = mirror(tbl)
    n_seg = n_none = 0
    causes = Counter()
    calc = DipCalc()
    n_val = n_exact = 0
    fails = []
    halted = False
    for item in stream_segments(tbl, total_steps):
        if item[0] == 'HALT':
            halted = True
            break
        (sg, cause), t0, t1 = item
        causes[cause] += 1
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
                else:
                    fails.append(('mismatch', rec['t']))
            else:
                fails.append(('no_rule', rec['t']))
    total = n_seg + n_none
    arch = n_seg / total if total else 0.0
    return dict(code=code, mirrored=(gd == 'L'), segments=total,
                tiled=n_seg, arch=arch, causes=dict(causes),
                conflicts=calc.conflicts,
                ctx=len(calc.ctx), tails=len(calc.tails),
                shoots=len(calc.shoots),
                validated=n_val, exact=n_exact, fails=fails[:20],
                n_fail=len(fails), halted=halted)


if __name__ == '__main__':
    machines = [
        '1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC',
        '1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB',
    ]
    train = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
    total = int(sys.argv[2]) if len(sys.argv) > 2 else 4_000_000
    for label, cap in (('LAW  (tail<=64)', 64),
                       ('COVER (no cap) ', 10 ** 9)):
        globals()['TAIL_CAP'] = cap
        print(f"== operating point: {label} ==")
        for code in machines:
            r = ladder(code, train, total)
            if r.get('verdict'):
                print(f"{code}  {r['verdict']}")
                continue
            pct = (100 * r['exact'] / r['validated']
                   if r['validated'] else 0)
            print(f"{code}  mir={int(r['mirrored'])} "
                  f"segs={r['segments']:>5} "
                  f"tiled={r['arch']*100:5.1f}% "
                  f"conflicts={r['conflicts']:>3} "
                  f"ctx={r['ctx']:>4} "
                  f"tails={r['tails']:>3} shoots={r['shoots']:>3} "
                  f"heldout={r['exact']}/"
                  f"{r['validated']} ({pct:5.1f}%)", flush=True)
            print(f"  causes={r['causes']}")
            if r['fails']:
                print(f"  first validation failures: "
                      f"{r['fails'][:8]}")

"""Bidirectional certification ladder for two-sided array-class machines.

Architecture copied from d5_generic.py, re-targeted at machines whose
extremes both advance persistently and whose full traversals strictly
alternate ends.  Boundaries are arrivals at either extreme: a turn at a
position at or beyond the current record extreme on that side.  Two
sub-segment kinds arise between consecutive boundaries:

  X (cross)  : consecutive boundaries on opposite ends -- one full
               traversal sweep; the whole word is rewritten.
  B (burst)  : consecutive boundaries on the same end -- one record
               advance inside a burst; a bounded excursion below the
               arrival end, identity prefix below its floor.

A full traversal in the sense of the alternating-frontier anatomy is
one X followed by the run of Bs at its destination end; the
configuration is the whole word between extremes plus the active end.

Every sub-segment is tiled by the d5_generic max-turn unit walk in an
oriented frame that always reads left-to-right with the arrival end on
the right: B at the right end and X starting at the left end use the
real orientation, the mirror cases use the reversed cell string.  X is
the degenerate case of the d5_generic walk with floor 0 and the far
turn at the start boundary itself.  Unit tiling, literal-calculus
learning and held-out validation are otherwise exactly the d5_generic
pipeline.  All rungs fail-closed: any sub-segment that does not tile
exactly is counted and sampled, never absorbed; held-out validation
demands exact word, step count, arrival, head offset and next kind.

As in d5_generic, held-out validation of B sub-segments receives the
floor and the incoming head offset from extraction; the step count of
the downward shoot is derived as the head-to-floor distance and fails
closed through the dt comparison when the shoot is not straight.
"""
import json
import sys
from collections import Counter

LOOK = 20


def parse(code):
    tbl = {}
    for i, blk in enumerate(code.split('_')):
        st = chr(ord('A') + i)
        for r in (0, 1):
            e = blk[3 * r:3 * r + 3]
            tbl[(st, r)] = (None if e == '---'
                            else (int(e[0]), e[1], e[2]))
    return tbl


def cellstr(tp, a, b):
    return ''.join('#' if tp.get(p) else '.' for p in range(a, b + 1))


import os

CUT = LOOK        # split units whose consumed span exceeds this
SPLIT = bool(int(os.environ.get('D5_SPLIT', '0')))
                  # cruise micro-rule experiment (see results doc):
                  # exact by construction, but emission finality
                  # depends on future backtrack depth, so the rules
                  # conflict; kept as the diagnostic that pins the
                  # residual failure mode.


def _resim_states(tbl, tp0, p0, st0, nsteps):
    """Replay a segment from its entry snapshot, returning the state
    before each step.  Used only to label cruise micro-rules; all
    words, windows and step counts come from the turn algebra."""
    tape = dict(tp0)
    pos, st = p0, st0
    arr = []
    for _ in range(nsteps + 1):
        arr.append(st)
        r = tape.get(pos, 0)
        w, d, ns = tbl[(st, r)]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        st = ns
    return arr


def stream_subsegments(tbl, steps):
    """Yield ((seg, reason), t0, t1) per pair of consecutive record
    boundaries, with one boundary of lookahead so each segment knows
    the kind of its successor.  Snapshots are taken before the turn
    step writes its cell, exactly as in d5_generic."""
    tape = {}
    pos, st = 0, 'A'
    lastd = None
    lo = hi = 0
    buf = []
    b0 = b1 = None       # last two boundaries
    seg_turns1 = None    # turns of the pending (b0,b1) segment
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
            side = None
            if kind == 'M' and pos >= hi:
                side = 'R'
            elif kind == 'm' and pos <= lo:
                side = 'L'
            if side is not None:
                cand = (side, t, pos, st, r, dict(tape), lo, hi)
                if b1 is not None:
                    if b0 is not None:
                        nxt = ('B' if cand[0] == b1[0] else 'X')
                        yield (_process(tbl, b0, b1, seg_turns1,
                                        nxt), b0[1], b1[1])
                    seg_turns1 = [u for u in buf
                                  if b1[1] < u[0] <= t]
                    buf = [u for u in buf if u[0] > t]
                b0, b1 = b1, cand
        tape[pos] = w
        lastd = d
        pos += 1 if d == 'R' else -1
        lo = min(lo, pos)
        hi = max(hi, pos)
        st = ns


def _chain(spec, window, dip_width):
    """Distribute an emission window over chain pieces, forward
    aligned with the physical writes: a zero-cons dip piece takes the
    below-anchor share (dip_width cells), each consuming piece takes
    the window cell at its own position while the window lasts, and
    any window remainder past the consumed span rides on the last
    piece.  spec: [(label, cons, dt)]; returns 4-tuples."""
    pieces = []
    w = 0
    for (lab, cons, dt) in spec:
        if not cons:
            take = min(max(dip_width, 0), len(window) - w)
            pieces.append((lab, cons, window[w:w + take], dt))
            w += take
            continue
        em = []
        for _ in range(len(cons)):
            em.append(window[w] if w < len(window) else '')
            w += 1 if w < len(window) else 0
        pieces.append((lab, cons, ''.join(em), dt))
    if w < len(window):
        lab, cons, e, dt = pieces[-1]
        pieces[-1] = (lab, cons, e + window[w:], dt)
    return pieces


def _split_units(tbl, a0, rec, fl, far_t, head, events, aux):
    """Split units whose consumed span exceeds CUT into one-cell
    cruise micro-rules labeled by the machine state at each
    leading-edge crossing.  Consecutive turns bound straight legs, so
    all times are exact turn algebra; a lazy replay of the segment
    supplies the states.  Exactness is preserved by construction: the
    pieces of each unit concatenate to the unit's own cons, emit and
    dt.  Returns (new_head, new_events)."""
    units = [head] + events
    if not SPLIT or not any(len(u[1]) > CUT for u in units):
        return head, events
    t0 = rec['t']
    states = _resim_states(tbl, a0[5], a0[2], a0[3], rec['dt'])
    s_in = rec['s_in']
    out_head = None
    out_events = []
    prevp = None
    prevt = None
    pt = fl - 1     # absolute oriented position of the previous trail
    for idx, (u, (t_abs, po)) in enumerate(zip(units, aux)):
        lab, cons, emit, dtu = u
        c = len(cons)
        splittable = (c > CUT
                      and ((idx == 0 and dtu == c - 1)
                           or (idx > 0 and dtu >= c
                               and (dtu - c) % 2 == 0)))
        if not splittable:
            if idx == 0:
                out_head = u
            else:
                out_events.append(u)
            prevp, prevt = po, t_abs
            pt += len(emit)
            continue
        if idx == 0:
            # ascent from the floor: straight leg, dt == c - 1.
            start = fl
            t_cross0 = far_t          # time cell `start` is processed
            spec = [(None, cons[:CUT], CUT)]
            j0 = start + CUT
        else:
            depth = (dtu - c) // 2
            m = prevp - depth
            t_min = prevt + depth
            start = prevp + 1
            t_cross0 = t_min + (start - m)
            spec = [(f'DIP:{lab}', '', 2 * depth)]
            j0 = start
        for j in range(j0, po + 1):
            tc = t_cross0 + (j - start) if idx else far_t + (j - fl)
            if j == po:
                spec.append((lab, s_in[j], 1 if idx else 0))
            else:
                spec.append(('CR:' + states[tc + 1 - t0],
                             s_in[j], 1))
        if idx == 0:
            # first piece label: state after its consumed cells.
            spec[0] = ('CR:' + states[far_t + CUT - t0],
                       spec[0][1], spec[0][2])
            dip_w = 0
        else:
            dip_w = prevp - pt
        pieces = _chain(spec, emit, dip_w)
        if idx == 0:
            out_head = pieces[0]
            out_events.extend(pieces[1:])
        else:
            out_events.extend(pieces)
        prevp, prevt = po, t_abs
        pt += len(emit)
    return out_head, out_events


def _process(tbl, a0, a1, turns, kind_next):
    """Tile one sub-segment in its oriented frame.  Returns
    (seg_dict_or_None, reason); seg_dict carries rec always, and unit
    data plus ok=True only when the tiling telescopes exactly."""
    side0, t0, p0, st0, r0, tp0, lo0, hi0 = a0
    side1, t1, p1, st1, r1, tp1, lo1, hi1 = a1
    kind = 'B' if side0 == side1 else 'X'
    if kind == 'B':
        # arrival end on the oriented right; frame anchored at the
        # untouched far extreme.
        if side0 == 'R':
            base, top = lo0, max(hi0, p1)
            o = lambda p: p - base
            real = True
        else:
            base, top = min(lo0, p1), hi0
            o = lambda p: top - p
            real = False
        maxk = 'M' if real else 'm'
    else:
        # traversal frame: start end at oriented 0, far end grows.
        if side0 == 'L':
            base, top = lo0, max(hi0, p1)
            o = lambda p: p - base
            real = True
        else:
            base, top = min(lo0, p1), hi0
            o = lambda p: top - p
            real = False
        maxk = 'M' if real else 'm'
    n = top - base + 1

    def ocell(tp):
        s = cellstr(tp, base, top)
        return s if real else s[::-1]

    s_in = ocell(tp0)
    s_out = ocell(tp1)
    poff_in = o(p0)
    poff_out = o(p1)
    rec = dict(t=t0, dt=t1 - t0, kind=kind, side=side0,
               side_next=side1, kind_next=kind_next,
               arr_in=(st0, r0), arr_out=(st1, r1),
               s_in=s_in, s_out=s_out,
               poff_in=poff_in, poff_out=poff_out)
    if kind == 'X' and (poff_in != 0 or poff_out != n - 1):
        return None, 'head-not-at-extreme'
    if kind == 'B' and poff_out != n - 1:
        return None, 'head-not-at-extreme'
    omax = [(t, o(p), s, r) for (t, p, s, r, k) in turns
            if k == maxk and t < t1]
    omin = [(t, o(p)) for (t, p, s, r, k) in turns
            if k != maxk and t < t1]
    if kind == 'B':
        if not omin:
            return None, 'no-far'
        far = min(omin, key=lambda u: (u[1], u[0]))
        far_t, fl = far
    else:
        far_t, fl = t0, 0
    if s_in[:fl] != s_out[:fl]:
        return dict(rec=rec, ok=False, floor=fl), 'floor-dirty'
    rec['floor'] = fl
    events = []
    head = None
    prevp = prevt = None
    prev_trail = fl - 1
    mi = 0
    omin_after = [u for u in omin if u[0] > far_t]
    # suffix minima over later returns: the trail of a leading turn is
    # the deepest position any later return reaches; cells strictly
    # below it are final from that moment on.  Suffix minima are
    # monotone in time, so emission windows tile by construction and
    # nested backtracks are attributed exactly.
    sfx = [0] * len(omin_after)
    m = 10 ** 9
    for i in range(len(omin_after) - 1, -1, -1):
        m = min(m, omin_after[i][1])
        sfx[i] = m
    march_break = False
    aux = []
    for (t, po, s, r) in omax:
        if t <= far_t:
            continue
        if prevp is not None and po <= prevp:
            march_break = True
            break
        while mi < len(omin_after) and omin_after[mi][0] < t:
            mi += 1
        trail = sfx[mi] if mi < len(omin_after) else po
        cons = (s_in[prevp + 1: po + 1] if prevp is not None
                else s_in[fl: po + 1])
        emit = s_out[prev_trail + 1: trail + 1]
        dt = t - (prevt if prevt is not None else far_t)
        unit = (f"{s}{r}", cons, emit, dt)
        aux.append((t, po))
        if prevp is None:
            head = unit
        else:
            events.append(unit)
        prevp, prevt, prev_trail = po, t, trail
    rec['march_break'] = march_break
    shoot_dt = far_t - t0
    if head is None:
        # excursion with no interior maximum: whole body literal.
        rec['shoot_lin'] = (shoot_dt == poff_in - fl)
        return dict(rec=rec, ok=True, direct=True, floor=fl,
                    shoot_dt=shoot_dt), 'direct'
    tail_cons = s_in[prevp + 1:]
    tail_emit = s_out[prev_trail + 1:]
    tail_dt = t1 - prevt
    tail_rel = poff_out - prev_trail - 1
    tin = s_in[:fl] + head[1] + ''.join(e[1] for e in events) \
        + tail_cons
    tout = s_out[:fl] + head[2] + ''.join(e[2] for e in events) \
        + tail_emit
    dtsum = shoot_dt + head[3] + sum(e[3] for e in events) + tail_dt
    if tin != s_in:
        return dict(rec=rec, ok=False, floor=fl), 'tile-in'
    if tout != s_out:
        return dict(rec=rec, ok=False, floor=fl), 'tile-out'
    if dtsum != rec['dt']:
        return dict(rec=rec, ok=False, floor=fl), 'tile-dt'
    rec['shoot_lin'] = (shoot_dt == poff_in - fl)
    units = [head] + events
    rec['n_units'] = len(units) + 1
    rec['long_units'] = sum(1 for u in units if len(u[1]) > LOOK) \
        + (1 if len(tail_cons) > LOOK else 0)
    head, events = _split_units(tbl, a0, rec, fl, t0 + shoot_dt,
                                head, events, aux)
    tin = s_in[:fl] + head[1] + ''.join(e[1] for e in events) \
        + tail_cons
    tout = s_out[:fl] + head[2] + ''.join(e[2] for e in events) \
        + tail_emit
    dtsum = shoot_dt + head[3] + sum(e[3] for e in events) + tail_dt
    if tin != s_in or tout != s_out or dtsum != rec['dt']:
        return dict(rec=rec, ok=False, floor=fl), 'split-broken'
    return dict(rec=rec, ok=True, direct=False, floor=fl,
                shoot_dt=shoot_dt,
                shoot_extra=shoot_dt - (poff_in - fl),
                head=head, events=events,
                tail=(tail_cons, tail_emit, tail_dt, tail_rel)), 'ok'


class BidirCalc:
    """Pure-literal calculus.  Every table key carries (kind, side):
    the same machine label reads the tape mirrored in the two frames
    and must never share a rule."""

    def __init__(self):
        self.heads = {}
        self.ctx = {}
        self.tails = {}
        self.direct = {}
        self.conflicts = 0

    @staticmethod
    def _look(s, i):
        return s[i:i + LOOK].ljust(LOOK, '_')

    def _put(self, table, key, val):
        if key in table and table[key] != val:
            self.conflicts += 1
            return False
        table[key] = val
        return True

    def learn(self, sg):
        rec = sg['rec']
        ks = (rec['kind'], rec['side'])
        fl = sg['floor']
        if sg['direct']:
            self._put(self.direct, (ks, rec['arr_in'],
                                    rec['s_in'][fl:]),
                      (rec['s_out'][fl:],
                       rec['dt'] - (rec['poff_in'] - fl),
                       rec['arr_out'], rec['poff_out'] - fl,
                       rec['kind_next']))
            return
        lab_h, cons_h, emit_h, dt_h = sg['head']
        self._put(self.heads, (ks, rec['arr_in'], cons_h),
                  sg['head'] + (sg['shoot_extra'],))
        s_in = rec['s_in']
        i = fl + len(cons_h)
        prev = 'HEAD:' + lab_h
        for ev in sg['events']:
            lab, cons, emit, dtu = ev
            self._put(self.ctx, (ks, prev, self._look(s_in, i)), ev)
            i += len(cons)
            prev = lab
        tail_cons, tail_emit, tail_dt, tail_rel = sg['tail']
        self._put(self.tails, (ks, prev, tail_cons),
                  (tail_emit, tail_dt, rec['arr_out'], tail_rel,
                   rec['kind_next']))

    def step(self, cells, arr, ks, poff, floor):
        """(oriented word, arrival, (kind, side)) -> (word', arrival',
        dt, poff', kind_next) or (None, reason).  floor and poff are
        supplied externally for B sub-segments, as in d5_generic; the
        shoot cost is derived as poff - floor."""
        fl = 0 if ks[0] == 'X' else floor
        dt = poff - fl
        dkey = (ks, arr, cells[fl:])
        if dkey in self.direct:
            emit, dt_d, arr_out, rel, kn = self.direct[dkey]
            return (cells[:fl] + emit, arr_out, dt + dt_d,
                    fl + rel, kn), 'ok'
        hit = None
        for (k, a, cons_h), val in self.heads.items():
            if k == ks and a == arr and cells.startswith(cons_h, fl):
                if hit is None or len(cons_h) > len(hit[0]):
                    hit = (cons_h, val)
        if hit is None:
            return None, 'no-head'
        cons_h, (lab_h, _c, emit_h, dt_h, extra) = hit
        out = [cells[:fl]] if fl else []
        out.append(emit_h)
        dt += dt_h + extra
        i = fl + len(cons_h)
        prev = 'HEAD:' + lab_h
        for _ in range(len(cells) * 4 + 50):
            rest = cells[i:]
            if (ks, prev, rest) in self.tails:
                emit_t, dt_t, arr_out, rel, kn = \
                    self.tails[(ks, prev, rest)]
                out_len = sum(len(x) for x in out)
                out.append(emit_t)
                return (''.join(out), arr_out, dt + dt_t,
                        out_len + rel, kn), 'ok'
            key = (ks, prev, self._look(cells, i))
            if key not in self.ctx:
                return None, 'no-ctx'
            lab, cons, emit, dtu = self.ctx[key]
            if cons and not cells.startswith(cons, i):
                return None, 'cons-mismatch'
            out.append(emit)
            dt += dtu
            i += len(cons)
            prev = lab
        return None, 'loop-limit'


def ladder(code, train_steps, total_steps, collect=False,
           max_samples=4):
    tbl = parse(code)
    calc = BidirCalc()
    seg_n = Counter()
    seg_tiled = Counter()
    n_direct = 0
    n_val = Counter()
    n_exact = Counter()
    untiled_reasons = Counter()
    val_fail = Counter()
    untiled_samples = []
    fail_samples = []
    shoot_nonlin = 0
    march_breaks = 0
    long_units = tot_units = 0
    words = [] if collect else None
    halted = False
    # traversal-level bookkeeping: an X opens a traversal, the run of
    # Bs after it belongs to that traversal.
    trav_total = trav_tiled = trav_val = trav_exact = 0
    cur_ok = cur_exact = cur_heldout = None
    for item in stream_subsegments(tbl, total_steps):
        if item[0] == 'HALT':
            halted = True
            break
        (sg, reason), t0, t1 = item
        kind = sg['rec']['kind'] if sg is not None else '?'
        if kind == 'X' or sg is None:
            if cur_ok is not None:
                trav_total += 1
                trav_tiled += cur_ok
                if cur_heldout:
                    trav_val += 1
                    trav_exact += (cur_ok and cur_exact)
            cur_ok, cur_exact, cur_heldout = True, True, False
        if sg is None:
            seg_n[kind] += 1
            untiled_reasons[reason] += 1
            cur_ok = False
            if len(untiled_samples) < max_samples:
                untiled_samples.append(dict(t0=t0, t1=t1,
                                            reason=reason))
            continue
        rec = sg['rec']
        seg_n[kind] += 1
        if collect:
            words.append((rec['t'], rec['dt'], kind, rec['side'],
                          rec['s_in'], rec['s_out']))
        if not sg['ok']:
            untiled_reasons[reason] += 1
            cur_ok = False
            if len(untiled_samples) < max_samples:
                untiled_samples.append(dict(
                    t0=t0, reason=reason, kind=kind,
                    side=rec['side'], n=len(rec['s_out']),
                    dt=rec['dt'], floor=sg.get('floor')))
            continue
        seg_tiled[kind] += 1
        if sg.get('direct'):
            n_direct += 1
        if not rec.get('shoot_lin', True):
            shoot_nonlin += 1
        if rec.get('march_break'):
            march_breaks += 1
        long_units += rec.get('long_units', 0)
        tot_units += rec.get('n_units', 1)
        if rec['t'] < train_steps:
            calc.learn(sg)
        else:
            n_val[kind] += 1
            cur_heldout = True
            res, why = calc.step(rec['s_in'], rec['arr_in'],
                                 (kind, rec['side']),
                                 rec['poff_in'], sg['floor'])
            ok = False
            if res is None:
                val_fail[kind + ':' + why] += 1
                if len(fail_samples) < max_samples * 2:
                    fail_samples.append(dict(
                        t0=t0, why=why, kind=kind, side=rec['side'],
                        n=len(rec['s_in']), dt=rec['dt'],
                        floor=sg['floor'],
                        win=rec['s_in'][max(0, sg['floor'] - 4):
                                        sg['floor'] + 24]))
            else:
                s_out, arr_out, dt, poff, kn = res
                bad = []
                if s_out != rec['s_out']:
                    bad.append('word')
                if dt != rec['dt']:
                    bad.append('dt')
                if arr_out != rec['arr_out']:
                    bad.append('arr')
                if poff != rec['poff_out']:
                    bad.append('poff')
                if kn != rec['kind_next']:
                    bad.append('kindnext')
                if bad:
                    why = 'mismatch:' + '+'.join(bad)
                    val_fail[kind + ':' + why] += 1
                    if len(fail_samples) < max_samples * 2:
                        fail_samples.append(dict(
                            t0=t0, why=why, kind=kind,
                            side=rec['side'], n=len(rec['s_in']),
                            dt=rec['dt'], dt_pred=dt))
                else:
                    ok = True
                    n_exact[kind] += 1
            if not ok:
                cur_exact = False
    total = sum(seg_n.values())
    tiled = sum(seg_tiled.values())
    vald = sum(n_val.values())
    exact = sum(n_exact.values())
    return dict(code=code, segments=total, tiled=tiled,
                arch=(tiled / total if total else 0.0),
                by_kind={k: (seg_tiled[k], seg_n[k]) for k in seg_n},
                direct=n_direct, shoot_nonlin=shoot_nonlin,
                march_breaks=march_breaks, long_units=long_units,
                tot_units=tot_units,
                conflicts=calc.conflicts, heads=len(calc.heads),
                ctx=len(calc.ctx), tails=len(calc.tails),
                directs=len(calc.direct),
                validated=vald, exact=exact,
                val_by_kind={k: (n_exact[k], n_val[k])
                             for k in n_val},
                trav=dict(total=trav_total, tiled=trav_tiled,
                          validated=trav_val, exact=trav_exact),
                untiled_reasons=dict(untiled_reasons),
                val_fail=dict(val_fail),
                untiled_samples=untiled_samples,
                fail_samples=fail_samples,
                words=words, halted=halted)


def _traversals(words):
    """Fold a sub-segment stream into traversal summaries:
    (from_side, n_bursts, word_len_at_X, t_X, dt_total)."""
    out = []
    cur = None
    for (t, dt, kind, side, s_in, s_out) in words:
        if kind == 'X':
            if cur is not None:
                out.append(tuple(cur))
            cur = [side, 0, len(s_in), t, dt]
        elif cur is not None:
            cur[1] += 1
            cur[4] += dt
    if cur is not None:
        out.append(tuple(cur))
    return out


def twin_check(r0, r1):
    """Align the two traversal streams (early transients may offset
    them) and compare burst-run structure, word lengths, step counts
    and raw words."""
    tv0 = _traversals(r0['words'])
    tv1 = _traversals(r1['words'])
    key0 = [(s, b) for (s, b, _n, _t, _dt) in tv0]
    key1 = [(s, b) for (s, b, _n, _t, _dt) in tv1]
    best = (-1, 0)
    for shift in range(-40, 41):
        m = sum(1 for i in range(len(key0))
                if 0 <= i + shift < len(key1)
                and key0[i] == key1[i + shift])
        if m > best[0]:
            best = (m, shift)
    m, shift = best
    pairs = [(i, i + shift) for i in range(len(key0))
             if 0 <= i + shift < len(key1)]
    same_burst = sum(1 for i, j in pairs if key0[i] == key1[j])
    dlen = Counter(tv1[j][2] - tv0[i][2] for i, j in pairs)
    ddt = Counter(tv1[j][4] - tv0[i][4] for i, j in pairs)
    # raw word comparison at aligned X boundaries: common prefix and
    # suffix lengths localize where the realizations differ.
    x0 = [w for w in r0['words'] if w[2] == 'X']
    x1 = [w for w in r1['words'] if w[2] == 'X']
    same_word = 0
    cap = Counter()
    for i, j in pairs:
        a, b = x0[i][4], x1[j][4]
        side = x0[i][3]
        if a == b:
            same_word += 1
            continue
        n = min(len(a), len(b))
        cp = 0
        while cp < n and a[cp] == b[cp]:
            cp += 1
        cs = 0
        while cs < n - cp and a[-1 - cs] == b[-1 - cs]:
            cs += 1
        cap[(side, n - cp, n - cs)] += 1
    return dict(n_trav=(len(tv0), len(tv1)), shift=shift,
                aligned=len(pairs), same_burst_run=same_burst,
                dlen_top=dlen.most_common(3),
                ddt_top=ddt.most_common(3),
                same_word=same_word,
                cap_top=cap.most_common(6))


MACHINES = [
    '1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD',
    '1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE',
    '1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---',
    '1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF',
    '1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC',
]


def main(train=2_000_000, total=4_000_000,
         out='/tmp/d5_bidir_results.json'):
    results = []
    for idx, code in enumerate(MACHINES):
        r = ladder(code, train, total, collect=(idx < 2))
        results.append(r)
        pct = (100 * r['exact'] / r['validated']
               if r['validated'] else 0.0)
        tv = r['trav']
        tpct = (100 * tv['exact'] / tv['validated']
                if tv['validated'] else 0.0)
        print(f"{code}\n"
              f"  segs={r['segments']:>6} tiled={r['arch']*100:5.1f}%"
              f" by_kind={dict(r['by_kind'])} direct={r['direct']}"
              f" shootnl={r['shoot_nonlin']}"
              f" marchbrk={r['march_breaks']}"
              f" longunits={r['long_units']}/{r['tot_units']}\n"
              f"  conf={r['conflicts']:>3} heads={r['heads']:>3}"
              f" ctx={r['ctx']:>4} tails={r['tails']:>4}"
              f" directs={r['directs']:>3}"
              f" heldout={r['exact']}/{r['validated']}"
              f" ({pct:5.1f}%) val_by_kind={dict(r['val_by_kind'])}\n"
              f"  traversals: total={tv['total']}"
              f" tiled={tv['tiled']}"
              f" heldout={tv['exact']}/{tv['validated']}"
              f" ({tpct:5.1f}%)", flush=True)
        if r['untiled_reasons']:
            print(f"    untiled: {r['untiled_reasons']}")
            for s in r['untiled_samples']:
                print(f"      {s}")
        if r['val_fail']:
            print(f"    valfail: {r['val_fail']}")
            for s in r['fail_samples']:
                print(f"      {s}")
    tw = twin_check(results[0], results[1])
    print(f"TWIN: {tw}", flush=True)
    for r in results:
        r.pop('words')
    with open(out, 'w') as f:
        json.dump(dict(results=results, twin=tw), f, indent=1,
                  default=str)
    return results, tw


if __name__ == '__main__':
    a = [x if '/' in x else int(x) for x in sys.argv[1:]]
    main(*(a or []))

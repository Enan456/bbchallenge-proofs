"""Dossier-5 step 1: the trisection calculus, fail-closed.

Machine: 1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC  (rank-1 array-class)

State of the calculus: the head-form word at each right-end arrival
(max-turn at the running right end): tape = 1-blocks of length 1/2/3
separated by single 0s.  One segment = left shoot to the (extended)
far end + rightward zigzag pass back.  The segment map is a sequential
transducer processed far -> head.

This module:
  1. extracts segments from raw simulation (arrival-to-arrival),
  2. learns the transducer rule set (unit tiling, fail-closed),
  3. provides predict(word) -> (word', dt, d_extreme, arrival) with
     NO fallback: unseen context raises Unexplained,
  4. validates predictor vs raw exactly over a horizon.
"""

from collections import Counter, defaultdict

CODE = '1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC'


def parse(code):
    tbl = {}
    for i, blk in enumerate(code.split('_')):
        st = chr(ord('A') + i)
        for r in (0, 1):
            e = blk[3 * r:3 * r + 3]
            tbl[(st, r)] = None if e == '---' else (int(e[0]), e[1], e[2])
    return tbl


TBL = parse(CODE)


# ----------------------------------------------------------------- raw

def raw_run(steps):
    """Single raw pass.  Returns (turns, arrival_flags, snapshots).
    turns: list of (t, pos, st, r, kind) at direction changes, kind in
    'M'/'m'.  An M-turn is an ARRIVAL iff the leftward excursion that
    follows it reaches (and extends) the running left extreme before
    the next M-turn.  snapshots: {t_of_arrival: (tape copy, lo, pos)}."""
    tape = {}
    pos, st = 0, 'A'
    lastd = None
    lo = 0
    turns = []
    pend = None                    # candidate arrival M-turn
    arrivals_t = []
    snaps = {}
    for t in range(steps):
        r = tape.get(pos, 0)
        w, d, ns = TBL[(st, r)]
        if lastd is not None and d != lastd:
            kind = 'M' if lastd == 'R' else 'm'
            turns.append((t, pos, st, r, kind))
            if kind == 'M':
                pend = (t, pos, st, r, dict(tape), lo)
            elif pend is not None and pos < lo:
                arrivals_t.append(pend[0])
                snaps[pend[0]] = (pend[4], pend[5], pend[1],
                                  pend[2], pend[3])
                pend = None
        tape[pos] = w
        lo = min(lo, pos)
        lastd = d
        pos += 1 if d == 'R' else -1
        st = ns
    return turns, arrivals_t, snaps


def arrivals(steps):
    """Yield (t, state, read, pos, tape_snapshot, lo) per arrival."""
    turns, arr_t, snaps = raw_run(steps)
    for t in arr_t:
        tp, lo, pos, st, r = snaps[t]
        yield (t, st, r, pos, tp, lo)


def cellstr(tp, a, b):
    return ''.join('#' if tp.get(p) else '.' for p in range(a, b + 1))


def word_blocks(s):
    """Cell string -> tuple of 1-block lengths; None if a 0-gap has
    length != 1 strictly inside."""
    runs = []
    import re
    if not s.strip('.'):
        return ()
    core = s.strip('.')
    lead = len(s) - len(s.lstrip('.'))
    parts = core.split('.')
    if any(p == '' for p in parts):
        return None
    return tuple(len(p) for p in parts)


# ----------------------------------------------------- segment records

def segment_records(steps):
    """List of dicts: one per segment (arrival k -> arrival k+1)."""
    arr = list(arrivals(steps))
    recs = []
    for i in range(len(arr) - 1):
        t0, st0, r0, p0, tp0, lo0 = arr[i]
        t1, st1, r1, p1, tp1, lo1 = arr[i + 1]
        s_in = cellstr(tp0, lo1, p0)     # include the cell(s) the far
        s_out = cellstr(tp1, lo1, p1)    # end will gain (lo1 <= lo0)
        recs.append(dict(t=t0, dt=t1 - t0, arr_in=(st0, r0),
                         arr_out=(st1, r1), pin=p0, pout=p1,
                         lo_in=lo0, lo_out=lo1,
                         s_in=s_in, s_out=s_out))
    return recs


# ------------------------------------------------------------- learner
#
# Transducer rules, far -> head, over cell strings.
# Core parametric rules (learned shapes, verified by tiling):
#   B-copy    : '#.'            -> '#.'              dt 12
#   B-absorb  : '#.###.'        -> '#.'              dt 8
#   B-cursor  : '##'            -> '#.'  (+mode D)   dt 12
#   D-insert  : '#.'            -> '#.###.'          dt 12
#   D-regroup : '#.#.(###.#.)^k #.' -> '(#.###.)^{k+1}'  dt 8+6k
# Boundary (learned from data, keyed literally):
#   head chunk: leading cells of s_in before the first unit
#   tail chunk: trailing cells + arrival
#
# Instead of hand-coding mode logic, we learn a context table:
#   (prev_rule_id, next6cells) -> rule_id
# and boundary tables.  Everything fail-closed.


class Unexplained(Exception):
    pass


def turns_of(trace):
    turns = []
    lastd = None
    for (t, pos, st, r, d) in trace:
        if lastd is not None and d != lastd:
            turns.append((t, pos, st, r, 'M' if lastd == 'R' else 'm'))
        lastd = d
    return turns


def extract_units_seg(steps):
    """Per arrival-segment unit tiling.  A segment runs from arrival k
    (M-turn, then left shoot to the extended far end, then rightward
    zigzag pass) to arrival k+1.  Returns per-segment dict:
      rec: s_in/s_out cell strings on [lo_out .. p] windows, dt
      shoot_dt: arrival M-turn -> far-end m-turn
      head_lab/head_in/head_dt: far-end gadget up to first max
      units: [(label, consumed_cells, dt, pos)] between maxima
      tail_in/tail_dt: last max -> next arrival
    """
    turns, arr_t, snaps = raw_run(steps)
    out = []
    for i in range(len(arr_t) - 1):
        t0, t1 = arr_t[i], arr_t[i + 1]
        tp0, lo0, p0, st0, r0 = snaps[t0]
        tp1, lo1, p1, st1, r1 = snaps[t1]
        seg_turns = [u for u in turns if t0 < u[0] <= t1]
        base = lo1
        s_in = cellstr(tp0, lo1, p0)
        s_out = cellstr(tp1, lo1, p1)
        rec = dict(t=t0, dt=t1 - t0, arr_in=(st0, r0),
                   arr_out=(st1, r1), pin=p0, pout=p1,
                   lo_in=lo0, lo_out=lo1, s_in=s_in, s_out=s_out)
        # far-end m-turn: first m-turn at pos <= lo0 (extends extreme)
        far = next((u for u in seg_turns
                    if u[4] == 'm' and u[1] <= lo0), None)
        maxima = [u for u in seg_turns
                  if u[4] == 'M' and u[0] < t1] if far else []
        maxima = ([u for u in maxima if u[0] > far[0]]
                  if far else maxima)
        units = []
        head_in = head_lab = ''
        head_dt = 0
        shoot_dt = far[0] - t0 if far else rec['dt']
        prevp = prevt = None
        for (t, p, s, r, k) in maxima:
            if prevp is None:
                head_in = s_in[:p - base + 1] if p >= base else ''
                head_lab = f"{s}{r}"
                head_dt = t - far[0]
            else:
                units.append((f"{s}{r}",
                              s_in[prevp - base + 1: p - base + 1],
                              t - prevt, p))
            prevp, prevt = p, t
        if prevp is not None:
            tail_in = s_in[prevp - base + 1:]
            tail_dt = t1 - prevt
        else:
            tail_in = s_in
            tail_dt = t1 - (far[0] if far else t0)
        out.append(dict(rec=rec, shoot_dt=shoot_dt, head_in=head_in,
                        head_lab=head_lab, head_dt=head_dt,
                        units=units, tail_in=tail_in, tail_dt=tail_dt))
    return out



def _process_segment(t0, t1, snap0, snap1, seg_turns):
    """Shared segment analysis.  Returns segdict or None (tiling/
    structure failure)."""
    tp0, lo0, p0, st0, r0 = snap0
    tp1, lo1, p1, st1, r1 = snap1
    base = lo1
    hi0 = max([p for p in tp0 if tp0[p]] + [p0])
    hi1 = max([p for p in tp1 if tp1[p]] + [p1])
    s_in = cellstr(tp0, lo1, max(p0, hi0))
    s_out = cellstr(tp1, lo1, max(p1, hi1))
    rec = dict(t=t0, dt=t1 - t0, arr_in=(st0, r0),
               arr_out=(st1, r1), pin=p0, pout=p1,
               lo_in=lo0, lo_out=lo1, s_in=s_in, s_out=s_out,
               poff_in=p0 - base, poff_out=p1 - base)
    far = next((u for u in seg_turns
                if u[4] == 'm' and u[1] < lo0), None)
    if far is None:
        return None
    maxima = [u for u in seg_turns if u[4] == 'M'
              and far[0] < u[0] < t1]
    minima = [u for u in seg_turns if u[4] == 'm'
              and u[0] > far[0]]
    events = []
    prevp = prevt = None
    prev_trail = base - 1
    mi = 0
    head = None
    floor = None
    pp = None
    tp_prev = None
    for (t, p, s, r, k) in maxima:
        if pp is not None and p <= pp:
            t_reg = tp_prev
            floor = min(u[1] for u in seg_turns if u[0] > t_reg)
            break
        pp = p
        tp_prev = t
    for (t, p, s, r, k) in maxima:
        if prevp is not None and p <= prevp:
            break
        while mi < len(minima) and minima[mi][0] < t:
            mi += 1
        if (floor is not None and mi < len(minima)
                and minima[mi][1] >= floor):
            break
        if floor is not None and mi >= len(minima):
            break
        if mi >= len(minima):
            trail = p
        else:
            trail = minima[mi][1]
        cons = (s_in[prevp - base + 1: p - base + 1]
                if prevp is not None
                else s_in[: p - base + 1])
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
    tin = head[1] + ''.join(e[1] for e in events) + tail_cons
    tout = head[2] + ''.join(e[2] for e in events) + tail_emit
    dtsum = (far[0] - t0) + head[3] + sum(e[3] for e in events) \
        + tail_dt
    if tin != s_in or tout != s_out or dtsum != rec['dt']:
        return None
    return dict(rec=rec, shoot_dt=far[0] - t0, head=head,
                events=events,
                tail=(tail_cons, tail_emit, tail_dt, tail_rel))


def stream_segments(steps):
    """Generator of segment dicts with bounded memory.  Yields
    (segdict_or_None, t0, t1) -- None on tiling/structure failure."""
    tape = {}
    pos, st = 0, 'A'
    lastd = None
    lo = 0
    buf = []                       # turns since before last arrival
    pend = None
    prev_arr = None                # (t, snapshot)
    cur_arr = None
    for t in range(steps):
        r = tape.get(pos, 0)
        w, d, ns = TBL[(st, r)]
        if lastd is not None and d != lastd:
            kind = 'M' if lastd == 'R' else 'm'
            buf.append((t, pos, st, r, kind))
            if kind == 'M':
                pend = (t, pos, st, r, dict(tape), lo)
            elif pend is not None and pos < lo:
                # arrival at pend confirmed
                snap = (pend[4], pend[5], pend[1], pend[2], pend[3])
                t_arr = pend[0]
                if cur_arr is not None:
                    t0, snap0 = cur_arr
                    seg_turns = [u for u in buf
                                 if t0 < u[0] <= t_arr]
                    yield (_process_segment(t0, t_arr, snap0, snap,
                                            seg_turns), t0, t_arr)
                    buf = [u for u in buf if u[0] > t_arr]
                cur_arr = (t_arr, snap)
                pend = None
        tape[pos] = w
        lo = min(lo, pos)
        lastd = d
        pos += 1 if d == 'R' else -1
        st = ns


def extract_full(steps):
    """Like extract_units_seg but with per-unit EMISSIONS from
    trailing-min windows, and exact input+output tiling verification.
    The word spans from (left extreme - 1) to the CONTENT frontier
    (which can exceed the head position after a mid-pass arrival);
    the head offset within the word is part of the configuration.
    Returns (segments, n_tiling_failures)."""
    turns, arr_t, snaps = raw_run(steps)
    out = []
    bad = 0
    from bisect import bisect_right, bisect_left
    turn_ts = [u[0] for u in turns]
    for i in range(len(arr_t) - 1):
        t0, t1 = arr_t[i], arr_t[i + 1]
        tp0, lo0, p0, st0, r0 = snaps[t0]
        tp1, lo1, p1, st1, r1 = snaps[t1]
        seg_turns = turns[bisect_right(turn_ts, t0):
                          bisect_right(turn_ts, t1)]
        base = lo1
        hi0 = max([p for p in tp0 if tp0[p]] + [p0])
        hi1 = max([p for p in tp1 if tp1[p]] + [p1])
        s_in = cellstr(tp0, lo1, max(p0, hi0))
        s_out = cellstr(tp1, lo1, max(p1, hi1))
        rec = dict(t=t0, dt=t1 - t0, arr_in=(st0, r0),
                   arr_out=(st1, r1), pin=p0, pout=p1,
                   lo_in=lo0, lo_out=lo1, s_in=s_in, s_out=s_out,
                   poff_in=p0 - base, poff_out=p1 - base)
        far = next((u for u in seg_turns
                    if u[4] == 'm' and u[1] < lo0), None)
        if far is None:
            bad += 1
            continue
        maxima = [u for u in seg_turns if u[4] == 'M'
                  and far[0] < u[0] < t1]
        minima = [u for u in seg_turns if u[4] == 'm'
                  and u[0] > far[0]]
        # pair max_i with the first min after it
        events = []   # (label, consumed, emitted, dt)
        prevp = prevt = None
        prev_trail = base - 1
        mi = 0
        head = None
        # head-end re-pass detection: if maxima regress, everything
        # whose emission window reaches the re-pass floor is tail
        floor = None
        pp = None
        tp_prev = None
        for (t, p, s, r, k) in maxima:
            if pp is not None and p <= pp:
                t_reg = tp_prev      # peak before the regression
                floor = min(u[1] for u in seg_turns if u[0] > t_reg)
                break
            pp = p
            tp_prev = t
        for (t, p, s, r, k) in maxima:
            if prevp is not None and p <= prevp:
                break        # head-end dance: rest belongs to the tail
            while mi < len(minima) and minima[mi][0] < t:
                mi += 1
            if (floor is not None and mi < len(minima)
                    and minima[mi][1] >= floor):
                break        # emission would touch re-pass region
            if floor is not None and mi >= len(minima):
                break
            if mi >= len(minima):
                trail = p
            else:
                trail = minima[mi][1]
            cons = (s_in[prevp - base + 1: p - base + 1]
                    if prevp is not None
                    else s_in[: p - base + 1])
            emit = s_out[prev_trail - base + 1: trail - base + 1]
            dt = t - (prevt if prevt is not None else far[0])
            if prevp is None:
                head = (f"{s}{r}", cons, emit, dt)
            else:
                events.append((f"{s}{r}", cons, emit, dt))
            prevp, prevt, prev_trail = p, t, trail
            mi += 1
        if prevp is None:
            bad += 1
            continue
        i_tail = prevp - base + 1
        tail_cons = s_in[i_tail:]
        tail_emit = s_out[prev_trail - base + 1:]
        tail_dt = t1 - prevt
        tail_rel = p1 - prev_trail - 1    # head offset rel OUT cursor
        # exact tiling checks
        tin = head[1] + ''.join(e[1] for e in events) + tail_cons
        tout = head[2] + ''.join(e[2] for e in events) + tail_emit
        dtsum = (far[0] - t0) + head[3] + sum(e[3] for e in events) \
            + tail_dt
        if tin != s_in or tout != s_out or dtsum != rec['dt']:
            bad += 1
            continue
        out.append(dict(rec=rec, shoot_dt=far[0] - t0, head=head,
                        events=events,
                        tail=(tail_cons, tail_emit, tail_dt, tail_rel)))
    return out, bad


# ----------------------------------------------------------- predictor

class Calculus:
    """Fail-closed word-rewrite calculus learned from raw segments.

    Configuration: (cells, arr, poff) -- cells spans from one cell
    left of the left extreme to the content frontier; arr = arrival
    (state, read); poff = head offset within cells.  step() applies
    one full sweep (left shoot + rightward transducer pass)."""

    def __init__(self):
        self.heads = {}   # (arr_in, cons) -> (label, cons, emit, dt)
        self.ctx = {}     # (prev_label, look8) -> (label,cons,emit,dt)
        self.tails = {}   # (prev_label, remaining) ->
        #                   (emit, dt, arr_out, rel)

    @staticmethod
    def _look(s, i):
        return s[i:i + 20].ljust(20, '_')

    CASC = __import__('re').compile(r'^#\.#\.((?:###\.#\.)+)#\.')

    @classmethod
    def casc_match(cls, s, i):
        """Maximal-munch cascade at position i: consumed
        '#.#.(###.#.)^k#.' with k>=1.  Returns (cons, emit, dt) or
        None."""
        m = cls.CASC.match(s[i:])
        if not m:
            return None
        k = len(m.group(1)) // 6
        cons = s[i:i + 4 + 6 * k + 2]
        return cons, '#.###.' * (k + 1), 8 + 6 * k

    TRI = __import__('re').compile(
        r'^###\.#\.((?:#\.|###\.#\.)*)#\.$')

    @classmethod
    def tri_tail(cls, rest):
        """Parametric D1 trisection tail:
        '###.#.' MIX '#.'  ->  '#.#.#.' MIX' '#.#'
        where in MIX: '#.' -> '#.', '###.#.' -> '#...#.'.
        Constant dt=5, rel=3, arrival (B,0).
        Returns emit or None."""
        m = cls.TRI.match(rest)
        if m is None:
            return None
        mix = m.group(1)
        outm = []
        j = 0
        while j < len(mix):
            if mix.startswith('###.#.', j):
                outm.append('#...#.')
                j += 6
            elif mix.startswith('#.', j):
                outm.append('#.')
                j += 2
            else:
                return None
        return '#.#.#.' + ''.join(outm) + '#.#'

    @classmethod
    def c1_tail(cls, rest):
        """Parametric C1 tail: '.X' -> '#.#..X', dt=8, rel=3,
        arrival (B,0).  Returns emit or None."""
        if rest.startswith('.') and rest.endswith('#'):
            return '#.#..' + rest[1:]
        return None

    def learn(self, segs):
        for sg in segs:
            rec = sg['rec']
            lab_h, cons_h, emit_h, dt_h = sg['head']
            self._put(self.heads, (rec['arr_in'], cons_h), sg['head'],
                      sg, 'head')
            s_in = rec['s_in']
            i = len(cons_h)
            prev = 'HEAD:' + lab_h
            for ev in sg['events']:
                lab, cons, emit, dt = ev
                cm = self.casc_match(cons, 0)
                if (lab == 'D1' and cm is not None
                        and cm[0] == cons):
                    # parametric cascade: verify, do not store
                    if cm[1] != emit or cm[2] != dt:
                        raise Unexplained(
                            f"cascade mismatch t={rec['t']}: "
                            f"cons='{cons}' emit='{emit}' dt={dt}")
                else:
                    self._put(self.ctx, (prev, self._look(s_in, i)),
                              ev, sg, 'unit')
                i += len(cons)
                prev = lab
            tail_cons, tail_emit, tail_dt, tail_rel = sg['tail']
            tri = self.tri_tail(tail_cons) if prev == 'D1' else None
            c1 = self.c1_tail(tail_cons) if prev == 'C1' else None
            if tri is not None:
                if (tri != tail_emit or tail_dt != 5 or tail_rel != 3
                        or rec['arr_out'] != ('B', 0)):
                    raise Unexplained(
                        f"tri-tail mismatch t={rec['t']}: "
                        f"rest='{tail_cons}' emit='{tail_emit}' "
                        f"pred='{tri}' dt={tail_dt} rel={tail_rel}")
            elif c1 is not None:
                if (c1 != tail_emit or tail_dt != 8 or tail_rel != 3
                        or rec['arr_out'] != ('B', 0)):
                    raise Unexplained(
                        f"c1-tail mismatch t={rec['t']}: "
                        f"rest='{tail_cons}' emit='{tail_emit}' "
                        f"pred='{c1}' dt={tail_dt} rel={tail_rel}")
            else:
                self._put(self.tails, (prev, tail_cons),
                          (tail_emit, tail_dt, rec['arr_out'],
                           tail_rel), sg, 'tail')

    def _put(self, table, key, val, sg, kind):
        if key in table and table[key] != val:
            raise Unexplained(
                f"non-deterministic {kind} rule at t={sg['rec']['t']}:"
                f"\n  key={key}\n  old={table[key]}\n  new={val}")
        table[key] = val

    def step(self, cells, arr, poff):
        """One sweep: (cells, arr, poff) -> (cells', arr', dt, poff').
        Raises Unexplained on any unmatched or ambiguous context."""
        hit = None
        for (a, cons_h), val in self.heads.items():
            if a == arr and cells.startswith(cons_h):
                if hit is None or len(cons_h) > len(hit[0]):
                    hit = (cons_h, val)
        if hit is None:
            raise Unexplained(f"no head rule for arr={arr} "
                              f"cells[:8]='{cells[:8]}'")
        cons_h, (lab_h, _c, emit_h, dt_h) = hit
        out = [emit_h]
        dt = poff + dt_h
        i = len(cons_h)
        prev = 'HEAD:' + lab_h
        while True:
            rest = cells[i:]
            t_hit = (prev, rest) in self.tails
            key = (prev, self._look(cells, i))
            u_hit = key in self.ctx
            if t_hit and u_hit:
                raise Unexplained(f"ambiguous tail/unit: prev={prev} "
                                  f"rest='{rest[:20]}'")
            if t_hit:
                emit_t, dt_t, arr_out, rel = self.tails[(prev, rest)]
                out_len = sum(len(x) for x in out)
                out.append(emit_t)
                dt += dt_t
                return ''.join(out), arr_out, dt, out_len + rel
            if not u_hit:
                cm = self.casc_match(cells, i)
                if cm is not None:
                    cons_c, emit_c, dt_c = cm
                    out.append(emit_c)
                    dt += dt_c
                    i += len(cons_c)
                    prev = 'D1'
                    continue
                if prev == 'D1':
                    tri = self.tri_tail(rest)
                    if tri is not None:
                        out_len = sum(len(x) for x in out)
                        out.append(tri)
                        return (''.join(out), ('B', 0), dt + 5,
                                out_len + 3)
                if prev == 'C1':
                    c1 = self.c1_tail(rest)
                    if c1 is not None:
                        out_len = sum(len(x) for x in out)
                        out.append(c1)
                        return (''.join(out), ('B', 0), dt + 8,
                                out_len + 3)
                raise Unexplained(f"no unit rule: prev={prev} "
                                  f"look='{self._look(cells, i)}'")
            lab, cons, emit, dtu = self.ctx[key]
            if cons and not cells.startswith(cons, i):
                raise Unexplained(
                    f"rule mismatch at i={i}: expected '{cons}' "
                    f"got '{cells[i:i+len(cons)]}'")
            out.append(emit)
            dt += dtu
            i += len(cons)
            prev = lab


def validate(calc, segs):
    """Every segment must be reproduced exactly: output word, dt,
    arrival type, head offset.  Returns (n_ok, failures)."""
    fails = []
    for sg in segs:
        rec = sg['rec']
        try:
            s_out, arr_out, dt, poff = calc.step(
                rec['s_in'], rec['arr_in'], rec['poff_in'])
        except Unexplained as e:
            fails.append((rec['t'], 'unexplained', str(e)))
            continue
        if (s_out != rec['s_out'] or arr_out != rec['arr_out']
                or dt != rec['dt'] or poff != rec['poff_out']):
            fails.append((rec['t'], 'mismatch',
                          f"pred=({s_out},{arr_out},{dt},{poff}) "
                          f"real=({rec['s_out']},{rec['arr_out']},"
                          f"{rec['dt']},{rec['poff_out']})"))
    return len(segs) - len(fails), fails


def chain_check(segs):
    """Verify configuration chaining: s_in(k+1) == '.' + s_out(k) and
    poff_in(k+1) == poff_out(k) + 1."""
    bad = 0
    for a, b in zip(segs, segs[1:]):
        ra, rb = a['rec'], b['rec']
        if ra['t'] + ra['dt'] != rb['t']:
            continue      # non-adjacent (extraction gap)
        if (rb['s_in'] != '.' + ra['s_out']
                or rb['poff_in'] != ra['poff_out'] + 1):
            bad += 1
    return bad


if __name__ == '__main__':
    import sys
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    segs = extract_units_seg(steps)
    print(f"{len(segs)} segments")
    # survey: head chunks, unit alphabet (consumed only), tails
    heads = Counter()
    units = Counter()
    tails = Counter()
    for sg in segs:
        heads[(sg['head_lab'], sg['head_in'], sg['head_dt'])] += 1
        for (lab, cons, dt, p) in sg['units']:
            units[(lab, cons, dt)] += 1
        tails[(sg['tail_in'], sg['tail_dt'],
               sg['rec']['arr_out'],
               sg['rec']['pout'] - sg['rec']['pin'])] += 1
    print("--- head chunks (label, cells, dt):")
    for k, n in heads.most_common(12):
        print(f"  x{n:>4} {k}")
    print("--- units (label, consumed, dt):")
    for k, n in units.most_common(16):
        print(f"  x{n:>4} {k}")
    print("--- tails (cells, dt, arrival, d_extreme):")
    for k, n in tails.most_common(16):
        print(f"  x{n:>4} {k}")

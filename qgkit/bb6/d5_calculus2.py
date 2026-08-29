"""Dossier-5 trisection calculus v2: two-kind segmentation.

Arrivals come in two kinds:
  full : the following leftward excursion reaches below the global
         left extreme (a fresh far-end cell is claimed);
  mini : the excursion stops mid-word (depth >= 8) -- always at the
         '.' immediately left of a '##' cursor block deposited by the
         previous pass's tail.

A segment = arrival -> next arrival, and every segment is one clean
monotone transducer pass (the v1 "re-pass tails" become their own
mini segments).  Configuration: (cells, arr, poff, kind) where kind
is how THIS segment's shoot behaves; each tail rule predicts the next
arrival's (state, read, kind).
"""

from d5_calculus import (TBL, cellstr, Unexplained, Calculus as _C1)

MINI_DEPTH = 8


def stream_segments2(steps):
    """Yield (segdict_or_None, t0, t1).  Bounded memory."""
    tape = {}
    pos, st = 0, 'A'
    lastd = None
    lo = 0
    buf = []
    pend = None
    cur_arr = None          # (t, snap, kind) kind = its own shoot kind
    for t in range(steps):
        r = tape.get(pos, 0)
        w, d, ns = TBL[(st, r)]
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
                        yield (_process2(t0, t_arr, snap0, snap,
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


def _process2(t0, t1, snap0, snap1, seg_turns, kind0, kind1):
    """Analyze one segment.  kind0 = this segment's shoot kind,
    kind1 = the closing arrival's kind (next segment's shoot)."""
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
    fl = far[1] - base                 # floor index (0 for full)
    if kind0 == 'mini':
        if s_in[:fl] != s_out[:fl]:
            return None                # identity prefix violated
        if not (s_in[fl:fl + 4].startswith('.##')):
            rec['floor_pattern'] = s_in[max(0, fl - 2):fl + 4]
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
            break                       # residual dance -> tail
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


class Calculus2(_C1):
    """v2: kinds, floor-finding, per-kind heads, kinded tail values."""

    @staticmethod
    def _look(s, i):
        """20-cell decision window; when the window is saturated
        clean alternation ('#.'*10) the decision additionally
        depends on proximity to the input end -- append the
        remaining-length bucket (exact below 64, else FAR)."""
        w = s[i:i + 20].ljust(20, '_')
        if w == '#.' * 10:
            rem = len(s) - i
            return w + (f"|{rem}" if rem < 64 else "|FAR")
        return w

    def learn(self, segs):
        for sg in segs:
            rec = sg['rec']
            kind = rec['kind']
            fl = sg['floor']
            lab_h, cons_h, emit_h, dt_h = sg['head']
            self._put(self.heads, (kind, rec['arr_in'], cons_h),
                      sg['head'], sg, 'head')
            if kind == 'full' and fl != 0:
                raise Unexplained(f"full segment with floor {fl}")
            if kind == 'mini':
                # verify the floor law: '.' just left of rightmost
                # '.##.' below poff, at odd distance
                pf = self._find_floor(rec['s_in'], rec['poff_in'])
                if pf != fl:
                    raise Unexplained(
                        f"floor law fails t={rec['t']}: law={pf} "
                        f"real={fl} poff={rec['poff_in']}")
                # shoot cost = poff - floor
                if sg['shoot_dt'] != rec['poff_in'] - fl:
                    raise Unexplained(
                        f"mini shoot dt {sg['shoot_dt']} != "
                        f"{rec['poff_in'] - fl} t={rec['t']}")
            else:
                if sg['shoot_dt'] != rec['poff_in']:
                    raise Unexplained(
                        f"full shoot dt {sg['shoot_dt']} != poff "
                        f"{rec['poff_in']} t={rec['t']}")
            s_in = rec['s_in']
            i = fl + len(cons_h)
            prev = 'HEAD:' + lab_h
            for ev in sg['events']:
                lab, cons, emit, dt = ev
                cm = self.casc_match(cons, 0)
                if lab == 'D1' and cm is not None and cm[0] == cons:
                    if cm[1] != emit or cm[2] != dt:
                        raise Unexplained(
                            f"cascade mismatch t={rec['t']}")
                else:
                    self._put(self.ctx, (prev, self._look(s_in, i)),
                              ev, sg, 'unit')
                i += len(cons)
                prev = lab
            tail_cons, tail_emit, tail_dt, tail_rel = sg['tail']
            # kind law: mini iff a cursor '.##.' remains below poff
            law = ('mini' if rec['s_out'].rfind(
                '.##.', 0, rec['poff_out']) >= 0 else 'full')
            if law != rec['kind_next']:
                raise Unexplained(
                    f"kind law fails t={rec['t']}: law={law} "
                    f"real={rec['kind_next']}")
            tri = self.tri_tail(tail_cons) if prev == 'D1' else None
            c1 = self.c1_tail(tail_cons) if prev == 'C1' else None
            if tri is not None:
                if (tri != tail_emit or tail_dt != 5 or tail_rel != 3
                        or rec['arr_out'] != ('B', 0)):
                    raise Unexplained(
                        f"tri-tail mismatch t={rec['t']}")
            elif c1 is not None:
                if (c1 != tail_emit or tail_dt != 8 or tail_rel != 3
                        or rec['arr_out'] != ('B', 0)):
                    raise Unexplained(
                        f"c1-tail mismatch t={rec['t']}")
            else:
                self._put(self.tails, (prev, tail_cons),
                          (tail_emit, tail_dt, rec['arr_out'],
                           tail_rel), sg, 'tail')

    @staticmethod
    def _find_floor(cells, poff):
        """The floor: '.' immediately left of the '##' the shoot hits:
        rightmost j < poff with cells[j:j+4] == '.##.'."""
        j = cells.rfind('.##.', 0, poff)
        return j if j >= 0 else None

    def step(self, cells, arr, poff, kind):
        """(cells, arr, poff, kind) -> (cells', arr', dt, poff',
        kind')."""
        if kind == 'full':
            fl = 0
            dt = poff
            out = []
        else:
            fl = self._find_floor(cells, poff)
            if fl is None:
                raise Unexplained("mini arrival but no '.##.' found")
            dt = poff - fl
            out = [cells[:fl]]
        hit = None
        for (k, a, cons_h), val in self.heads.items():
            if (k == kind and a == arr
                    and cells.startswith(cons_h, fl)):
                if hit is None or len(cons_h) > len(hit[0]):
                    hit = (cons_h, val)
        if hit is None:
            raise Unexplained(f"no head rule kind={kind} arr={arr} "
                              f"cells[fl:fl+10]='{cells[fl:fl+10]}'")
        cons_h, (lab_h, _c, emit_h, dt_h) = hit
        out.append(emit_h)
        dt += dt_h
        i = fl + len(cons_h)
        prev = 'HEAD:' + lab_h
        while True:
            rest = cells[i:]
            t_hit = (prev, rest) in self.tails
            key = (prev, self._look(cells, i))
            u_hit = key in self.ctx
            if t_hit and u_hit:
                raise Unexplained(f"ambiguous tail/unit prev={prev}")
            if t_hit:
                emit_t, dt_t, arr_out, rel = self.tails[(prev, rest)]
                out_len = sum(len(x) for x in out)
                out.append(emit_t)
                s_out = ''.join(out)
                poff2 = out_len + rel
                kn = ('mini' if s_out.rfind('.##.', 0, poff2) >= 0
                      else 'full')
                return s_out, arr_out, dt + dt_t, poff2, kn
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
                        s_out = ''.join(out)
                        poff2 = out_len + 3
                        kn = ('mini' if s_out.rfind(
                            '.##.', 0, poff2) >= 0 else 'full')
                        return s_out, ('B', 0), dt + 5, poff2, kn
                if prev == 'C1':
                    c1 = self.c1_tail(rest)
                    if c1 is not None:
                        out_len = sum(len(x) for x in out)
                        out.append(c1)
                        s_out = ''.join(out)
                        poff2 = out_len + 3
                        kn = ('mini' if s_out.rfind(
                            '.##.', 0, poff2) >= 0 else 'full')
                        return s_out, ('B', 0), dt + 8, poff2, kn
                raise Unexplained(f"no unit rule prev={prev} "
                                  f"look='{self._look(cells, i)}'")
            lab, cons, emit, dtu = self.ctx[key]
            if cons and not cells.startswith(cons, i):
                raise Unexplained(f"rule mismatch at i={i}")
            out.append(emit)
            dt += dtu
            i += len(cons)
            prev = lab


def validate2(calc, segs):
    fails = []
    for sg in segs:
        rec = sg['rec']
        try:
            s_out, arr_out, dt, poff, kn = calc.step(
                rec['s_in'], rec['arr_in'], rec['poff_in'],
                rec['kind'])
        except Unexplained as e:
            fails.append((rec['t'], 'unexplained', str(e)))
            continue
        if (s_out != rec['s_out'] or arr_out != rec['arr_out']
                or dt != rec['dt'] or poff != rec['poff_out']
                or kn != rec['kind_next']):
            fails.append((rec['t'], 'mismatch',
                          f"pred dt={dt} poff={poff} kind={kn} "
                          f"real dt={rec['dt']} "
                          f"poff={rec['poff_out']} "
                          f"kind={rec['kind_next']} "
                          f"word_eq={s_out == rec['s_out']}"))
    return len(segs) - len(fails), fails

"""Parametric calculus for the candidate array-class machine
1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB (right-growing, no mirror).

The generic literal ladder (d5_generic.py, MINI_DEPTH=8) leaves this
machine at 82.4% held-out: its dynamics is tail-dominated (616 tail
literals, 308 learning conflicts, all in the tails table).  Analysis
of the learned tails shows they collapse into two parametric families
plus one bounded literal, and the 308 conflicts are all the same
single key aliasing on kind_next only.  This module replaces the
literal tail table with the families and derives kind_next (and the
mini floor) from a word law, exactly the move that closed the rank-1
machine (d5_calculus2.py).

Families (cons -> emit; leading run length 2m+1 must be odd):

  D1 tail (after mini head 'D1' = '..####' -> '####', dt 5):
    '#'^(2m+1) '.'          ->  '##.' ('#.')^m '#'
    '#'^(2m+1) '.' '#.' S   ->  '##.' ('#.')^m '##.' S
    dt 5, rel 2, arr_out (C,0).   Observed m: 1, 4, 7 (runs 3+6j).

  A1 tail (after full head 'A1' = '.#' -> '.', dt 1):
    '#'^(2m+1) '.'          ->  ('#.')^(m+1) '#'
    '#'^(2m+1) '.' '#.' S   ->  ('#.')^(m+1) '##.' S
    dt 3, rel 1, arr_out (C,0).   Observed m: 0, 5, 8 (runs 5+6j
    and 1).

  C0 tail (after full head 'C0' = '..#.#' -> '####', dt 6, and the
    growth unit '' -> '###', dt 11): '' -> '#####.', dt 15, rel 5,
    arr_out (C,0).  Kept literal (single bounded rule).

Word laws (verified on every one of the 179,715 tiled segments of
the 4M-step run, zero exceptions):

  floor law : the mini floor is the rightmost j < poff with
              cells[j:j+6] == '..####' and poff - j >= 8.
  kind law  : the next arrival is mini iff the floor law finds a
              site in s_out below poff_out; else full.
  arrivals  : every arrival is (C, 0).

Learning stays fail-closed: every observed tail instance is checked
against its family (emit, dt, rel, arr_out) and every segment against
the kind law; any mismatch is a conflict.  Validation never guesses:
a rest that fits no family, no literal tail, and no ctx rule fails.
"""
import re
from d5_generic import (parse, mirror, growth_dir, stream_segments,
                        LiteralCalc)

CODE = '1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB'
MIN_DEPTH = 8

_RUN = re.compile(r'^(#+)\.(.*)$', re.S)


def _family(cons, unit0, unit1):
    """Shared shape: '#'^(2m+1) '.' rest with rest in {'', '#.'+S}.
    Emit unit0 + '#.'*m + ('#' if rest=='' else unit1+S)."""
    mo = _RUN.match(cons)
    if mo is None:
        return None
    n = len(mo.group(1))
    if n % 2 == 0:
        return None
    m = (n - 1) // 2
    rest = mo.group(2)
    if rest == '':
        return unit0 + '#.' * m + '#'
    if rest.startswith('#.'):
        return unit0 + '#.' * m + unit1 + rest[2:]
    return None


def d1_tail(cons):
    return _family(cons, '##.', '##.')


def a1_tail(cons):
    return _family(cons, '#.', '##.') if cons else None


FAMS = {'HEAD:D1': (d1_tail, 5, 2), 'HEAD:A1': (a1_tail, 3, 1)}


def law_floor(cells, poff):
    """Rightmost j < poff with '..####' at j and depth >= 8."""
    j = cells.rfind('..####', 0, poff)
    while j >= 0:
        if poff - j >= MIN_DEPTH:
            return j
        j = cells.rfind('..####', 0, j)
    return None


class ParamCalc(LiteralCalc):
    """Literal heads/ctx + parametric tails + floor/kind word laws."""

    def learn(self, sg):
        rec = sg['rec']
        fl = sg['floor']
        lab_h, cons_h, emit_h, dt_h = sg['head']
        self._put(self.heads, (rec['kind'], rec['arr_in'], cons_h),
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
        fam = FAMS.get(prev)
        pe = fam[0](tail_cons) if fam else None
        if pe is not None:
            if (pe != tail_emit or tail_dt != fam[1]
                    or tail_rel != fam[2]
                    or rec['arr_out'] != ('C', 0)):
                self.conflicts += 1
        else:
            self._put(self.tails, (prev, tail_cons),
                      (tail_emit, tail_dt, rec['arr_out'], tail_rel,
                       rec['kind_next']))
        # word laws, checked on every segment
        if rec['kind'] == 'mini' and law_floor(s_in,
                                               rec['poff_in']) != fl:
            self.conflicts += 1
        law_kn = ('mini' if law_floor(rec['s_out'],
                                      rec['poff_out']) is not None
                  else 'full')
        if law_kn != rec['kind_next']:
            self.conflicts += 1

    def step(self, cells, arr, poff, kind, floor):
        fl = 0 if kind == 'full' else floor
        dt = poff - fl
        out = [cells[:fl]] if fl else []
        hit = None
        for (k, a, cons_h), val in self.heads.items():
            if k == kind and a == arr and cells.startswith(cons_h,
                                                          fl):
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
            fam = FAMS.get(prev)
            pe = fam[0](rest) if fam else None
            if pe is not None:
                out_len = sum(len(x) for x in out)
                out.append(pe)
                s_out = ''.join(out)
                poff2 = out_len + fam[2]
                kn = ('mini' if law_floor(s_out, poff2) is not None
                      else 'full')
                return s_out, ('C', 0), dt + fam[1], poff2, kn
            if (prev, rest) in self.tails:
                emit_t, dt_t, arr_out, rel, kn = \
                    self.tails[(prev, rest)]
                out_len = sum(len(x) for x in out)
                out.append(emit_t)
                s_out = ''.join(out)
                poff2 = out_len + rel
                kn = ('mini' if law_floor(s_out, poff2) is not None
                      else 'full')
                return s_out, arr_out, dt + dt_t, poff2, kn
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


def ladder(train_steps=2_000_000, total_steps=4_000_000):
    tbl = parse(CODE)
    gd = growth_dir(tbl)
    assert gd == 'R', gd
    calc = ParamCalc()
    n_seg = n_none = n_val = n_exact = 0
    for item in stream_segments(tbl, total_steps):
        if item[0] == 'HALT':
            return dict(verdict='HALT?')
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
                        and kn == rec['kind_next']
                        and arr_out == rec['arr_out']):
                    n_exact += 1
    total = n_seg + n_none
    return dict(segments=total, tiled=n_seg,
                arch=n_seg / total if total else 0.0,
                conflicts=calc.conflicts, ctx=len(calc.ctx),
                heads=len(calc.heads), tails=len(calc.tails),
                validated=n_val, exact=n_exact)


if __name__ == '__main__':
    r = ladder()
    pct = 100 * r['exact'] / r['validated'] if r['validated'] else 0
    print(f"segs={r['segments']} tiled={r['arch']*100:.2f}% "
          f"conflicts={r['conflicts']} heads={r['heads']} "
          f"ctx={r['ctx']} tails={r['tails']} "
          f"heldout={r['exact']}/{r['validated']} ({pct:.2f}%)")

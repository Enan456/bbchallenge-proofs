"""Literal Python ports of the Google DeepMind `cryptids` Lean 4
accelerations (`State`, `start`, `encode`, `next`) for the four BB(6)
machines shared with this repository, plus a `decode` (inverse of
`encode`) used to recognise canonical configurations in a raw trace.

Source files (github.com/google-deepmind/cryptids, BusyBeaver/BB6/):
  M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean   (dossier-2)
  M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean   (dossier-3)
  M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean   (dossier-7)
  M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean   (dossier-27)

Conventions (BusyBeaver/Defs.lean, Basic.lean):
  `Cfg.headRight q l r` : head reads r[0]; l is the left half-tape with
                          l[0] adjacent to the head (nearest-first).
  `ListBlank.append s L`, written `s +> L` or `L <+ s`, prepends the
  list s toward the head.  `default` is the all-blank half-tape.

`encode(s)` here returns (state_letter, left_nearest_first, right_head_first)
as tuples of 0/1 with trailing blanks stripped, which is exactly the
canonical form `RawSim.left_nearest_first()/right_head_first()` yields.
`decode(state, left, right)` returns a State or None.
"""
import re

from .rawtm import bits, strbits


def _strip(t):
    t = list(t)
    while t and t[-1] == 0:
        t.pop()
    return tuple(t)


# =====================================================================
# dossier-2  (Google: C_0 / C_1 three-counter system)
# =====================================================================
class D2:
    CODE = '1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD'
    START_STEP = 100           # "Start: C_1(2, 2, 0), reached after 100 raw TM steps"
    start = ('C1', 2, 2, 0)
    HEAD_STATE = 'E'

    @staticmethod
    def encode(s):
        kind, a, b, c = s
        if kind == 'C0':
            left = (1, 1) + (1, 1) * a
        else:
            left = (1, 1, 1) + (1, 1) * a
        right = (1, 1) + (1, 1) * b + (0, 1, 1) + (1, 1) * c
        return 'E', _strip(left), _strip(right)

    _RIGHT = re.compile(r'^(1{2,})0(1{2,})$')

    @classmethod
    def decode(cls, state, left, right):
        if state != 'E':
            return None
        if any(x != 1 for x in left) or len(left) < 2:
            return None
        m = cls._RIGHT.match(strbits(right))
        if not m:
            return None
        p, q = len(m.group(1)), len(m.group(2))
        if p % 2 or q % 2:
            return None
        L = len(left)
        if L % 2 == 0:
            return ('C0', (L - 2) // 2, (p - 2) // 2, (q - 2) // 2)
        if L < 3:
            return None
        return ('C1', (L - 3) // 2, (p - 2) // 2, (q - 2) // 2)

    @staticmethod
    def next(s):
        kind, a, b, c = s
        if kind == 'C0':
            if b == 0 and c == 0:
                return None
            if b == 0 and c == 1:
                return ('C1', 2, 2, a + 1)
            if b == 0:                       # c = d + 2
                return ('C0', 1, a + 3, c - 2)
            if c == 0:                       # b = b' + 1
                return ('C1', a + 1, 0, b - 1)
            return ('C0', a + 3, b - 1, c - 1)
        else:
            if b == 0 and c == 0:
                return None
            if b == 0 and c == 1:
                return ('C0', 1, 0, a + 3)
            if b == 0:
                return ('C1', 2, a + 3, c - 2)
            if c == 0:
                return ('C0', a + 2, 0, b - 1)
            return ('C1', a + 3, b - 1, c - 1)

    @staticmethod
    def canon(s):
        return s


# =====================================================================
# dossier-3  (Google: C k m f)
# =====================================================================
class D3:
    CODE = '1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE'
    START_STEP = 76            # "Start: C(6, 2, 2), reached after 76 raw TM steps"
    start = ('C', 2, 0, 1)
    HEAD_STATE = 'D'

    @staticmethod
    def encode(s):
        _, k, m, f = s
        left = (0,) + (1, 1) * (m + 1) + (0,) + (1, 1) * (k + 1)
        right = (1,) + (1,) * (f + 1)
        return 'D', _strip(left), _strip(right)

    _LEFT = re.compile(r'^0(1{2,})0(1{2,})$')

    @classmethod
    def decode(cls, state, left, right):
        if state != 'D':
            return None
        if len(right) < 2 or any(x != 1 for x in right):
            return None
        m = cls._LEFT.match(strbits(left))
        if not m:
            return None
        p, q = len(m.group(1)), len(m.group(2))
        if p % 2 or q % 2:
            return None
        return ('C', q // 2 - 1, p // 2 - 1, len(right) - 2)   # right = 1^{f+2}

    @staticmethod
    def next(s):
        _, k, m, f = s
        if k == 0:
            if m == 0 or m == 1:
                return None
            if m == 2:
                return ('C', f // 2 + 3, 2, 4) if f % 2 == 0 else ('C', f // 2 + 5, 0, 1)
            # m = m' + 3
            return ('C', m - 3, f // 2 + 5, 1) if f % 2 == 0 else ('C', m - 3, f // 2 + 5, 4)
        if m == 0:
            if k == 1:
                return ('C', f // 2 + 3, 0, 1) if f % 2 == 0 else ('C', f // 2 + 2, 2, 4)
            # k = k' + 2
            return ('C', k - 2, f // 2 + 3, 4) if f % 2 == 0 else ('C', k - 2, f // 2 + 4, 1)
        # k = k'+1, m = m'+1
        kk, mm = k - 1, m - 1
        if kk < mm:
            return ('C', 0, mm - kk, f + 6 * (kk + 1))
        if mm < kk:
            return ('C', kk - mm, 0, f + 6 * (mm + 1))
        return ('C', 0, 0, f + 6 * (kk + 1))

    @staticmethod
    def canon(s):
        return s


# =====================================================================
# dossier-7  (Google: C_3 / C_6 / M_3 / M_6_pos / L_3 / L_6)
# =====================================================================
class D7:
    CODE = '1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA'
    START_STEP = 162           # "Start: C(4,0,0,3), reached after 162 raw TM steps"
    start = ('C3', 4, 0, 0)

    @staticmethod
    def encode(s):
        kind = s[0]
        tail = (0, 1, 1)
        if kind in ('C3', 'C6'):
            _, a, b, c = s
            d = 3 if kind == 'C3' else 6
            left = (1,) * (a + 1)
            right = (0, 0) + (1,) * (b + 4) + (0, 1) * c + (1,) * d + tail
            return 'C', _strip(left), _strip(right)
        if kind == 'M3':
            _, a, b, c = s
            left = (1, 0) + (1,) * ((1 if a else 0) + 3)
            right = (0,) + (1,) * (b + 4) + (0, 1) * c + (1,) * 3 + tail
            return 'A', _strip(left), _strip(right)
        if kind == 'M6':                     # M_6_pos a b c  = M(a, b, c+1, 6)
            _, a, b, c = s
            left = (1, 0) + (1,) * ((1 if a else 0) + 3)
            right = (0,) + (1,) * (b + 4) + (0, 1) * (c + 1) + (1,) * 6 + tail
            return 'A', _strip(left), _strip(right)
        if kind == 'L3':                     # L_3 a b = L(a, b+1, 3)
            _, a, b = s
            left = (1,) * ((b + 1) + 6) + (0,) + (1,) * ((1 if a else 0) + 3)
            right = (1,) + (1,) * 3 + tail
            return 'C', _strip(left), _strip(right)
        if kind == 'L6':                     # L_6 a b = L(a, b, 6)
            _, a, b = s
            left = (1,) * (b + 6) + (0,) + (1,) * ((1 if a else 0) + 3)
            right = (1,) + (1,) * 6 + tail
            return 'C', _strip(left), _strip(right)
        raise ValueError(s)

    # right-tape grammars (head-first).  (01)* then 1^d: the last pair's
    # `1` merges with the `d` run, hence the explicit alternatives.
    _C_RIGHT = re.compile(r'^00(1{4,})((?:01)*)(111|111111)011$')
    _M_RIGHT = re.compile(r'^0(1{4,})((?:01)*)(111|111111)011$')
    _L_RIGHT = re.compile(r'^(1111|1111111)011$')
    _L_LEFT = re.compile(r'^(1{6,})0(111|1111)$')

    @classmethod
    def decode(cls, state, left, right):
        ls, rs = strbits(left), strbits(right)
        if state == 'C':
            if ls and all(c == '1' for c in ls):
                m = cls._C_RIGHT.match(rs)
                if m:
                    a = len(ls) - 1
                    b = len(m.group(1)) - 4
                    c = len(m.group(2)) // 2
                    d = len(m.group(3))
                    return cls.canon(('C3' if d == 3 else 'C6', a, b, c))
            m2 = cls._L_LEFT.match(ls)
            m3 = cls._L_RIGHT.match(rs)
            if m2 and m3:
                a = len(m2.group(2)) == 4
                d = len(m3.group(1)) - 1
                if d == 3:
                    return ('L3', a, len(m2.group(1)) - 6 - 1) if len(m2.group(1)) >= 7 else None
                return ('L6', a, len(m2.group(1)) - 6)
            return None
        if state == 'A':
            if ls not in ('10111', '101111'):
                return None
            a = ls == '101111'
            m = cls._M_RIGHT.match(rs)
            if not m:
                return None
            b = len(m.group(1)) - 4
            c = len(m.group(2)) // 2
            d = len(m.group(3))
            if d == 3:
                return ('M3', a, b, c)
            if c == 0:
                return None                  # M_6_pos needs c+1 >= 1 pairs
            return ('M6', a, b, c - 1)
        return None

    @staticmethod
    def canon(s):
        """Google's identity C(a,b,0,6) = C(a,b+3,0,3): normalise to C_3."""
        if s[0] == 'C6' and s[3] == 0:
            return ('C3', s[1], s[2] + 3, 0)
        return s

    @staticmethod
    def next(s):
        kind = s[0]
        if kind == 'C3':
            _, a, b, c = s
            if a == 0:
                return ('M3', False, b, c)
            if a == 1:
                return ('M3', True, b, c)
            return ('C3', a - 2, b + 3, c)
        if kind == 'C6':
            _, a, b, c = s
            if a in (0, 1) and c == 0:
                return ('M3', a == 1, b + 3, 0)
            if a in (0, 1):
                return ('M6', a == 1, b, c - 1)
            return ('C6', a - 2, b + 3, c)
        if kind == 'M3':
            _, a, b, c = s
            if c == 0:
                return ('L3', a, b)
            if c == 1:
                return ('L6', a, b)
            return ('C3', b + 4 + (1 if a else 0), 3, c - 2)
        if kind == 'M6':
            _, a, b, c = s
            if c == 0:
                return ('C3', b + 4 + (1 if a else 0), 0, 3)
            return ('C6', b + 4 + (1 if a else 0), 3, c - 1)
        if kind == 'L3':
            _, a, b = s
            if b % 2 == 0:
                return ('C3', 1 if a else 0, 0, b // 2 + 3)
            if a:
                return ('C3', 6, 3, b // 2)
            return None
        if kind == 'L6':
            _, a, b = s
            if b % 2 == 1:
                return ('C6', 1 if a else 0, 0, b // 2 + 3)
            if not a:
                return None
            if b == 0:
                return ('C3', 6, 0, 3)
            return ('C6', 6, 3, b // 2 - 1)
        raise ValueError(s)


# =====================================================================
# dossier-27  (Google: five families R1/R2/Q/S4/S6 over U4 = [0,0,1,1]^n;
#              `next` composes HubTail / HubW8 / Scan transducers)
# =====================================================================
class D27:
    CODE = '1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA'
    # Google's docstring says "reaches S6 1 in 66 steps"; the raw trace
    # reaches P_cfg 3 at step 97 and S6_cfg 1 at step 169.  Their Lean
    # proof (`init_to_S6_1`) is a ReachesStar statement with no step
    # count, so only the docstring number is off (66 is the step count of
    # their `step_drain_odd_end_66_0349` turnaround lemma).
    START_STEP = 169
    DOCSTRING_START_STEP = 66
    start = ('S6', 1)
    U4 = '0011'
    SUFFIX = {
        'R1': '001',
        'R2': '001001',
        'Q': '001111',
        'S4': '001001001111',
        'S6': '00100100111111',
    }

    @classmethod
    def encode(cls, s):
        kind, n = s
        left = bits(cls.SUFFIX[kind] + cls.U4 * n)
        return 'A', _strip(left), ()

    @classmethod
    def decode(cls, state, left, right):
        if state != 'A' or right:
            return None
        ls = strbits(left)
        for kind, sfx in cls.SUFFIX.items():
            if ls.startswith(sfx):
                rest = ls[len(sfx):]
                if len(rest) % 4 == 0 and rest == cls.U4 * (len(rest) // 4):
                    return (kind, len(rest) // 4)
        return None

    @staticmethod
    def canon(s):
        return s

    # -- auxiliary successor maps ---------------------------------------
    @staticmethod
    def next_P(n):
        if n == 0:
            return ('S6', 1)
        if n == 1:
            return ('S4', 0)
        return ('S6', n - 2)

    @staticmethod
    def next_R1(n):
        if n == 0:
            return ('R1', 4)
        if n == 1:
            return ('R1', 6)
        return ('R1', (n - 2) + 7)

    @staticmethod
    def next_T1(n):
        if n == 0:
            return ('R1', 7)
        return ('R1', (n - 1) + 8)

    @classmethod
    def next_R3(cls, n):
        if n == 0:
            return cls.next_T1(4)
        if n == 1:
            return cls.next_T1(6)
        return cls.next_T1((n - 2) + 7)

    _HUBTAIL = {
        # r_R2
        'r_R2': {0: lambda a: ('R1', a + 8), 1: lambda a: ('R2', a + 11),
                 2: lambda a: ('Q', a + 19), 3: lambda a: ('R2', a + 26),
                 4: lambda a: D27.next_R3(a + 32)},
        'r_3': {0: lambda a: ('R1', a + 10), 1: lambda a: ('Q', a + 16),
                2: lambda a: ('R2', a + 23), 3: lambda a: None,
                4: lambda a: ('R2', a + 37)},
        'r_4': {0: lambda a: D27.next_T1(a + 9), 1: lambda a: ('R2', a + 15),
                2: lambda a: ('R1', a + 25), 3: lambda a: ('S6', a + 28),
                4: lambda a: ('R2', a + 41)},
        'r_5': {0: lambda a: ('R1', a + 12), 1: lambda a: ('R1', a + 15),
                2: lambda a: ('R2', a + 26), 3: lambda a: ('Q', a + 34),
                4: lambda a: D27.next_T1(a + 38)},
    }

    @classmethod
    def next_HubTail(cls, kind, a, w):
        """`a, w'+5 => next_HubTail (a+31) w'` unrolled, then the table."""
        a += 31 * (w // 5)
        return cls._HUBTAIL[kind][w % 5](a)

    # Scan bundles.  `eval_bundle(kind, b, name, a)` evaluates the field
    # `name` of `next_ScanBundle_<kind> b` at `a`, iterating the Nat.rec
    # step case down to the base case (no Python recursion).
    _BASE = {
        'r_Q': {
            'p0': lambda a: ('R1', a + 4),
            'p001010': lambda a: D27.next_P(a + 8),
            'p0010': lambda a: ('R2', a + 4),
            'p0010110': lambda a: D27.next_P(a + 10),
            'p00': lambda a: ('R1', a + 4),
            'p010': lambda a: D27.next_P(a + 7),
            'pnil': lambda a: D27.next_P(a + 5),
            'p0_next': lambda a: ('S6', a + 2),
            'p0010_next': lambda a: ('R1', a + 9),
        },
        'r_S6': {
            'p0': lambda a: ('S4', a + 9),
            'p001010': lambda a: D27.next_T1(a + 11),
            'p0010': lambda a: ('R1', a + 10),
            'p0010110': lambda a: None,
            'p00': lambda a: ('R2', a + 11),
            'p010': lambda a: ('R1', a + 14),
            'pnil': lambda a: D27.next_T1(a + 8),
            'p0_next': lambda a: D27.next_HubTail('r_4', 0, (a + 1) // 2 + 1),
            'p0010_next': lambda a: D27.next_HubTail('r_3', 0, (a + 8) // 2),
        },
        'r_S4': {
            'p0': lambda a: ('R2', a + 7),
            'p001010': lambda a: ('R1', a + 9),
            'p0010': lambda a: ('R1', a + 9),
            'p0010110': lambda a: ('S4', a + 9),
            'p00': lambda a: D27.next_T1(a + 4),
            'p010': lambda a: ('Q', a + 9),
            'pnil': lambda a: ('R1', a + 6),
            'p0_next': lambda a: D27.next_HubTail('r_5', 0, (a + 1) // 2 + 1),
            'p0010_next': lambda a: ('R1', a + 13),
        },
    }

    # step case: field of bundle_{b} in terms of bundle_{b-1} (= nb)
    #   p0 := nb.p0_next ; p001010 := a ↦ nb.p0 (a+6) ; p0010 := nb.p0010_next
    #   p0010110 := a ↦ nb.p00 (a+9) ; p00 := a ↦ nb.p010 (a+3)
    #   p010 := a ↦ nb.pnil (a+4) ; pnil := a ↦ nb.p0 (a+3)
    #   p0_next := a ↦ next_HubW8 nb 0 ((a+3)/2) ; p0010_next := a ↦ nb.p0010110 (a+5)
    _STEP = {
        'p0': ('p0_next', 0),
        'p001010': ('p0', 6),
        'p0010': ('p0010_next', 0),
        'p0010110': ('p00', 9),
        'p00': ('p010', 3),
        'p010': ('pnil', 4),
        'pnil': ('p0', 3),
        'p0010_next': ('p0010110', 5),
    }
    # next_HubW8 nb a w:  w<5 -> nb.<field>(a + off); w>=5 -> (a+31, w-5)
    _HUBW8 = {0: ('p0', 4), 1: ('p010', 7), 2: ('p00', 16), 3: ('p0010', 22),
              4: ('p001010', 28)}

    @classmethod
    def eval_bundle(cls, kind, b, name, a):
        while True:
            if b == 0:
                return cls._BASE[kind][name](a)
            if name == 'p0_next':
                # next_HubW8 nb 0 ((a+3)/2) with nb = bundle_{b-1}
                w = (a + 3) // 2
                a2 = 31 * (w // 5)
                name, off = cls._HUBW8[w % 5]
                a = a2 + off
                b -= 1
                continue
            name, off = cls._STEP[name]
            a += off
            b -= 1

    @classmethod
    def next_R2(cls, n):
        if n == 0:
            return ('R1', 4)
        return cls.next_HubTail('r_R2', 0, (n - 1) // 2)

    @classmethod
    def next_Q(cls, n):
        if n == 0:
            return ('R1', 6)
        return cls.eval_bundle('r_Q', n - 1, 'p0010110', 2)

    @classmethod
    def next_S4(cls, n):
        if n == 0:
            return ('R1', 10)
        return cls.eval_bundle('r_S4', n - 1, 'p0010110', 2)

    @classmethod
    def next_S6(cls, n):
        if n == 0:
            return ('R1', 9)
        if n == 1:
            return cls.next_HubTail('r_3', 0, 2)
        return cls.eval_bundle('r_S6', n - 2, 'p0010110', 2)

    @classmethod
    def next(cls, s):
        kind, n = s
        return {'R1': cls.next_R1, 'R2': cls.next_R2, 'Q': cls.next_Q,
                'S4': cls.next_S4, 'S6': cls.next_S6}[kind](n)


MACHINES = {'d2': D2, 'd3': D3, 'd7': D7, 'd27': D27}

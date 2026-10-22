"""Raw BB(6) simulator in absolute coordinates (blank start, head at 0,
state A) plus the Google-style canonical form of a configuration."""


def parse_tm(code):
    tbl = {}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \
                (int(tr[0]), tr[1], tr[2])
    return tbl


class RawSim:
    """Mutable raw configuration.  `tape` is a dict cell -> 0/1 (absent
    = blank); `lo`/`hi` bound the cells ever visited; `maxone`/`minone`
    bound the nonblank cells (recomputed lazily)."""

    def __init__(self, code):
        self.tbl = parse_tm(code)
        self.tape = {}
        self.state = 'A'
        self.head = 0
        self.t = 0
        self.halted = False

    def read(self):
        return self.tape.get(self.head, 0)

    def step(self):
        tr = self.tbl[(self.state, self.read())]
        if tr is None:
            self.halted = True
            return False
        wv, d, ns = tr
        self.tape[self.head] = wv
        self.head += 1 if d == 'R' else -1
        self.state = ns
        self.t += 1
        return True

    # -- Google-style canonical form -------------------------------------
    def left_nearest_first(self):
        """Cells head-1, head-2, ... down to the last nonblank one."""
        tape, h = self.tape, self.head
        keys = [k for k in tape if k < h and tape[k]]
        if not keys:
            return ()
        lo = min(keys)
        return tuple(tape.get(k, 0) for k in range(h - 1, lo - 1, -1))

    def right_head_first(self):
        """Cells head, head+1, ... up to the last nonblank one."""
        tape, h = self.tape, self.head
        keys = [k for k in tape if k >= h and tape[k]]
        if not keys:
            return ()
        hi = max(keys)
        return tuple(tape.get(k, 0) for k in range(h, hi + 1))

    def ones(self):
        return {k for k, v in self.tape.items() if v}


def bits(s):
    """'0011' -> (0, 0, 1, 1)."""
    return tuple(int(c) for c in s)


def strbits(t):
    return ''.join(str(b) for b in t)

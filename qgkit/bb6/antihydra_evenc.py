"""Antihydra even-c characterization of the realizable dying family (1,2,c).

Machine: 1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA  (Antihydra, BB(6)).

Context
-------
The Lean file busy-beaver-core/BusyBeaverCore/AntihydraRawTM.lean reduces
raw non-halting from the blank tape to `SafeOrbitA`: the abstract orbit of

    astep(a, m, c) = (a, m-2, c+3)        if m >= 3            [hydra]
                   = (a-1, c+3, 2)        if m = 2 and a >= 2  [drop]
                   = none                 if m = 2 and a  < 2  [DEATH]
                   = (a+2, c+2, 2)        if m = 1             [merge]
                   = none                 if m = 0             [DEATH]

never reaches a `none`.  The death set of the abstract map is therefore

    D = { (a, 2, c) : a <= 1 } union { (a, 0, c) }.

The grammar `Realizes` demands a, m, c >= 1, so the ONLY death states with
a tape realization are the family (1, 2, c).  "Abstract death" is loss of
grammar certification, NOT a proven raw halt.  This script measures the
actual RAW fate of the materialized tape 1^1 0 1^2 0 1^c (state B, head on
the fresh right frontier) as a function of c.

This is an analysis of the abstract/raw map.  It does NOT resolve the
Antihydra non-halting conjecture (`SafeOrbitA`); on the contrary, the
even-c fate is shown to REDUCE to that same open conjecture on derived
seeds.  Every number below is a measurement.

What this script establishes
----------------------------
1. odd c : materialize(1,2,c) runs straight into the undefined transition
   F0 -- a genuine raw halt -- in exactly (3c^2 + 44c + 125)/4 steps.
2. even c: the a=1 counter block folds and the raw machine re-materializes
   a LIVE grammar record (2, (3c+14)/2, 2).  Not a death realization at all.
3. The re-entry (and the odd-c descent to death) are BOTH explained by one
   "extended abstract descent" that lets the counter reach a=0:

        (1,2,c) --drop--> (0, c+3, 2) --hydra*--> lands on m in {1,2}
        odd c  -> c+3 even -> descent lands on m=2, a=0 -> DEATH  (halt)
        even c -> c+3 odd  -> descent lands on m=1     -> MERGE   (a:=2)

   So the parity of c is the switch between direct death and resurrection.
4. Verdict: the odd-c quadratic does NOT extend to even c.  Even c is a
   genuinely separate regime (escape/re-entry), whose halting is governed
   by SafeOrbitA on the derived seed (2, (3c+14)/2, 2) -- itself open.

Cross-reference: docs/results/2026-08-31-antihydra-parity.md (odd formula,
even gap flagged open) and docs/results/2026-09-03-lethality-and-cones.md
(first statement of the re-entry). This file is an independent reproduction
plus the analytic derivation of both branches from the extended descent.
"""

from fractions import Fraction

CODE = '1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA'


# ---------------------------------------------------------------------------
# Raw Turing machine (verbatim mirror of the Lean `instr` table)
# ---------------------------------------------------------------------------
def parse(code):
    tbl = {}
    for i, blk in enumerate(code.split('_')):
        st = chr(ord('A') + i)
        for b in (0, 1):
            e = blk[3 * b:3 * b + 3]
            tbl[(st, b)] = None if e == '---' else (int(e[0]), e[1], e[2])
    return tbl


TBL = parse(code=CODE)

# Sanity: the parsed table (write, dir, next) must equal the Lean instr
# table entry by entry.  Lean instr (State,Bool) -> Instr{next,write,dir};
# F0 is the sole undefined (halt) transition.
LEAN_INSTR = {
    ('A', 0): (1, 'R', 'B'), ('A', 1): (1, 'R', 'A'),
    ('B', 0): (0, 'L', 'C'), ('B', 1): (1, 'L', 'E'),
    ('C', 0): (1, 'L', 'D'), ('C', 1): (1, 'L', 'C'),
    ('D', 0): (1, 'L', 'A'), ('D', 1): (0, 'L', 'B'),
    ('E', 0): (1, 'L', 'F'), ('E', 1): (1, 'R', 'E'),
    ('F', 0): None,          ('F', 1): (0, 'R', 'A'),
}
for k, v in LEAN_INSTR.items():
    assert TBL[k] == v, (k, TBL[k], v)


def astep(s):
    """Exact mirror of AntihydraRawTM.astep."""
    a, m, c = s
    if m >= 3:
        return (a, m - 2, c + 3)
    if m == 2:
        return (a - 1, c + 3, 2) if a >= 2 else None
    if m == 1:
        return (a + 2, c + 2, 2)
    return None


def materialize(s, p=0):
    """Realize (a,m,c) as a raw config per the Lean `Realizes` grammar:
    1^a ending at p, gap, 1^m, gap, 1^c, head on fresh frontier, state B."""
    a, m, c = s
    tape = {}
    for i in range(a):
        tape[p - i] = 1
    for i in range(m):
        tape[p + 2 + i] = 1
    for i in range(c):
        tape[p + 3 + m + i] = 1
    return tape, p + 3 + m + c, 'B'


def raw_halt_steps(s, max_steps):
    """Run the raw machine from materialize(s).  Return the exact step
    count at the F0 halt, or None if it did not halt within max_steps."""
    tape, pos, st = materialize(s)
    for t in range(max_steps):
        b = tape.get(pos, 0)
        tr = TBL[(st, b)]
        if tr is None:          # F0: the undefined transition = raw halt
            return t
        w, d, ns = tr
        if w:
            tape[pos] = 1
        elif pos in tape:
            del tape[pos]
        pos += 1 if d == 'R' else -1
        st = ns
    return None


def first_reentry(s, max_steps):
    """Run raw from materialize(s); return the first LIVE grammar record
    (state B on a fresh frontier realizing some (a,m,c) with a,m,c>=1)
    reached, as ('reentry', step, (a,m,c)); or ('halt', step, None) if it
    hits F0 first; or ('escape', max_steps, None)."""
    tape, pos, st = materialize(s)
    for t in range(max_steps):
        b = tape.get(pos, 0)
        tr = TBL[(st, b)]
        if tr is None:
            return ('halt', t, None)
        w, d, ns = tr
        if w:
            tape[pos] = 1
        elif pos in tape:
            del tape[pos]
        pos += 1 if d == 'R' else -1
        st = ns
        if st == 'B':
            rec = _read_grammar(tape, pos)
            if rec is not None:
                return ('reentry', t + 1, rec)
    return ('escape', max_steps, None)


def _read_grammar(tape, pos):
    """Read (a,m,c) off a state-B tape with head at `pos` on a fresh
    frontier: everything at/right of pos is 0, and to the left the pattern
    is 1^c 0 1^m 0 1^a (reading leftward from the frontier).  None if the
    tape is not in canonical record form."""
    ones = [q for q, v in tape.items() if v == 1]
    if not ones:
        return None
    if any(q >= pos for q in ones):
        return None

    def run_left(j):
        n = 0
        while tape.get(pos - j, 0) == 1:
            n += 1
            j += 1
        return n, j

    c, j = run_left(1)            # 1^c immediately left of the frontier gap
    if tape.get(pos - j, 0) != 0:
        return None
    j += 1
    m, j = run_left(j)            # 1^m
    if m == 0 or tape.get(pos - j, 0) != 0:
        return None
    j += 1
    a, j = run_left(j)            # 1^a (the counter)
    if a == 0:
        return None
    # nothing further left may be 1
    lo = min(ones)
    if any(tape.get(pos - k, 0) == 1 for k in range(j, pos - lo + 1)):
        return None
    return (a, m, c)


# ---------------------------------------------------------------------------
# The "extended abstract descent": astep but allowing the counter to hit 0.
# This is the abstract shadow of what the raw machine does to (1,2,c).
# ---------------------------------------------------------------------------
def extended_step(s):
    """astep, except a drop at a=1 is allowed to send the counter to 0
    (physically the counter block just vanishes) instead of dying, and a
    state with m=2, a=0 is the genuine terminal death."""
    a, m, c = s
    if m >= 3:
        return (a, m - 2, c + 3)
    if m == 2:
        if a >= 1:
            return (a - 1, c + 3, 2)   # a=1 -> (0, c+3, 2); a>=2 = normal drop
        return None                    # a=0, m=2 : genuine death
    if m == 1:
        return (a + 2, c + 2, 2)
    return None


def descent_landing(c):
    """Trace the extended descent from (1,2,c) until the counter returns to
    a>=1 (a re-entry) or the orbit dies.  Return ('death', state) or
    ('reentry', state)."""
    s = (1, 2, c)
    for _ in range(10 * c + 100):
        a, m, _c = s
        if a >= 1 and (a, m) != (1, 2) and not (a == 0):
            return ('reentry', s)
        ns = extended_step(s)
        if ns is None:
            return ('death', s)
        s = ns
        if s[0] >= 1 and not (s[0] == 1 and s[1] == 2):
            return ('reentry', s)
    return ('nolanding', s)


# ---------------------------------------------------------------------------
# Abstract "true fate" fold: iterate the ordinary orbit, and whenever it
# crosses a boundary (1,2,c) resolve it by parity (odd = halt, even =
# re-enter the derived LIVE seed).  Fast surrogate for the raw fate.
# ---------------------------------------------------------------------------
def true_fate(seed, max_iters):
    a, m, c = seed
    reentries = 0
    for i in range(max_iters):
        if (a, m) == (1, 2):
            if c % 2 == 1:
                return ('genuine-halt', i, reentries, c)
            a, m, c = 2, (3 * c + 14) // 2, 2      # even re-entry
            reentries += 1
            continue
        ns = astep((a, m, c))
        if ns is None:
            return ('other-death', i, reentries, (a, m, c))
        a, m, c = ns
    return ('survives', max_iters, reentries, (a, m, c))


ODD_FORMULA = lambda c: (3 * c * c + 44 * c + 125) // 4


def oddc_decomposition(c):
    """Exact analytic decomposition of the odd-c raw halt time from the
    extended descent plus the per-rule raw cost model:

        drop  (1,2,c) -> (0,c+3,2)         costs 2c + 16
        J = (c+1)/2 hydra steps down the m-ladder, step j (m=c+3-2j,
            current c-value = 2+3j) costs 2*(2+3j) + 11 = 6j + 15
        the ladder lands on (0, 2, cfinal), cfinal = (3c+7)/2, whose raw
            terminal-death tail costs cfinal + 5 raw steps.

    Sum = (2c+16) + (3J^2+12J) + (cfinal+5) = (3c^2 + 44c + 125)/4.
    Returns (predicted_total, (drop, ladder, tail, cfinal))."""
    assert c % 2 == 1
    J = (c + 1) // 2
    drop = 2 * c + 16
    ladder = sum(6 * j + 15 for j in range(J))    # = 3J^2 + 12J
    cfinal = (3 * c + 7) // 2                       # = 2 + 3J
    tail = cfinal + 5
    return drop + ladder + tail, (drop, ladder, tail, cfinal)


if __name__ == '__main__':
    print("=" * 72)
    print("ANTIHYDRA even-c characterization of the dying family (1,2,c)")
    print("(measurement of the abstract/raw map; does NOT touch SafeOrbitA)")
    print("=" * 72)

    # -- 0. death set of the abstract map -----------------------------------
    print("\n[0] Abstract death set D (astep = none), small scan:")
    deaths = [(a, m, c) for a in range(4) for m in range(4)
              for c in range(1, 3) if astep((a, m, c)) is None]
    print("    (a,m,c) with astep=none for a,m<4, c in {1,2}:")
    print("   ", deaths)
    print("    realizable (a,m,c>=1) death states: "
          + str([d for d in deaths if d[0] >= 1 and d[1] >= 1 and d[2] >= 1]))
    print("    -> the only realizable dying family is (1, 2, c).")

    # -- 1. odd-c formula, direct raw simulation ----------------------------
    print("\n[1] ODD c: raw halt time vs (3c^2 + 44c + 125)/4")
    miss = 0
    checked = 0
    worst = None
    for c in range(1, 500, 2):
        t = raw_halt_steps((1, 2, c), 10_000_000)
        f = ODD_FORMULA(c)
        checked += 1
        if t != f:
            miss += 1
            if miss <= 5:
                print(f"    MISMATCH c={c}: raw={t} formula={f}")
        worst = (c, t, f)
    print(f"    odd c = 1,3,...,499  ({checked} values): mismatches = {miss}")
    print(f"    largest exhaustive case c={worst[0]}: raw halt = {worst[1]}"
          f"  (formula {worst[2]})")
    for c in (999, 2001, 4999):
        t = raw_halt_steps((1, 2, c), 200_000_000)
        print(f"    spot check c={c}: raw halt = {t}  formula ="
              f" {ODD_FORMULA(c)}  match={t == ODD_FORMULA(c)}")
    # closed-form structure
    print("    second difference f(c+2)-f(c) = 3c+25 (fixed-slope quadratic).")
    # analytic decomposition (extended descent + raw cost model) vs raw sim
    dmiss = 0
    for c in range(1, 500, 2):
        pred, parts = oddc_decomposition(c)
        raw = raw_halt_steps((1, 2, c), 10_000_000)
        if not (pred == ODD_FORMULA(c) == raw):
            dmiss += 1
    print(f"    decomposition (2c+16)+(3J^2+12J)+(cfinal+5) == raw halt"
          f" for all odd c in 1..499: mismatches = {dmiss}")
    for c in (1, 3, 99):
        pred, (drop, ladder, tail, cf) = oddc_decomposition(c)
        print(f"      c={c:3d}: drop={drop} + ladder={ladder} +"
              f" tail(cfinal={cf})={tail} = {pred} = f(c)")

    # -- 2. the extended-descent derivation of BOTH branches ----------------
    print("\n[2] Extended abstract descent (1,2,c) --drop--> (0,c+3,2) --hydra*-->")
    print("    parity of c decides where the m-ladder lands:")
    for c in range(1, 13):
        kind, s = descent_landing(c)
        note = "DEATH (m=2,a=0)" if kind == 'death' else f"re-enter {s}"
        print(f"    c={c:2d}: c+3={c+3:2d} ({'even' if (c+3)%2==0 else 'odd '})"
              f" -> {kind:7s}  {note}")

    # -- 3. even-c re-entry, raw-verified -----------------------------------
    print("\n[3] EVEN c: first LIVE grammar re-entry read back off the raw tape")
    print("    predicted re-entry (2, (3c+14)/2, 2):")
    allok = True
    for c in range(2, 41, 2):
        kind, step, rec = first_reentry((1, 2, c), 5_000_000)
        pred = (2, (3 * c + 14) // 2, 2)
        ok = (kind == 'reentry' and rec == pred)
        allok &= ok
        print(f"    c={c:3d}: {kind:8s} at raw step {step:8d}  read={rec}"
              f"  pred={pred}  match={ok}")
    print(f"    all even c in 2..40 match the re-entry formula: {allok}")

    # -- 4. fold vs direct raw, on cases that halt within reach -------------
    print("\n[4] Fold (abstract) fate vs direct raw halt, small even c")
    print("    (fold: cross a (1,2,odd) boundary = halt; (1,2,even) = re-enter)")
    for c in (2, 14, 16):
        ff = true_fate((1, 2, c), 2_000_000)
        raw = raw_halt_steps((1, 2, c), 30_000_000)
        print(f"    c={c:3d}: fold={ff}")
        print(f"           direct raw halt = {raw}")

    # -- 5. population split of even c --------------------------------------
    print("\n[5] Even-c population split via the abstract fold (fast surrogate)")
    print("    each is governed by SafeOrbitA on derived seed (2,(3c+14)/2,2):")
    for c in (2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 50, 100, 1000):
        ff = true_fate((1, 2, c), 20_000_000)
        tag = ff[0]
        if tag == 'genuine-halt':
            detail = f"reaches odd (1,2,{ff[3]}) after {ff[2]} re-entries"
        elif tag == 'survives':
            detail = (f"no death in {ff[1]} abstract steps; "
                      f"grew to {ff[3]}")
        else:
            detail = str(ff)
        print(f"    c={c:5d}: {tag:13s}  {detail}")

    # -- 6. unified-vs-separate verdict ------------------------------------
    print("\n[6] VERDICT")
    print("    - odd c : closed-form raw halt (3c^2+44c+125)/4, a true halt.")
    print("    - even c: NO closed-form halt time.  The a=1 block folds and")
    print("      the machine re-enters the LIVE seed (2,(3c+14)/2,2); its raw")
    print("      fate is exactly the Antihydra fate of that seed (open).")
    print("    - The odd-c quadratic does NOT extend to even c: even c is a")
    print("      genuinely separate regime (resurrection, not death).")
    print("    - What stays open: whether any given even-c derived orbit ever")
    print("      reaches an ODD boundary (halt) or survives forever -- an")
    print("      instance of SafeOrbitA itself, not decidable by a formula.")

"""Unconditionality hunt for the BB(6) holdout set.

Goal: find holdout machines that admit a GENUINE UNCONDITIONAL non-halting
proof, as opposed to the program's conditional (Collatz-class) closures.

Two honest routes are searched; both certify non-halting without crossing a
Collatz-orbit conjecture.

ROUTE A -- EVENTUAL PERIODICITY (translated cycle, shift may be zero).
  A configuration that repeats up to a fixed spatial shift, same state, every
  P steps after a transient T, never halts, unconditionally.  Detection is a
  two-phase, fail-closed procedure:
    (1) screen: at every record (fresh-extreme) event on the growing side,
        hash (state, fixed window behind the head); a repeat with a consistent
        shift is a CANDIDATE.  Pure (in-place) cycles are screened separately
        by hashing the full bounded configuration.
    (2) verify: re-simulate from scratch, and confirm the exact translated-
        cycle relation holds over several full periods, tracking the leftward
        excursion depth so the window provably covers the whole active region.
  Only a verified cycle is reported.

ROUTE B -- MONOTONE DIVERGENCE WITH UNREACHABLE HALT.
  A strictly monotone unbounded quantity (word length) whose halt probe
  requires reading a value the diverging orbit provably never realises.  The
  detector flags the STRUCTURAL preconditions (monotone frontier growth plus a
  probe that on the observed orbit only ever fires at fresh-frontier cells).
  It does NOT by itself prove unreachability: for a Collatz-class holdout the
  "unreachability" is exactly the orbit conjecture.  Route-B reporting is
  therefore explicit that a flag is a precondition, not a proof, and separates
  a genuine bounded-region argument (proof) from a Collatz-class one (not).

Run:
  python3 uncond_hunt.py --screen        broad screen, all 1094, writes jsonl
  python3 uncond_hunt.py --verify FILE    verify candidates from a screen file
  python3 uncond_hunt.py --selfcheck      sanity: a hand-built translated cycler
"""
from __future__ import annotations
import json
import pathlib
import sys
from collections import Counter
from multiprocessing import Pool

ROOT = pathlib.Path(__file__).resolve().parents[2]
SWEEP = ROOT / "experiments" / "outputs" / "d4_fullsweep.jsonl"
AUDIT = ROOT / "experiments" / "outputs" / "audit_openset.jsonl"
OUT = ROOT / "experiments" / "outputs" / "uncond_hunt.jsonl"


def parse(code):
    """(state,read) -> (write, dir 0=L/1=R, next state) or None (undefined)."""
    tbl = {}
    for i, blk in enumerate(code.split("_")):
        for r in (0, 1):
            e = blk[3 * r:3 * r + 3]
            tbl[(i, r)] = (None if e == "---"
                           else (int(e[0]), 0 if e[1] == "L" else 1,
                                 ord(e[2]) - 65))
    return tbl


def trans_list(code):
    tbl = parse(code)
    nst = len(code.split("_"))
    return [tbl.get((s, r)) for s in range(nst) for r in range(2)], nst


# --------------------------------------------------------------------------
# Phase 1: broad screen
# --------------------------------------------------------------------------

def screen(code, horizon=10_000_000, window=1024, cap_entries=250_000,
           bounded_span=500, bounded_entries=500_000,
           verify_inline=False):
    """One simulation, fail-closed, that reports the first evidence of

      - HALT  (undefined step reached; a genuine finding),
      - a PURE CYCLE  (full config repeats exactly; shift 0),
      - a TRANSLATED-CYCLE CANDIDATE  (state+window repeat, consistent shift),

    or NONE up to the horizon.  Windows are hashed, so a false hash collision
    is possible; every candidate is re-checked by verify_translated below.

    While the visited span stays <= bounded_span, the full configuration is
    hashed each step to catch a pure (in-place) cycle; this is disabled once
    the tape grows past bounded_span (a growing machine is not an in-place
    cycler) so the per-step cost stays low.  The 13 audit-bounded machines,
    whose spans creep past this, are handled separately by bounded_longrun.
    """
    trans, nst = trans_list(code)
    size = 1 << 16
    tape = bytearray(size)
    origin = size // 2
    pos = origin
    st = 0
    lo = hi = origin

    # record-window screen state, per side.  A single window match is a weak
    # signal (structured tapes collide on a fixed window), so a candidate is
    # only raised when the SAME (side,state,window) recurs three times in
    # arithmetic progression -- two consecutive periods with a consistent shift
    # and equal spacing.  A true translated cycler produces infinitely many
    # such records; a hash coincidence almost never makes three.
    seen = {}                      # key -> (t, pos)  most recent occurrence
    seen2 = {}                     # key -> (dt, dp) of the last consistent gap
    frozen = False

    # pure-cycle (bounded) screen state
    full_seen = {}
    bounded = True

    def grow():
        nonlocal tape, size, origin, pos, lo, hi
        new = bytearray(size * 2)
        shift = size // 2
        new[shift:shift + size] = tape
        tape, origin, pos, lo, hi = new, origin + shift, pos + shift, \
            lo + shift, hi + shift
        size = len(tape)

    t = 0
    while t < horizon:
        b = tape[pos]
        tr = trans[st * 2 + b]
        if tr is None:
            return dict(kind="HALT", t=t)
        w, d, ns = tr
        tape[pos] = w
        if d:
            pos += 1
        else:
            pos -= 1

        record = None
        if pos > hi:
            hi = pos
            record = "R"
            if pos >= size - 2:
                grow()
        elif pos < lo:
            lo = pos
            record = "L"
            if pos <= 1:
                grow()

        st = ns
        t += 1

        # translated-cycle screen at record events on the growing frontier
        if record is not None and not frozen:
            p = pos
            if record == "R":
                left = p - window + 1
                win = bytes(tape[max(lo, left):p + 1])
            else:
                right = p + window - 1
                win = bytes(tape[p:min(hi, right) + 1])
            # hash the window to bound memory; verify_translated is the exact
            # safety net for the rare hash coincidence.
            key = (record, st, hash(win))
            prev = seen.get(key)
            if prev is not None:
                pt, pp = prev
                dt, dp = t - pt, p - pp
                last = seen2.get(key)
                if last is not None and last == (dt, dp) and dp != 0:
                    # third occurrence, arithmetic progression -> candidate.
                    # t1 = the FIRST of the three (pt - dt), for a clean
                    # transient; verify starts there.
                    cand = dict(kind="TC_CANDIDATE", side=record, state=st,
                                t1=pt - dt, t2=pt, p1=pp - dp, p2=pp,
                                delta=dp, period=dt, window=window)
                    if not verify_inline:
                        return cand
                    v = verify_translated(code, cand["t1"], cand["t2"],
                                          cand["delta"], record, periods=3)
                    if v.get("verified"):
                        cand["kind"] = "TC_VERIFIED"
                        cand["verify"] = v
                        return cand
                    # false positive: drop this key's history, keep screening
                    seen.pop(key, None)
                    seen2.pop(key, None)
                    continue
                seen2[key] = (dt, dp)
                seen[key] = (t, p)
            else:
                seen[key] = (t, p)
                if len(seen) >= cap_entries:
                    frozen = True

        # pure-cycle screen while the tape stays bounded
        if bounded:
            span = hi - lo
            if span > bounded_span or len(full_seen) > bounded_entries:
                bounded = False
                full_seen = None
            else:
                fkey = (st, pos - lo, hash(bytes(tape[lo:hi + 1])))
                if fkey in full_seen:
                    return dict(kind="PURE_CYCLE", t1=full_seen[fkey], t2=t,
                                period=t - full_seen[fkey])
                full_seen[fkey] = t

    return dict(kind="NONE", t=t, frozen=frozen, bounded=bounded)


# --------------------------------------------------------------------------
# Phase 2: rigorous verification of a translated-cycle candidate
# --------------------------------------------------------------------------

def verify_translated(code, t1, t2, delta, side, periods=3):
    """Re-simulate and CONFIRM the translated-cycle certificate.

    The certificate (right-growing case; left is the mirror): at the transient
    time t1 and at t1+P the machine is in the same state, the head has advanced
    by delta = shift, and the tape window [head - L, head] -- where L is the
    deepest leftward reach during the period -- is identical after shifting by
    delta.  Because the head never reads left of head-L during the period and
    the right side is blank at a record, the next period is forced to repeat
    the same finite behaviour shifted by delta.  We require the relation to
    hold exactly for `periods` consecutive periods.

    Returns a dict with verified=True/False and the exact (T, P, shift).
    """
    P = t2 - t1
    trans, nst = trans_list(code)

    # simulate once, snapshotting full tape (as dict) and head/state at the
    # period boundaries t1, t1+P, ..., t1+periods*P, tracking per-interval
    # min/max head positions.
    tape = {}
    pos = 0
    st = 0
    snaps = {}            # step -> (state, head, frozen dict copy)
    boundaries = [t1 + k * P for k in range(periods + 1)]
    bset = set(boundaries)
    interval_reach = []   # (min_pos, max_pos) per interval
    cur_min = cur_max = 0
    limit = boundaries[-1]
    t = 0
    while t <= limit:
        if t in bset:
            snaps[t] = (st, pos, dict(tape))
            cur_min = cur_max = pos
        if t == limit:
            break
        b = tape.get(pos, 0)
        tr = trans[st * 2 + b]
        if tr is None:
            return dict(verified=False, reason="halt during verify", t=t)
        w, d, ns = tr
        if w:
            tape[pos] = w
        elif pos in tape:
            del tape[pos]
        pos = pos + 1 if d else pos - 1
        st = ns
        if pos < cur_min:
            cur_min = pos
        if pos > cur_max:
            cur_max = pos
        t += 1
        if t in bset:
            interval_reach.append((cur_min, cur_max))

    # check each consecutive pair of boundaries
    for k in range(periods):
        ta, tb = boundaries[k], boundaries[k + 1]
        sa, pa, tapea = snaps[ta]
        sb, pb, tapeb = snaps[tb]
        if sa != sb:
            return dict(verified=False, reason="state mismatch", k=k)
        if pb - pa != delta:
            return dict(verified=False, reason="shift mismatch", k=k,
                        got=pb - pa, want=delta)
        cmin, cmax = interval_reach[k]
        # rigorous windowed check.  During the period the head reads only cells
        # in [cmin, cmax]; everything outside is blank (right of the record on
        # the growing side) or untouched.  A growing translated cycler leaves a
        # growing trail, so whole-line equality is WRONG; the certificate is
        # that the ACTIVE window reproduces itself shifted by delta:
        #     tapeb[y + delta] == tapea[y]   for all y in [cmin, cmax].
        # state + matching window + blank exterior then force the next period
        # to repeat the same finite behaviour shifted by delta, forever.
        # Confirmed over `periods` consecutive periods for margin.
        for y in range(cmin, cmax + 1):
            if tapeb.get(y + delta, 0) != tapea.get(y, 0):
                return dict(verified=False, reason="window mismatch",
                            k=k, y=y)
    return dict(verified=True, T=t1, P=P, shift=delta, side=side,
                periods=periods)


def verify_pure_cycle(code, t1, t2):
    """Re-simulate and confirm an exact in-place cycle: state, head position,
    and the entire tape are identical at t1 and t2.  A repeat then loops
    forever (shift 0), unconditional non-halting.  Hash coincidences from the
    screen are filtered here by exact comparison."""
    trans, nst = trans_list(code)
    tape = {}
    pos = 0
    st = 0
    snap = {}
    t = 0
    while t <= t2:
        if t == t1 or t == t2:
            snap[t] = (st, pos, dict(tape))
        if t == t2:
            break
        b = tape.get(pos, 0)
        tr = trans[st * 2 + b]
        if tr is None:
            return dict(verified=False, reason="halt during verify", t=t)
        w, d, ns = tr
        if w:
            tape[pos] = w
        elif pos in tape:
            del tape[pos]
        pos = pos + 1 if d else pos - 1
        st = ns
        t += 1
    sa, pa, ta = snap[t1]
    sb, pb, tb = snap[t2]
    if sa == sb and pa == pb and ta == tb:
        return dict(verified=True, T=t1, P=t2 - t1, shift=0)
    return dict(verified=False, reason="config mismatch")


# --------------------------------------------------------------------------
# Route B: structural screen (preconditions only)
# --------------------------------------------------------------------------

def route_b_screen(code, horizon=10_000_000, sample=64):
    """Structural preconditions for monotone divergence with unreachable halt.

    Reports:
      - monotone: is the growing-side word length (hi-lo) non-decreasing from
        some point (records only add, never retract)?  For a one-directional
        machine this is automatic; the useful signal is whether the SLOW side
        ever retracts.
      - probe_read_at_fresh: over the run, every time the machine enters the
        undefined state, was the cell it read a fresh-frontier zero (so a
        undef_read==1 halt never fires), or was it always a grown cell?
    This is a PRECONDITION, never a proof of unreachability.
    """
    trans, nst = trans_list(code)
    tbl = parse(code)
    und = [k for k, v in tbl.items() if v is None]
    if len(und) != 1:
        return dict(ok=False, reason="not one undefined transition")
    us, ur = und[0]

    size = 1 << 16
    tape = bytearray(size)
    origin = size // 2
    pos = origin
    st = 0
    lo = hi = origin
    maxvisit = bytearray(size)   # 1 if cell was ever written/visited-nonfresh

    def grow():
        nonlocal tape, size, origin, pos, lo, hi, maxvisit
        new = bytearray(size * 2)
        nm = bytearray(size * 2)
        shift = size // 2
        new[shift:shift + size] = tape
        nm[shift:shift + size] = maxvisit
        tape, maxvisit = new, nm
        origin, pos, lo, hi = origin + shift, pos + shift, lo + shift, hi + shift
        size = len(tape)

    # Each time the machine is in the undefined state us, it reads the SAFE
    # bit 1-ur on any non-halting orbit (reading ur would halt).  The Route B
    # question is WHERE that safe read sits: is the cell always solidly grown
    # (deep interior, value a maintained invariant) or is it ever a fresh
    # frontier cell whose safe value is only the incidental blank?  We record
    # the freshness and the distance from the nearer frontier.
    safe_reads = 0
    safe_reads_fresh = 0          # safe read on a never-before-visited cell
    min_front_dist = None         # min distance of a safe read from a frontier
    halt_would_fire = 0           # times reading ur in us would occur (=halt)
    span_prev = 0
    monotone_span = True
    t = 0
    while t < horizon:
        b = tape[pos]
        if st == us:
            if b == ur:
                return dict(ok=True, halted=True, t=t)   # fail-closed
            safe_reads += 1
            if maxvisit[pos] == 0:
                safe_reads_fresh += 1
            fd = min(pos - lo, hi - pos)
            if min_front_dist is None or fd < min_front_dist:
                min_front_dist = fd
        tr = trans[st * 2 + b]
        if tr is None:
            return dict(ok=True, halted=True, t=t)
        w, d, ns = tr
        tape[pos] = w
        maxvisit[pos] = 1
        pos = pos + 1 if d else pos - 1
        if pos > hi:
            hi = pos
            if pos >= size - 2:
                grow()
        elif pos < lo:
            lo = pos
            if pos <= 1:
                grow()
        st = ns
        t += 1
        span = hi - lo
        if span < span_prev:
            monotone_span = False
        span_prev = span

    return dict(ok=True, halted=False, undef_state=chr(65 + us), undef_read=ur,
                safe_reads=safe_reads, safe_reads_fresh=safe_reads_fresh,
                min_front_dist=min_front_dist,
                monotone_span=monotone_span, final_span=hi - lo, t=t)


# --------------------------------------------------------------------------
# drivers
# --------------------------------------------------------------------------

def all_codes():
    return [json.loads(l)["code"] for l in open(SWEEP) if l.strip()]


def _screen_job(args):
    code, horizon, window = args
    r = screen(code, horizon=horizon, window=window)
    r["code"] = code
    return r


def run_screen(horizon=10_000_000, window=1024, workers=6):
    codes = all_codes()
    print(f"screening {len(codes)} machines to {horizon:.0e} steps, "
          f"window={window}", flush=True)
    rows = []
    args = [(c, horizon, window) for c in codes]
    with Pool(workers, maxtasksperchild=20) as pool:
        for i, r in enumerate(pool.imap_unordered(_screen_job, args, chunksize=2)):
            rows.append(r)
            if (i + 1) % 50 == 0:
                print(f"  {i + 1}/{len(codes)}", flush=True)
    rows.sort(key=lambda r: r["code"])
    with open(OUT, "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    hist = Counter(r["kind"] for r in rows)
    print("screen histogram:", dict(hist), flush=True)
    print("wrote", OUT, flush=True)
    return rows


BOUNDED_OUT = ROOT / "experiments" / "outputs" / "uncond_bounded_longrun.jsonl"


def bounded_longrun(code, horizon=50_000_000, span_cap=200, entry_cap=3_000_000):
    """Long-run analysis for a machine the audit called bounded (no growing
    frontier past its budget).  Distinguishes a genuinely bounded / eventually
    periodic machine (Route A: an in-place or translated cycle) from a slow
    diverger (span keeps creeping, Collatz-class).  Exact cycle detection runs
    while span stays <= span_cap; span checkpoints record the trajectory.
    O(1) memory beyond the capped config set."""
    trans, nst = trans_list(code)
    size = 1 << 12
    tape = bytearray(size)
    origin = size // 2
    pos = origin
    st = 0
    lo = hi = origin
    seen = {}
    capped = False
    maxspan = 0
    last_growth_t = 0
    checkpoints = {int(horizon * f) for f in (0.2, 0.4, 0.6, 0.8, 1.0)}
    span_at = []
    for t in range(horizon):
        b = tape[pos]
        tr = trans[st * 2 + b]
        if tr is None:
            return dict(code=code, halt=t, maxspan=maxspan)
        w, d, ns = tr
        tape[pos] = w
        grew = False
        if d:
            pos += 1
        else:
            pos -= 1
        if pos > hi:
            hi = pos
            grew = True
            if pos >= size - 2:
                new = bytearray(size * 2)
                sh = size // 2
                new[sh:sh + size] = tape
                tape = new
                origin += sh
                pos += sh
                lo += sh
                hi += sh
                size *= 2
        elif pos < lo:
            lo = pos
            grew = True
            if pos <= 1:
                new = bytearray(size * 2)
                sh = size // 2
                new[sh:sh + size] = tape
                tape = new
                origin += sh
                pos += sh
                lo += sh
                hi += sh
                size *= 2
        st = ns
        if grew:
            last_growth_t = t
        span = hi - lo
        if span > maxspan:
            maxspan = span
        if not capped and span <= span_cap:
            key = (st, pos - lo, bytes(tape[lo:hi + 1]))
            if key in seen:
                return dict(code=code, cycle=[seen[key], t], period=t - seen[key],
                            maxspan=maxspan)
            seen[key] = t
            if len(seen) > entry_cap:
                capped = True
                seen = None
        if t in checkpoints:
            span_at.append([t, span])
    return dict(code=code, halt=None, cycle=None, maxspan=maxspan,
                final_span=hi - lo, last_growth_t=last_growth_t,
                span_at=span_at, capped=capped)


def run_bounded(horizon=50_000_000):
    """Long-run the 13 audit-bounded (OUT_OF_SCOPE) machines."""
    bounded = [json.loads(l)["code"] for l in open(AUDIT)
               if json.loads(l).get("verdict") == "OUT_OF_SCOPE"]
    print(f"bounded long-run: {len(bounded)} machines to {horizon:.0e}", flush=True)
    rows = []
    for c in bounded:
        r = bounded_longrun(c, horizon=horizon)
        rows.append(r)
        tag = ("HALT" if r.get("halt") is not None else
               "CYCLE" if r.get("cycle") else "slow-diverge")
        print(f"  {tag:12} maxspan={r.get('maxspan')} {c}", flush=True)
    with open(BOUNDED_OUT, "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    cyc = sum(1 for r in rows if r.get("cycle"))
    hlt = sum(1 for r in rows if r.get("halt") is not None)
    print(f"bounded: cycles={cyc} halts={hlt} "
          f"slow-divergers={len(rows) - cyc - hlt}", flush=True)
    print("wrote", BOUNDED_OUT, flush=True)
    return rows


ROUTE_B_OUT = ROOT / "experiments" / "outputs" / "uncond_route_b.jsonl"


def _route_b_job(args):
    code, horizon = args
    r = route_b_screen(code, horizon=horizon)
    r["code"] = code
    return r


def run_route_b(horizon=10_000_000, workers=6, only_ready=True):
    """Route B structural measurement over the open set (default: the 795
    ENGINE_READY machines, which have exactly one undefined transition and a
    growing frontier)."""
    ready = None
    if only_ready:
        ready = set()
        for l in open(AUDIT):
            d = json.loads(l)
            if d.get("verdict") == "ENGINE_READY":
                ready.add(d["code"])
    codes = [c for c in all_codes() if ready is None or c in ready]
    print(f"route-B on {len(codes)} machines to {horizon:.0e} steps", flush=True)
    rows = []
    args = [(c, horizon) for c in codes]
    with Pool(workers, maxtasksperchild=20) as pool:
        for i, r in enumerate(pool.imap_unordered(_route_b_job, args, chunksize=2)):
            rows.append(r)
            if (i + 1) % 50 == 0:
                print(f"  {i + 1}/{len(codes)}", flush=True)
    rows.sort(key=lambda r: r.get("code", ""))
    with open(ROUTE_B_OUT, "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    halted = [r for r in rows if r.get("halted")]
    clean = [r for r in rows if r.get("ok") and not r.get("halted")
             and r.get("safe_reads_fresh") == r.get("safe_reads")
             and r.get("safe_reads", 0) > 0]
    print(f"route-B: halted={len(halted)} all-fresh-probe={len(clean)}", flush=True)
    print("wrote", ROUTE_B_OUT, flush=True)
    return rows


def selfcheck():
    """A hand-built translated cycler must be caught and verified.

    1RB1LB_1LA... is not one; use the canonical 2-state ">>" mover:
    the machine 1RB0RA_ (state A) prints and moves right forever on blanks --
    that is a translated cycle of period 1 shift 1.  Build a 6-state code whose
    A on 0 -> write1 move R stay A: block A = '1RA' + '1RA'.
    """
    code = "1RA1RA_" + "_".join(["1RA1RA"] * 5)
    # A on 0 -> 1,R,A ; frontier advances 1 per step, state constant.
    r = screen(code, horizon=10_000, window=64)
    print("selfcheck screen:", r)
    if r["kind"] == "TC_CANDIDATE":
        v = verify_translated(code, r["t1"], r["t2"], r["delta"], r["side"])
        print("selfcheck verify:", v)
        return v.get("verified", False)
    if r["kind"] == "PURE_CYCLE":
        print("selfcheck: pure cycle (unexpected for a mover)")
    return False


if __name__ == "__main__":
    if "--selfcheck" in sys.argv:
        selfcheck()
    elif "--verify" in sys.argv:
        fn = sys.argv[sys.argv.index("--verify") + 1]
        for line in open(fn):
            r = json.loads(line)
            if r.get("kind") == "TC_CANDIDATE":
                v = verify_translated(r["code"], r["t1"], r["t2"], r["delta"],
                                      r["side"])
                print("TC ", r["code"], v)
            elif r.get("kind") == "PURE_CYCLE":
                v = verify_pure_cycle(r["code"], r["t1"], r["t2"])
                print("PC ", r["code"], v)
            elif r.get("kind") == "HALT":
                print("HALT", r["code"], "at", r.get("t"))
    elif "--bounded" in sys.argv:
        hz = 50_000_000
        for a in sys.argv[1:]:
            if a.startswith("--horizon="):
                hz = int(float(a.split("=")[1]))
        run_bounded(horizon=hz)
    elif "--route-b" in sys.argv:
        hz = 10_000_000
        for a in sys.argv[1:]:
            if a.startswith("--horizon="):
                hz = int(float(a.split("=")[1]))
        run_route_b(horizon=hz)
    else:
        hz = 10_000_000
        for a in sys.argv[1:]:
            if a.startswith("--horizon="):
                hz = int(float(a.split("=")[1]))
        run_screen(horizon=hz)

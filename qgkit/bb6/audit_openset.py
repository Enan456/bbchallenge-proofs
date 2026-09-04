"""Phase 1.1 audit harness: classify every open BB(6) machine by whether
the raw-step closure engine can close it, WITHOUT closing anything.

For each open machine a single raw simulation to 2e7 steps decides, all
fail-closed, the three axes the raw-step engine depends on (see
docs/results/2026-09-03-forward-plan.md phase 1.1 and the closures-doc
anatomy sections):

  1. HALT CHECK      -- halts within 20M steps -> verdict HALTS (a genuine
                        finding), excluded from the rest.
  2. SIDEDNESS       -- does the tape grow one side, both, or neither
                        (bounded = likely translated cycler / out of scope);
                        for two-sided, which extreme has fewer distinct
                        arrival states (the record side the engine picks).
  3. PROBE BENIGNITY -- structural, from the table: is the undefined
                        transition a halt-is-probe case (one-cell safety,
                        like d9/d14) or a neighbour-guarded pattern
                        (two-cell, like d7)?  Determined by working backward
                        one step from the '---'.
  4. FUEL GROWTH     -- records = fresh-extreme events on the growing side;
                        max record-to-record step gap vs word length over
                        the run; sub-quadratic (standard fuel
                        64*(len+64)^2 suffices) or faster (bigger fuel form).

Verdict per machine in {HALTS, ENGINE_READY, ENGINE_READY_WITH_WORK,
OUT_OF_SCOPE}.  The probe axis is reported but does not gate the verdict:
8 of the 18 known closures are two-cell and all are closed, so a neighbour
guard is within the engine's reach.  The verdict is gated by sidedness
(bounded -> OUT_OF_SCOPE) and fuel (super-quadratic -> WITH_WORK).

Run:  python3 audit_openset.py            (full sweep, writes jsonl)
      python3 audit_openset.py --selfcheck (audit the 18 known closures)
"""
from __future__ import annotations
import json
import pathlib
import sys
from collections import Counter
from multiprocessing import Pool

ROOT = pathlib.Path(__file__).resolve().parents[2]
SWEEP = ROOT / "experiments" / "outputs" / "d4_fullsweep.jsonl"
OUT = ROOT / "experiments" / "outputs" / "audit_openset.jsonl"

STEPS = 20_000_000
CAP = 40             # extent (cells) a side must exceed to count as advancing
HALF = STEPS // 2    # a side "advances" if a fresh extreme is set past here

# The 18 already-closed machines (Antihydra + the RawTM.lean tranche),
# excluded from the open set.  probe_truth records the certified corridor
# kind for the self-check.
KNOWN = {
    "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA": ("Antihydra", "two-cell"),
    "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB": ("dossier-1", "two-cell"),
    "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD": ("dossier-2", "two-cell"),
    "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE": ("dossier-3", "two-cell"),
    "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA": ("dossier-7", "two-cell"),
    "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE": ("dossier-8", "two-cell"),
    "1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB": ("dossier-9", "one-cell"),
    "1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB": ("dossier-10", "one-cell"),
    "1RB---_1LC0LD_1RD0LB_0RF1RE_1RF0RA_0LE0RC": ("dossier-11", "one-cell"),
    "1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_0RB---": ("dossier-12", "one-cell"),
    "1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE": ("dossier-13", "one-cell"),
    "1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD": ("dossier-14", "one-cell"),
    "1RB0RA_1RC0RF_1RD1LE_1RE---_1LF1LE_1RA0LE": ("dossier-15", "one-cell"),
    "1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---": ("dossier-16", "one-cell"),
    "1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF": ("dossier-17", "one-cell"),
    "1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC": ("dossier-18", "one-cell"),
    "1RB1RD_1LC0LC_0RD0LB_1RF0LE_0RD---_0RA1RC": ("rank-1", "two-cell"),
    "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB": ("Dvisetu", "two-cell"),
}


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


def probe_kind(code):
    """Classify the undefined transition by working backward one step.

    one-cell (halt-is-probe): the undefined state's own state+read is the
      fatal event; safety is a one-cell predicate on that state.
    two-cell (neighbour-guarded): the fatal read is on the ambient bit and
      the corridor must be pushed back to a predecessor, giving a two-cell
      guard.

    Rule (reproduces all 18 certified corridors):
      two-cell iff the machine dies reading a 0 (the blank bit, so a
      one-cell predicate on the undefined state would be violated at every
      fresh cell), OR the undefined state dies reading a 1 but is a single-
      predecessor satellite whose safe branch returns to that predecessor
      (the array-class case, rank-1: die on the ambient 1-block).
      Otherwise one-cell.
    """
    tbl = parse(code)
    und = [k for k, v in tbl.items() if v is None]
    if len(und) != 1:
        return "anomalous", {"n_undefined": len(und)}
    sh, rh = und[0]
    preds = [(sp, rp, v) for (sp, rp), v in tbl.items()
             if v is not None and v[2] == sh]
    sib = tbl[(sh, 1 - rh)]                 # safe branch of the undefined state
    safe_target = sib[2] if sib is not None else None
    if rh == 0:
        kind = "two-cell"
    elif len(preds) == 1 and safe_target == preds[0][0]:
        kind = "two-cell"                   # satellite of its predecessor
    else:
        kind = "one-cell"
    meta = {"undef_state": chr(65 + sh), "undef_read": rh,
            "n_preds": len(preds)}
    return kind, meta


def simulate(code, steps=STEPS):
    """One raw simulation gathering the four axes streaming, O(1) memory
    beyond the tape.  Fail-closed: a halt (undefined step) is reported."""
    tbl = parse(code)
    nst = len(code.split("_"))
    trans = [tbl.get((s, r)) for s in range(nst) for r in range(2)]

    size = 1 << 16
    tape = bytearray(size)
    origin = size // 2
    pos = origin
    st = 0
    lo = hi = origin

    # per-side streaming stats
    l_states = set()
    r_states = set()
    l_last = r_last = 0
    l_prevstep = r_prevstep = 0
    l_maxgap = r_maxgap = 0
    l_len_at = r_len_at = 0

    halted = None
    t = 0
    while t < steps:
        b = tape[pos]
        tr = trans[st * 2 + b]
        if tr is None:
            halted = t
            break
        w, d, ns = tr
        tape[pos] = w
        pos = pos + 1 if d else pos - 1
        if pos > hi:
            hi = pos
            r_states.add(ns)
            r_last = t
            gap = t - r_prevstep
            if gap > r_maxgap:
                r_maxgap = gap
                r_len_at = hi - lo
            r_prevstep = t
            if pos >= size - 2:
                tape, origin, pos, lo, hi = _grow(tape, size, origin,
                                                  pos, lo, hi)
                size = len(tape)
        elif pos < lo:
            lo = pos
            l_states.add(ns)
            l_last = t
            gap = t - l_prevstep
            if gap > l_maxgap:
                l_maxgap = gap
                l_len_at = hi - lo
            l_prevstep = t
            if pos <= 1:
                tape, origin, pos, lo, hi = _grow(tape, size, origin,
                                                  pos, lo, hi)
                size = len(tape)
        st = ns
        t += 1

    r_ext = hi - origin
    l_ext = origin - lo
    r_adv = r_last > HALF and r_ext > CAP
    l_adv = l_last > HALF and l_ext > CAP
    return dict(
        halted=halted, steps=t,
        r_ext=r_ext, l_ext=l_ext, r_adv=r_adv, l_adv=l_adv,
        l_states=sorted(l_states), r_states=sorted(r_states),
        l_nstate=len(l_states), r_nstate=len(r_states),
        l_maxgap=l_maxgap, r_maxgap=r_maxgap,
        l_len_at=l_len_at, r_len_at=r_len_at,
    )


def _grow(tape, size, origin, pos, lo, hi):
    """Double the tape, copying the used span into the middle."""
    new = bytearray(size * 2)
    shift = size // 2
    new[shift:shift + size] = tape
    return new, origin + shift, pos + shift, lo + shift, hi + shift


def classify(code):
    """Full per-machine audit -> the emitted row.  The 20M-step budget
    bounds runtime, so no wall-time signal is needed (and none is used:
    SIGALRM deadlocks a multiprocessing Pool)."""
    s = simulate(code)
    pkind, pmeta = probe_kind(code)

    # HALT
    if s["halted"] is not None:
        return dict(code=code, verdict="HALTS",
                    sidedness=None, record_side=None, probe_kind=pkind,
                    max_gap=None, word_len_at_max=None, fuel_ok=None,
                    halt_step=s["halted"], probe_meta=pmeta)

    # SIDEDNESS
    if s["r_adv"] and s["l_adv"]:
        sidedness = "two-sided"
    elif s["r_adv"]:
        sidedness = "one-sided-right"
    elif s["l_adv"]:
        sidedness = "one-sided-left"
    else:
        sidedness = "bounded"

    # record side + fuel stats from the record (growing) side
    if sidedness == "two-sided":
        # the side with fewer distinct arrival states is the record side
        if s["r_nstate"] <= s["l_nstate"]:
            record_side, maxgap, lenat = "right", s["r_maxgap"], s["r_len_at"]
        else:
            record_side, maxgap, lenat = "left", s["l_maxgap"], s["l_len_at"]
    elif sidedness == "one-sided-right":
        record_side, maxgap, lenat = "right", s["r_maxgap"], s["r_len_at"]
    elif sidedness == "one-sided-left":
        record_side, maxgap, lenat = "left", s["l_maxgap"], s["l_len_at"]
    else:
        record_side, maxgap, lenat = None, None, None

    # FUEL: standard budget 64*(len+64)^2
    if maxgap is not None:
        budget = 64 * (lenat + 64) * (lenat + 64)
        fuel_ok = maxgap <= budget
    else:
        fuel_ok = None

    row = dict(code=code, sidedness=sidedness, record_side=record_side,
               probe_kind=pkind, max_gap=maxgap, word_len_at_max=lenat,
               fuel_ok=fuel_ok, probe_meta=pmeta,
               l_nstate=s["l_nstate"], r_nstate=s["r_nstate"])

    # VERDICT
    if sidedness == "bounded":
        row["verdict"] = "OUT_OF_SCOPE"
        row["reason"] = "bounded tape (no growing frontier; likely cycler)"
    elif fuel_ok is False:
        row["verdict"] = "ENGINE_READY_WITH_WORK"
        row["reason"] = "record gap exceeds quadratic fuel; needs bigger form"
    else:
        row["verdict"] = "ENGINE_READY"
    return row


def open_set():
    rows = [json.loads(l) for l in open(SWEEP) if l.strip()]
    codes = [r["code"] for r in rows if r["code"] not in KNOWN]
    return codes


def main():
    codes = open_set()
    print(f"open machines: {len(codes)} "
          f"(1094 sweep - {sum(1 for r in map(json.loads, open(SWEEP)) if r['code'] in KNOWN)} known)",
          flush=True)
    results = []
    with Pool(6, maxtasksperchild=40) as pool:
        for i, row in enumerate(pool.imap_unordered(classify, codes, chunksize=4)):
            results.append(row)
            if (i + 1) % 50 == 0:
                print(f"  {i + 1}/{len(codes)}", flush=True)
    results.sort(key=lambda r: r["code"])
    with open(OUT, "w") as f:
        for r in results:
            f.write(json.dumps(r) + "\n")
    hist = Counter(r["verdict"] for r in results)
    print("verdict histogram:", dict(hist), flush=True)
    print("wrote", OUT, flush=True)
    return results


def selfcheck():
    """Audit the 18 known closures; every one must classify ENGINE_READY,
    and probe_kind must match the certified corridor."""
    print("SELF-CHECK: the 18 known closures", flush=True)
    ok_all = True
    for code, (name, truth) in KNOWN.items():
        row = classify(code)
        pmatch = "OK" if row["probe_kind"] == truth else "PROBE-MISMATCH"
        vok = row["verdict"] == "ENGINE_READY"
        ok_all = ok_all and vok and (row["probe_kind"] == truth)
        print(f"  {name:11} {row['verdict']:22} side={row.get('sidedness'):16}"
              f" rec={str(row.get('record_side')):6} probe={row['probe_kind']}"
              f"/{truth} {pmatch} maxgap={row.get('max_gap')}"
              f" len={row.get('word_len_at_max')} fuel_ok={row.get('fuel_ok')}",
              flush=True)
    print("ALL 18 ENGINE_READY and probe-correct:", ok_all, flush=True)
    return ok_all


if __name__ == "__main__":
    if "--selfcheck" in sys.argv:
        selfcheck()
    else:
        main()

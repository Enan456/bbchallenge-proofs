#!/usr/bin/env python3
"""Coverage calibration harness for the raw-step Lean generator.

Measures the TRUE clean-closure hit-rate of qgkit/bb6/rawstep_generator.py
over the *untouched* engine-ready holdouts.

The audit `experiments/outputs/audit_openset.jsonl` marks 795 holdouts
`verdict == "ENGINE_READY"`.  Only ~109 of those are actually closed
(the generated raw-step dossiers plus a handful of hand-built / named
machines).  This harness takes a deterministic, reproducible sample of the
UNTOUCHED engine-ready machines and, for each one, actually runs the
generator end-to-end and then runs the generator's own in-memory
differential gate (the 20-million-step exact fail-closed record-mirror
check, identical surgery to the emitted `dossier{N}_mirror.py`), recording:

    PASS  -- generator emitted all seven artifacts AND the differential gate
             passed cleanly (no halt, no orbit death, no fuel exhaustion,
             exact record agreement) over the full horizon.  A clean-closure
             *candidate* -- the Lean kernel is what ultimately certifies; this
             is the mechanical gate the generator itself relies on.
    SKIP  -- the generator declined (raised): split-door / exotic corridor
             (NotImplementedError) or a probe-structure mismatch.
    FAIL  -- a gate tripped.  Sub-classified; a HALT is flagged loudly.

Nothing here is a proof.  Every number is a MEASUREMENT of the generator's
mechanical behaviour on a sample, extrapolated with an explicit caveat.

Usage:
    python3 qgkit/bb6/coverage_calibration.py [--horizon N] [--stride K]
        [--timeout S] [--out results.jsonl] [--limit M]

Writes one JSON object per sampled machine to --out (default under the
scratchpad) and prints a summary table.  Commits nothing; writes emitted
Lean/py artifacts only into a scratch dir, never into packages/ or
busy-beaver-core/.
"""
import os
import sys
import json
import time
import signal
import argparse
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import rawstep_generator as G  # noqa: E402

AUDIT = os.path.join(REPO, "experiments", "outputs", "audit_openset.jsonl")


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def load_engine_ready():
    rows = []
    with open(AUDIT, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if r.get("verdict") == "ENGINE_READY":
                rows.append(r)
    return rows


def load_closed_codes(path):
    if not path or not os.path.exists(path):
        return set()
    return set(l.strip() for l in open(path) if l.strip())


def classify_failure(msg):
    """Map an AssertionError message from run_differential to a verdict."""
    m = (msg or "").lower()
    if "probe unsafe" in m or "raw halt" in m:
        return "FAIL_HALT"          # the machine HALTS -> loud flag
    if "orbit died" in m:
        return "FAIL_ORBIT"         # fail-closed: fuel exhaustion / orbit death
    if "mismatch" in m:
        return "FAIL_MISMATCH"      # word/state/step disagreement
    # bare `assert max_frac < 1.0` -> empty message
    return "FAIL_FUEL"              # quadratic fuel fraction hit 1.0


def run_one(row, N, horizon, timeout, scratch):
    """Run generator + differential gate on one machine.  Returns a dict."""
    code = row["code"]
    rec_side = row.get("record_side")
    orient = "R" if rec_side == "right" else "L"
    res = {"code": code, "record_side": rec_side, "orient": orient,
           "N": N, "verdict": None, "reason": None, "halt": False,
           "n_records": None, "max_frac": None, "seconds": None,
           "probe": None, "variant": None, "doors": None}
    t0 = time.time()

    # --- 1. build Spec (validates the halt/probe structure) --------------
    try:
        sp = G.Spec(code, orient, N)
    except ValueError as e:
        res["verdict"] = "SKIP_PROBE"
        res["reason"] = f"Spec rejected: {e}"
        res["seconds"] = round(time.time() - t0, 2)
        return res
    except Exception as e:  # noqa: BLE001
        res["verdict"] = "ERROR"
        res["reason"] = f"Spec error: {type(e).__name__}: {e}"
        res["seconds"] = round(time.time() - t0, 2)
        return res

    res["probe"] = f"{sp.P}{sp.probe_read}"
    res["variant"] = sp.variant
    res["doors"] = [f"{s}{b}->{'push' if d == sp.push_dir else 'pop'}({d})"
                    for (s, b, w, d) in sp.doors]

    # --- 2. run the generator: emit all seven artifacts to scratch -------
    dirs = {k: os.path.join(scratch, "artifacts", str(N), k)
            for k in ("core", "qgkit", "tests", "palomar", "comparator", "meta")}
    try:
        G.emit_all(sp, dirs)
    except NotImplementedError as e:
        res["verdict"] = "SKIP_SPLITDOOR"
        res["reason"] = f"corridor NotImplementedError: {str(e)[:160]}"
        res["seconds"] = round(time.time() - t0, 2)
        return res
    except Exception as e:  # noqa: BLE001
        res["verdict"] = "ERROR"
        res["reason"] = f"emit error: {type(e).__name__}: {str(e)[:160]}"
        res["seconds"] = round(time.time() - t0, 2)
        return res

    # --- 3. differential gate: 20M-step exact fail-closed check ----------
    old = signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(int(timeout))
    try:
        n_rec, max_frac = G.run_differential(sp, horizon)
        res["verdict"] = "PASS"
        res["n_records"] = n_rec
        res["max_frac"] = round(max_frac, 8)
    except Timeout:
        # differential ran clean up to the wall-clock cap without tripping any
        # gate; not a full-horizon PASS, honestly separated.
        res["verdict"] = "PASS_TIMEOUT"
        res["reason"] = f"no failure within {timeout}s wall-clock (partial horizon)"
    except AssertionError as e:
        v = classify_failure(str(e))
        res["verdict"] = v
        res["reason"] = str(e)[:200]
        res["halt"] = (v == "FAIL_HALT")
    except Exception as e:  # noqa: BLE001
        res["verdict"] = "ERROR"
        res["reason"] = f"{type(e).__name__}: {str(e)[:160]}\n{traceback.format_exc()[-400:]}"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)

    res["seconds"] = round(time.time() - t0, 2)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--horizon", type=int, default=20_000_000)
    ap.add_argument("--stride", type=int, default=15)
    ap.add_argument("--timeout", type=int, default=120,
                    help="per-machine wall-clock cap for the differential (s)")
    ap.add_argument("--limit", type=int, default=0,
                    help="cap number of sampled machines (0 = no cap)")
    ap.add_argument("--closed", default=os.path.join(
        os.environ.get("SCRATCH", "/tmp"), "closed_codes.txt"),
        help="file of already-closed TM codes to exclude (one per line)")
    ap.add_argument("--scratch", default=os.environ.get("SCRATCH", "/tmp"))
    ap.add_argument("--out", default=None)
    a = ap.parse_args()

    out = a.out or os.path.join(a.scratch, "calibration_results.jsonl")
    er = load_engine_ready()
    closed = load_closed_codes(a.closed)
    untouched = [r for r in er if r["code"] not in closed]

    # deterministic, reproducible sample: every `stride`-th untouched row
    # (file order is fixed), starting at index 0.
    sample = untouched[::a.stride]
    if a.limit:
        sample = sample[:a.limit]

    print(f"engine-ready total      : {len(er)}")
    print(f"closed codes excluded   : {len(closed)} (best-effort)")
    print(f"untouched engine-ready  : {len(untouched)}")
    print(f"sample (every {a.stride}th)     : {len(sample)}")
    print(f"horizon                 : {a.horizon:,} raw steps")
    print(f"per-machine timeout     : {a.timeout}s")
    print(f"writing results to      : {out}")
    print("-" * 72)

    results = []
    with open(out, "w", encoding="utf-8") as fout:
        for i, row in enumerate(sample):
            # untouched index -> stable N tag for scratch artifacts
            N = 90000 + i
            res = run_one(row, N, a.horizon, a.timeout, a.scratch)
            results.append(res)
            fout.write(json.dumps(res) + "\n")
            fout.flush()
            flag = "  <-- HALT!!!" if res["halt"] else ""
            print(f"[{i+1:>3}/{len(sample)}] {res['verdict']:<14} "
                  f"{res['code']}  ({res['seconds']}s, "
                  f"nrec={res['n_records']}){flag}")
            if res["reason"] and res["verdict"] not in ("PASS",):
                print(f"          reason: {res['reason'][:120]}")

    # -------- summary --------
    from collections import Counter
    c = Counter(r["verdict"] for r in results)
    halts = [r for r in results if r["halt"]]
    n = len(results)
    npass = c.get("PASS", 0)
    npass_to = c.get("PASS_TIMEOUT", 0)
    print("=" * 72)
    print("VERDICT BREAKDOWN")
    for k, v in c.most_common():
        print(f"  {k:<16} {v:>4}  ({100*v/n:.1f}%)")
    print("-" * 72)
    print(f"clean PASS (full horizon) : {npass}/{n} = {100*npass/n:.1f}%")
    if npass_to:
        print(f"PASS_TIMEOUT (partial)    : {npass_to}")
    if halts:
        print("!!!! HALTS DETECTED !!!!")
        for r in halts:
            print(f"   {r['code']}  {r['reason']}")
    else:
        print("halts detected            : NONE")
    print("=" * 72)
    print(json.dumps({"n": n, "breakdown": dict(c),
                      "pass": npass, "pass_timeout": npass_to,
                      "halts": len(halts)}))


if __name__ == "__main__":
    main()

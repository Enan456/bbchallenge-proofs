"""Stage 755 -- does the fitted macro system survive a 10x longer raw run?

Stage751's PASS gate compared the fitted rules against whatever records fell
beyond the fit horizon.  For slow-record machines that is only a handful of
transitions, so a PASS there is nearly vacuous and any downstream
extrapolation (stage754's abstract orbit) is unverified.

This script re-runs the raw machine far past the original budget and replays
every record transition against the rules fitted on the short run, reporting
the first mismatch.  A machine whose rules break here never had an exact
macro system; one that survives has a much stronger claim to it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from bisect import bisect_right
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import simulate_records
from qgkit.bb6.vcollatz import macro

OUT = HERE / "outputs" / "stage755"
FIT_STEPS, FIT_CAP = 20_000_000, 20_000
STARTUP_PREFIX = 8


def check(code: str, long_steps: int, cap: int) -> dict:
    halted, _s, fit_records = simulate_records(code, steps=FIT_STEPS, cap=FIT_CAP)
    if halted or len(fit_records) < STARTUP_PREFIX + 4:
        return {"code": code, "status": "NO_FIT"}
    rules = macro.fit_macro_rules(fit_records, startup_prefix=STARTUP_PREFIX)

    halted_long, stop, records = simulate_records(code, steps=long_steps, cap=cap)
    n_fit = len(fit_records)
    n_mismatch = n_uncovered = n_checked = 0
    first = None
    for i in range(max(n_fit - 1, STARTUP_PREFIX), len(records) - 1):
        pred = macro.predict_next(macro.astate(records[i]), rules)
        actual = macro.astate(records[i + 1])
        n_checked += 1
        if pred != actual:
            n_mismatch += 1
            if pred is None:
                n_uncovered += 1
            if first is None:
                first = {"record_index": i, "step": records[i]["step"],
                         "from": repr(macro.astate(records[i])),
                         "predicted": repr(pred), "actual": repr(actual)}
    return {
        "code": code,
        "status": ("HALTED" if halted_long else
                   "EXACT_EXTENDED" if n_mismatch == 0 else "RULES_BREAK"),
        "long_steps": long_steps, "steps_executed": stop,
        "n_records_fit_run": n_fit, "n_records_long_run": len(records),
        "n_transitions_checked": n_checked,
        "n_mismatches": n_mismatch, "n_uncovered": n_uncovered,
        "first_mismatch": first,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--code", required=True)
    parser.add_argument("--steps", type=int, default=1_000_000_000)
    parser.add_argument("--cap", type=int, default=200_000)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    row = check(args.code, args.steps, args.cap)
    path = OUT / f"{hashlib.sha1(args.code.encode()).hexdigest()[:12]}.json"
    path.write_text(json.dumps(row, indent=2, sort_keys=True) + "\n")
    print(json.dumps(row, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

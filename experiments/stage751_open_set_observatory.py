"""Bounded dossier and exact macro-replay observatory for the BB(6) open set.

``PASS_EXACT_MACRO_SYSTEM`` is an exact statement about the finite frontier
records collected here.  It is not a proof about the underlying machine.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import (
    abstraction_class,
    compact_growth_features,
    simulate_records,
)
from qgkit.bb6.vcollatz.macro import fit_macro_rules, replay_records

ROOT = Path(__file__).resolve().parent
DEFAULT_INPUT = ROOT / "outputs" / "BB6_open_1158_2026-07-29.txt"
OUT_DIR = ROOT / "outputs" / "stage751"
MACHINE_DIR = OUT_DIR / "machines"
FIT_STEPS, FIT_CAP = 20_000_000, 20_000
VERIFY_STEPS, VERIFY_CAP = 100_000_000, 100_000
# Parent-side grace period.  A worker is one task only; a timed-out result is
# recorded and never used, even though ProcessPoolExecutor cannot kill it.
TASK_TIMEOUT_SECONDS = 900
# Minimum out-of-sample record transitions for a PASS to mean anything.
MIN_OOS = 50
SCOPE = "bounded exact fitting+replay; PASS is an exact statement about observed records, not a proof"


def result_path(code: str) -> Path:
    return MACHINE_DIR / f"{hashlib.sha1(code.encode()).hexdigest()[:12]}.json"


def _base(code: str, verdict: str, *, error: str | None = None) -> dict:
    return {
        "code": code, "verdict": verdict, "n_conflicts": None,
        "in_sample": None, "out_of_sample": None,
        "n_group_rules": 0, "n_literal_rules": 0,
        "collapse_values": [], "n_collapses": 0, "features": None,
        "dims_hist": {}, "halted": False, "error": error, "scope": SCOPE,
        "fit_steps": FIT_STEPS, "verify_steps": VERIFY_STEPS,
    }


def observe_machine(code: str, fit_steps: int = FIT_STEPS,
                    verify_steps: int = VERIFY_STEPS) -> dict:
    """Worker entry point; all simulation and fitting for one machine.

    Budgets are explicit arguments because macOS spawn-mode workers reimport
    the module and would not see CLI-mutated globals.
    """
    global FIT_STEPS, VERIFY_STEPS
    FIT_STEPS = fit_steps
    VERIFY_STEPS = verify_steps
    try:
        halted, _stop, fit_records = simulate_records(code, steps=FIT_STEPS, cap=FIT_CAP)
        if halted:
            row = _base(code, "HALTED")
            row["halted"] = True
            row["dims_hist"] = dict(Counter(map(lambda r: len(r["blocks"]), fit_records)))
            return row

        fit_max_dim = max((len(r["blocks"]) for r in fit_records), default=0)
        high_dim = fit_max_dim > 12
        rules = None if high_dim else fit_macro_rules(fit_records)
        in_sample = None if rules is None else replay_records(fit_records, 8, rules)

        # One long run supplies both OOS replay and every dossier statistic.
        halted_long, _stop_long, records = simulate_records(
            code, steps=VERIFY_STEPS, cap=VERIFY_CAP)
        dims = [len(r["blocks"]) for r in records]
        collapse_values = [r["blocks"][0] for r in records if len(r["blocks"]) == 1]
        row = _base(code, "NOT_FITTABLE_HIGH_DIM" if high_dim else "PARTIAL")
        row.update({
            "halted": halted_long,
            "collapse_values": collapse_values[:40],
            "n_collapses": len(collapse_values),
            "features": compact_growth_features(records[:2000]),
            "dims_hist": dict(sorted(Counter(dims).items())),
            "dossier_class": abstraction_class(dims),
            "max_dim": max(dims, default=0),
        })
        if rules is not None:
            out_sample = replay_records(records, len(fit_records), rules)
            row.update({
                "n_conflicts": rules["n_conflicts"],
                "in_sample": in_sample,
                "out_of_sample": out_sample,
                "n_group_rules": len(rules["group_rules"]),
                "n_literal_rules": len(rules["literal_rules"]),
            })
            # A PASS needs real out-of-sample evidence.  Slow-record
            # machines can otherwise "pass" on a handful of transitions,
            # which stage755 showed to be vacuous: two such machines'
            # rules break catastrophically at ~2e8 steps.
            row["validation_strength"] = out_sample["n_transitions_checked"]
            if (rules["n_conflicts"] == 0 and in_sample["exact"]
                    and out_sample["exact"]):
                row["verdict"] = ("PASS_EXACT_MACRO_SYSTEM"
                                  if out_sample["n_transitions_checked"] >= MIN_OOS
                                  else "PASS_WEAK_VALIDATION")
        return row
    except Exception as exc:  # persisted so a resume does not silently retry forever
        return _base(code, "ERROR", error=repr(exc))


def _load_codes(path: Path, limit: int | None) -> list[str]:
    codes = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    return codes if limit is None else codes[:limit]


def _write_result(row: dict) -> None:
    path = result_path(row["code"])
    path.write_text(json.dumps(row, indent=2, sort_keys=True) + "\n")


def _timeout_row(code: str) -> dict:
    return _base(code, "TIMEOUT", error=f"future exceeded {TASK_TIMEOUT_SECONDS}s parent budget")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument("--fit-steps", type=int, default=FIT_STEPS)
    parser.add_argument("--verify-steps", type=int, default=VERIFY_STEPS)
    args = parser.parse_args()
    if not args.input.exists():
        raise FileNotFoundError(f"open-set input does not exist: {args.input}")
    if args.workers < 1:
        raise ValueError("--workers must be at least 1")

    MACHINE_DIR.mkdir(parents=True, exist_ok=True)
    codes = _load_codes(args.input, args.limit)
    pending = [code for code in codes if not result_path(code).exists()]
    if pending:
        # Submission timestamps let the parent record overdue tasks while
        # retaining normal completed-future progress reporting.
        try:
            executor = concurrent.futures.ProcessPoolExecutor(max_workers=args.workers)
        except (OSError, PermissionError):
            # Some restricted runners prohibit POSIX semaphores.  Preserve a
            # usable smoke/resume path there; normal execution uses processes.
            executor = concurrent.futures.ThreadPoolExecutor(max_workers=args.workers)
        with executor as pool:
            # Bounded in-flight submission: at most `workers` futures are
            # outstanding, so a future's submission time approximates its
            # start time and the per-task timeout is measured from start,
            # not from enqueueing (the mass-timeout bug of the first run).
            import time as _time
            queue = list(pending)
            futures: dict = {}
            with tqdm(total=len(pending), desc="stage751 machines") as bar:
                while queue or futures:
                    while queue and len(futures) < args.workers:
                        code = queue.pop(0)
                        futures[pool.submit(observe_machine, code,
                                            args.fit_steps,
                                            args.verify_steps)] = (
                            code, _time.monotonic())
                    done, _ = concurrent.futures.wait(
                        futures, timeout=1, return_when=concurrent.futures.FIRST_COMPLETED)
                    for future in done:
                        code, _submitted = futures.pop(future)
                        try:
                            row = future.result(timeout=0)
                        except Exception as exc:
                            row = _base(code, "ERROR", error=repr(exc))
                        _write_result(row)
                        bar.update(1)
                    now = _time.monotonic()
                    overdue = [future for future, (_code, submitted) in futures.items()
                               if now - submitted > TASK_TIMEOUT_SECONDS]
                    for future in overdue:
                        code, _submitted = futures.pop(future)
                        _write_result(_timeout_row(code))
                        future.cancel()
                        bar.update(1)

    rows = [json.loads(result_path(code).read_text()) for code in codes if result_path(code).exists()]
    verdicts = Counter(row["verdict"] for row in rows)
    dossier_classes = Counter(row.get("dossier_class", "NO_DOSSIER") for row in rows)
    summary = {
        "input": str(args.input), "n_requested": len(codes), "n_results": len(rows),
        "counts_by_verdict": dict(sorted(verdicts.items())),
        "counts_by_dossier_class": dict(sorted(dossier_classes.items())),
        "pass_codes": [row["code"] for row in rows if row["verdict"] == "PASS_EXACT_MACRO_SYSTEM"],
        "timeout_error_codes": [row["code"] for row in rows
                                if row["verdict"] in {"TIMEOUT", "ERROR"}],
        "scope": SCOPE,
    }
    (OUT_DIR / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

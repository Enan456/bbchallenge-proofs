"""Stage 754 -- arithmetic triage of the abstract orbits of the PASS machines.

For each machine with an exact macro system, the closure argument reduces
non-halting to one statement about the *abstract* orbit: it never leaves the
fitted rule domain (never abstains).  This script asks, per machine, whether
that statement looks **provable by a finite certificate** or **orbit
dependent** (Collatz-class):

* run the abstract orbit forward (pure arithmetic on block tuples);
* record the fired rule label at each abstract step;
* test the label sequence for eventual periodicity — a period means the
  safety condition follows from a finite cycle, i.e. the machine could be
  decided outright rather than conditionally;
* report growth rate, the small-value (< 5) components that ever appear,
  and where the orbit abstains, if it does.

Verdicts are heuristics about proof difficulty, never claims about halting.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from tqdm import tqdm

from qgkit.bb6.vcollatz.classify import simulate_records
from qgkit.bb6.vcollatz import macro

OUT = HERE / "outputs" / "stage754"
FIT_STEPS, FIT_CAP = 20_000_000, 20_000
STARTUP_PREFIX = 8


def label_of(state: tuple, rules: dict) -> str | None:
    """The exact rule the macro table selects, or None when it abstains."""
    pred = macro.predict_next(state, rules)
    if pred is None:
        return None
    if state in rules["literal_rules"]:
        return "LITERAL"
    for parity in (True, False):
        key = macro.group_key(state, parity=parity)
        if key in rules["group_rules"]:
            return repr(key)
    return None


def eventual_period(seq: list[str], max_period: int = 4096) -> dict | None:
    """Smallest (start, period) making `seq` eventually periodic, if any.

    Only a period that is confirmed over the whole tail is accepted, so a
    coincidental short repeat cannot masquerade as a cycle.
    """
    n = len(seq)
    if n < 32:
        return None
    for period in range(1, min(max_period, n // 4) + 1):
        # The tail must be exactly periodic; scan back for the earliest start.
        start = n - 1
        while start - period >= 0 and seq[start] == seq[start - period]:
            start -= 1
        first = start + 1
        if n - first >= max(8 * period, n // 2):
            return {"period": period, "first_index": first - period + 1,
                    "confirmed_tail": n - first}
    return None


def analyse(code: str, abstract_steps: int) -> dict:
    halted, _stop, records = simulate_records(code, steps=FIT_STEPS, cap=FIT_CAP)
    if halted or len(records) < STARTUP_PREFIX + 4:
        return {"code": code, "status": "NO_FIT",
                "halted": halted, "n_records": len(records)}
    rules = macro.fit_macro_rules(records, startup_prefix=STARTUP_PREFIX)
    if rules["n_conflicts"]:
        return {"code": code, "status": "CONFLICTS",
                "n_conflicts": rules["n_conflicts"]}

    state = macro.astate(records[STARTUP_PREFIX])
    labels: list[str] = []
    dims: list[int] = []
    small_components: dict[str, int] = {}
    ones_trace: list[int] = []
    abstain_at = None
    for step in tqdm(range(abstract_steps), desc=f"orbit {code[:14]}",
                     mininterval=5.0):
        lab = label_of(state, rules)
        if lab is None:
            abstain_at = step
            break
        labels.append(lab)
        blocks = state[2]
        dims.append(len(blocks))
        for i, v in enumerate(blocks):
            if v < 5:
                key = f"dim{len(blocks)}[{i}]={v}"
                small_components[key] = small_components.get(key, 0) + 1
        if step % 64 == 0:
            ones_trace.append(sum(blocks))
        state = macro.predict_next(state, rules)

    period = eventual_period(labels)
    n = len(labels)
    growth = None
    if len(ones_trace) >= 8:
        a, b = ones_trace[len(ones_trace) // 2], ones_trace[-1]
        growth = {"ones_mid": a, "ones_end": b,
                  "ratio": (b / a) if a else None}

    if abstain_at is not None:
        status = "ABSTAINS"
    elif period is not None:
        status = "PERIODIC_CERTIFICATE"
    else:
        status = "ORBIT_DEPENDENT"

    return {
        "code": code,
        "status": status,
        "n_abstract_steps": n,
        "abstain_at": abstain_at,
        "abstract_state_at_abstain": repr(state) if abstain_at is not None else None,
        "period": period,
        "n_distinct_rules_fired": len(set(labels)),
        "n_rules_in_table": len(rules["group_rules"]) + len(rules["literal_rules"]),
        "dim_range": [min(dims), max(dims)] if dims else None,
        "small_component_hits": dict(sorted(small_components.items(),
                                            key=lambda kv: -kv[1])[:12]),
        "growth": growth,
        "honest_scope": ("heuristic triage of proof difficulty for the "
                         "abstract-orbit safety condition; not a halting claim"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path,
                        default=HERE / "outputs" / "stage753_queue.txt")
    parser.add_argument("--abstract-steps", type=int, default=200_000)
    args = parser.parse_args()
    codes = [line.strip() for line in args.input.read_text().splitlines()
             if line.strip()]
    OUT.mkdir(parents=True, exist_ok=True)
    rows = []
    for code in codes:
        path = OUT / f"{hashlib.sha1(code.encode()).hexdigest()[:12]}.json"
        if path.exists():
            rows.append(json.loads(path.read_text()))
            print(f"skip existing {code}")
            continue
        row = analyse(code, args.abstract_steps)
        path.write_text(json.dumps(row, indent=2, sort_keys=True) + "\n")
        rows.append(row)
        print(f"{code}: {row['status']} steps={row.get('n_abstract_steps')} "
              f"period={row.get('period')}")
    summary = {"n": len(rows),
               "by_status": {s: [r["code"] for r in rows if r["status"] == s]
                             for s in sorted({r["status"] for r in rows})}}
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2,
                                                 sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

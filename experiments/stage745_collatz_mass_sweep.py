"""Stage 745 -- Collatz-lens mass classification of all BB(6) holdouts.

Runs characterize_holdout over every machine in BB6_holdouts_1094.txt and
writes a per-machine JSONL plus an aggregate summary and markdown table.
Resumable: codes already present in rows.jsonl are skipped, so the sweep can
be interrupted and relaunched.

Only decider-chain rows are certainties; all other labels are bounded
empirical structure and prove nothing.

Run:
    python3 experiments/stage745_collatz_mass_sweep.py [--profile fast|deep]
        [--limit N] [--input PATH]
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from collections import Counter
from pathlib import Path

from tqdm import tqdm

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from qgkit.bb6.vcollatz.classify import characterize_holdout

OUT = Path(__file__).resolve().parent / "outputs" / "stage745"
DEFAULT_INPUT = Path(__file__).resolve().parent / "outputs" / "BB6_holdouts_1094.txt"

PROFILES = {
    # Holdouts already survived huge decider budgets; "fast" keeps the chain
    # cheap and spends time on structure instead.
    "fast": dict(decider_budget=20_000, backward_depth=200, ctl_radius=4,
                 far_dfa_states=6, sim_steps=700_000, extract_steps=1_000_000),
    "deep": dict(decider_budget=200_000, backward_depth=800, ctl_radius=7,
                 far_dfa_states=10, sim_steps=2_000_000, extract_steps=3_000_000),
}


def load_done(path: Path) -> set[str]:
    done: set[str] = set()
    if path.exists():
        for line in path.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                done.add(json.loads(line)["code"])
            except (json.JSONDecodeError, KeyError):
                continue
    return done


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--profile", choices=sorted(PROFILES), default="fast")
    ap.add_argument("--limit", type=int, default=0, help="stop after N new rows (0 = all)")
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    rows_path = OUT / "rows.jsonl"
    codes = [ln.strip() for ln in args.input.read_text().splitlines() if ln.strip()]
    done = load_done(rows_path)
    todo = [c for c in codes if c not in done]
    if args.limit:
        todo = todo[: args.limit]

    kwargs = PROFILES[args.profile]
    with rows_path.open("a") as fh:
        for code in tqdm(todo, desc=f"stage745 sweep ({args.profile})"):
            try:
                row = characterize_holdout(code, **kwargs)
            except Exception as exc:  # keep the sweep alive; record the crash
                row = {"code": code, "label": "ERROR", "decided": False,
                       "error": repr(exc)}
            fh.write(json.dumps(row, sort_keys=True) + "\n")
            fh.flush()

    all_rows = [json.loads(ln) for ln in rows_path.read_text().splitlines() if ln.strip()]
    label_counts = Counter(r["label"] for r in all_rows)
    scored = [r for r in all_rows
              if r.get("features") and not r["decided"] and r.get("novel")]
    scored.sort(key=lambda r: r["features"]["score"], reverse=True)
    summary = {
        "profile": args.profile,
        "n_input": len(codes),
        "n_classified": len(all_rows),
        "label_counts": dict(label_counts),
        "n_novel_scored": len(scored),
        "top_novel": [
            {"code": r["code"], "label": r["label"],
             "score": r["features"]["score"], "dmax": r["features"]["dmax"],
             "dominant_delta": r["features"]["dominant_delta"],
             "dominant_delta_frac": r["features"]["dominant_delta_frac"]}
            for r in scored[:25]
        ],
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")

    lines = ["# Stage 745 -- Collatz-lens mass classification", "",
             f"Input machines: {len(codes)}  |  classified: {len(all_rows)}", "",
             "| label | count |", "|---|---|"]
    for label, count in label_counts.most_common():
        lines.append(f"| {label} | {count} |")
    lines += ["", "## Top novel compact-growth candidates", "",
              "| score | dmax | dominant delta | frac | code |", "|---|---|---|---|---|"]
    for r in summary["top_novel"]:
        lines.append(f"| {r['score']} | {r['dmax']} | {r['dominant_delta']} "
                     f"| {r['dominant_delta_frac']} | `{r['code']}` |")
    (OUT / "classification.md").write_text("\n".join(lines) + "\n")

    print(json.dumps({k: v for k, v in summary.items() if k != "top_novel"}, indent=2))
    print(f"wrote {OUT / 'summary.json'}")


if __name__ == "__main__":
    main()

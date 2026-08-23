#!/usr/bin/env python3
"""stage757: OrbitFinder sweep over the stage753 obligation-queue machines.

For each machine, attempt a fail-closed exact orbit spec (affine record
rules + exact step costs, qgkit.bb6.dragon.finder). EXACT means every
observed frontier-record transition replays with zero error — the
prerequisite for an OrbitPredictor and, downstream, a flying-dragon
localization proof. Bounded empirical structure; nothing here is a proof.

Run from repo root: python experiments/stage757_orbit_finder_sweep.py
"""
from __future__ import annotations

import json
import pathlib
import sys

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from qgkit.bb6.dragon.finder import OrbitFinder  # noqa: E402

OUT = REPO / "experiments" / "outputs" / "stage757"
OUT.mkdir(parents=True, exist_ok=True)

rows = []
codes = [l.strip() for l in
         (REPO / "experiments/outputs/stage753_queue.txt").open()
         if l.strip()]
for code in codes:
    f = OrbitFinder(code, steps=150_000)
    spec = f.fit()
    row = {"code": code, "n_transitions": len(f.pairs),
           "verdict": "EXACT" if spec else "REJECTED"}
    if spec:
        row["n_rules"] = spec["n_rules"]
        row["top_support"] = max(r["support"] for r in spec["rules"].values())
        row["rules"] = {str(k): {"maps": [[str(x) for x in m]
                                          for m in r["maps"]],
                                 "cost": [str(x) for x in r["cost"]],
                                 "support": r["support"]}
                        for k, r in spec["rules"].items()}
    rows.append(row)
    print(row["verdict"], code, row["n_transitions"])

(OUT / "specs.json").write_text(json.dumps(rows, indent=2))
n_exact = sum(1 for r in rows if r["verdict"] == "EXACT")
(OUT / "summary.md").write_text(
    "# stage757 — orbit-finder sweep (stage753 queue)\n\n"
    f"{n_exact}/{len(rows)} machines admit a fail-closed exact orbit spec "
    "at 150k-step budget.\nEXACT machines are OrbitPredictor-ready and "
    "candidates for flying-dragon\nlocalization proofs; REJECTED means no "
    "exact affine record spec at this\nbudget/signature (not a negative "
    "result about the machine).\n\n"
    + "\n".join(f"- {r['verdict']:8s} `{r['code']}` "
                f"trans={r['n_transitions']}"
                + (f" rules={r['n_rules']} top={r['top_support']}"
                   if r["verdict"] == "EXACT" else "")
                for r in rows)
    + "\n\nHonest scope: bounded empirical structure over observed "
    "records; only the Lean layer turns specs into theorems.\n")
print(f"wrote {OUT}/specs.json and summary.md ({n_exact}/{len(rows)} exact)")

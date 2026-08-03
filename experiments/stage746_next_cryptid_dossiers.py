"""Stage 746 -- Deep dossiers for the top novel cryptid candidates.

For each top-scoring novel machine from the stage745 sweep, run a long
focused simulation collecting one-block checkpoint values (the tape moments
where exactly one 1-run exists), measure the dominant two-block transfer
rule at frontier records, and attempt a high-budget exact vector-map
projection. Bounded evidence only; nothing here decides any machine.

Run:
    python3 experiments/stage746_next_cryptid_dossiers.py [--top K]
        [--steps N] [--checkpoint-cap M]
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
from pathlib import Path

from tqdm import tqdm

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from qgkit.bb6.vcollatz.classify import (
    DVISETU_CODE, KNOWN_WIKI_CRYPTIDS, _parse, compact_growth_features,
    simulate_records,
)
from qgkit.bb6.vcollatz.extract import extract_vector_map

OUT = Path(__file__).resolve().parent / "outputs" / "stage746"
SUMMARY_745 = Path(__file__).resolve().parent / "outputs" / "stage745" / "summary.json"


def focused_run(code: str, steps: int, checkpoint_cap: int = 4_000):
    """Long raw run: halt check + one-block checkpoint series.

    A checkpoint is recorded whenever the tape holds exactly one 1-run;
    consecutive duplicates are collapsed. tqdm-wrapped because this is the
    long loop (up to hundreds of millions of steps).
    """
    tab = _parse(code)
    tape: dict[int, int] = {}
    head = 0
    state = 0
    lo = hi = 0
    checkpoints: list[int] = []
    ones = 0
    run_breaks = 0  # number of 0-gaps inside [min_one, max_one]
    min_one = None
    max_one = None

    def snapshot_one_block() -> int | None:
        cells = (tape.get(p, 0) for p in range(lo, hi + 1))
        runs = [sum(1 for _ in g) for b, g in itertools.groupby(cells) if b == 1]
        return runs[0] if len(runs) == 1 else None

    check_every = 64
    for step in tqdm(range(steps), desc=f"focused {code[:12]}", mininterval=5.0):
        sym = tape.get(head, 0)
        tr = tab.get((state, sym))
        if tr is None:
            return {"halted": True, "halt_step": step, "checkpoints": checkpoints}
        ns, nw, direction = tr
        if nw:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = ns
        head += direction
        lo = min(lo, head)
        hi = max(hi, head)
        if step % check_every == 0 and len(checkpoints) < checkpoint_cap:
            value = snapshot_one_block()
            if value is not None and (not checkpoints or checkpoints[-1] != value):
                checkpoints.append(value)
    return {"halted": False, "halt_step": None, "checkpoints": checkpoints}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=8)
    ap.add_argument("--steps", type=int, default=50_000_000)
    ap.add_argument("--checkpoint-cap", type=int, default=4_000)
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    summary = json.loads(SUMMARY_745.read_text())
    candidates = [r for r in summary["top_novel"]
                  if r["code"] not in KNOWN_WIKI_CRYPTIDS
                  and r["code"] != DVISETU_CODE][: args.top]

    md = ["# Stage 746 -- next-cryptid candidate dossiers", ""]
    for idx, cand in enumerate(candidates):
        code = cand["code"]
        run = focused_run(code, steps=args.steps,
                          checkpoint_cap=args.checkpoint_cap)
        _h, _s, records = simulate_records(code, steps=3_000_000, cap=600)
        features = compact_growth_features(records)
        try:
            vgc = extract_vector_map(code, max_steps=3_000_000, max_dim=6)
        except Exception:
            vgc = None
        dossier = {
            "code": code,
            "stage745_score": cand["score"],
            "halted_in_focused_run": run["halted"],
            "halt_step": run["halt_step"],
            "focused_steps": args.steps,
            "one_block_checkpoints_head": run["checkpoints"][:80],
            "n_checkpoints": len(run["checkpoints"]),
            "features_3m": features,
            "vmap": None if vgc is None else {
                "d": int(vgc.d), "mod_vec": list(vgc.mod_vec),
                "n_branches": len(vgc.branches), "halt_faithful": False,
            },
        }
        path = OUT / f"dossier_{idx:02d}.json"
        path.write_text(json.dumps(dossier, indent=2, sort_keys=True) + "\n")
        md += [f"## {idx}: `{code}`", "",
               f"- stage745 score: {cand['score']}",
               f"- focused run: {'HALTED at ' + str(run['halt_step']) if run['halted'] else f'no halt in {args.steps:,} steps'}",
               f"- one-block checkpoints observed: {len(run['checkpoints'])}",
               f"- checkpoint head: {run['checkpoints'][:24]}",
               f"- dominant delta (3M-step records): {features['dominant_delta'] if features else None} "
               f"@ {features['dominant_delta_frac'] if features else None}",
               f"- exact projection map: {dossier['vmap']}", ""]
    (OUT / "dossiers.md").write_text("\n".join(md) + "\n")
    print(f"wrote {len(candidates)} dossiers to {OUT}")


if __name__ == "__main__":
    main()

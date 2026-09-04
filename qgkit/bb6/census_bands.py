"""Pinned census-band definitions (forward-plan phase 0.1).

Single source of truth for how the 1,094 BB(6) holdouts are bucketed.
Every downstream doc and harness must import from here rather than
re-deriving thresholds, which is what let the counts drift
(262 vs 289 single-law across two independent recounts).

Band definition (fixed 2026-09-03):
  structured   := laws == 1 and nreg >= 3   (single affine regime law)
  multi_law    := laws > 1
  unstructured := everything else

Run as a script to print the canonical counts.
"""
from __future__ import annotations
import json, pathlib

SWEEP = (pathlib.Path(__file__).resolve().parents[2]
         / "experiments" / "outputs" / "d4_fullsweep.jsonl")


def load_rows(path=SWEEP):
    return [json.loads(l) for l in open(path) if l.strip()]


def band(row) -> str:
    if row.get("laws", 0) > 1:
        return "multi_law"
    if row.get("laws", 0) == 1 and row.get("nreg", 0) >= 3:
        return "structured"
    return "unstructured"


def counts(rows=None):
    rows = rows if rows is not None else load_rows()
    out = {"structured": 0, "multi_law": 0, "unstructured": 0,
           "halts": 0, "total": len(rows)}
    for r in rows:
        out[band(r)] += 1
        if r.get("halted"):
            out["halts"] += 1
    return out


if __name__ == "__main__":
    c = counts()
    print("Pinned census bands (definition frozen 2026-09-03):")
    for k in ("total", "structured", "multi_law", "unstructured",
              "halts"):
        print(f"  {k:>13}: {c[k]}")

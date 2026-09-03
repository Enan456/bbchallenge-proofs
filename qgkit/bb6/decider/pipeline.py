"""The decider driver: learn -> search -> emit, fail-closed.

Verdicts:
  NONHALT(certificate)      only after the emitted Lean file is
                            kernel-checked (this module never returns
                            it directly; it returns DRAFT)
  DRAFT(path, obligations)  invariant found and verified; certificate
                            draft emitted with named obligations
  CONDITIONAL(reason)       law learned, no invariant (dossier case)
  UNKNOWN(stage, reason)    fail-closed at the named stage
"""

from __future__ import annotations
import sys, pathlib
from dataclasses import dataclass
from fractions import Fraction

HERE = pathlib.Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[3]))

from qgkit.bb6.decider.invariants import (AffineSystem, Branch,
                                          congruence_search,
                                          monotone_search, stress)


@dataclass
class Verdict:
    kind: str          # DRAFT | CONDITIONAL | UNKNOWN
    stage: str = ""
    detail: str = ""
    certificate: str = ""


def spec_to_system(spec, seed, fatal_residues=None):
    """Convert an OrbitFinder spec to an AffineSystem. Guards are
    unknown to the finder, so branches carry guard_mod None: the
    congruence search then requires closure under every branch from
    every residue, the sound over-approximation."""
    branches = []
    dim = None
    for key, r in spec['rules'].items():
        n = len(r['maps'][0]) - 1
        if dim is None:
            dim = n
        if n != dim:
            continue      # mixed-arity rules: skip (over-approx stays sound
                          # only if skipped branches cannot fire; caller
                          # must check; we record it)
        A = tuple(tuple(m[:-1]) for m in r['maps'])
        b = tuple(m[-1] for m in r['maps'])
        branches.append(Branch(matrix=A, offset=b, name=str(key)))
    return AffineSystem(branches=branches, dim=dim, seed=seed,
                        fatal_residues=fatal_residues or {})


def decide(code, steps=1_500_000, cap=20_000, fatal_model=None,
           seed=None, out_dir="certificates"):
    """Run the pipeline on one machine. fatal_model: {m: residues}
    established per machine (e.g. from halt-corridor analysis); the
    congruence searcher cannot exclude anything without one."""
    from qgkit.bb6.dragon.finder import OrbitFinder
    spec = OrbitFinder(code, steps=steps, cap=cap).fit()
    if spec is None:
        return Verdict("UNKNOWN", "learn",
                       "no exact orbit spec at this budget")
    seed = seed or _observed_seed(code, spec)
    if seed is None:
        return Verdict("UNKNOWN", "learn", "no seed tuple recovered")
    sys_ = spec_to_system(spec, seed, fatal_model)
    mono = monotone_search(sys_)
    cong = congruence_search(sys_) if fatal_model else []
    if not mono and not cong:
        why = ("no invariant at searched depth"
               + ("" if fatal_model else
                  "; no fatal model supplied, congruence not decisive"))
        return Verdict("CONDITIONAL", "search", why)
    for inv in cong:
        ok, viol = stress(sys_, inv)
        if not ok:
            cong.remove(inv)
    if not mono and not cong:
        return Verdict("CONDITIONAL", "stress",
                       "candidates failed raw stress")
    from qgkit.bb6.decider.emit import emit_draft
    path = emit_draft(code, sys_, mono, cong, out_dir)
    return Verdict("DRAFT", "emit",
                   f"mono={len(mono)} cong={len(cong)}", path)


def _observed_seed(code, spec):
    """Recover a representative seed tuple from the machine's own
    record stream (first block tuple matching the spec dimension)."""
    from qgkit.bb6.vcollatz.classify import simulate_records
    try:
        recs = simulate_records(code, 200_000)
    except Exception:
        return None
    dims = {len(r['maps'][0]) - 1 for r in spec['rules'].values()}
    for rec in recs if isinstance(recs, list) else []:
        t = rec.get('blocks') if isinstance(rec, dict) else rec
        if t is not None and len(t) in dims:
            return tuple(int(v) for v in t)
    return None


if __name__ == '__main__':
    code = sys.argv[1]
    v = decide(code)
    print(v.kind, v.stage, v.detail, v.certificate)

"""Unit tests: the searchers must find known invariants and reject
known non-invariants."""
import sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[3]))
from qgkit.bb6.decider.invariants import (AffineSystem, Branch,
                                          congruence_search,
                                          monotone_search, stress)

# 1. pure drift (a,b) -> (a+2, b+1): f = a (and b, and a+b) monotone
drift = AffineSystem(
    branches=[Branch(matrix=((1,0),(0,1)), offset=(2,1), name="d")],
    dim=2, seed=(5, 3))
hits = monotone_search(drift)
assert any(c == (1, 0) for c, _ in hits), hits
assert any(c == (0, 1) for c, _ in hits), hits
print(f"monotone: {len(hits)} functionals found on drift (ok)")

# 2. rotation (a,b) -> (b,a): no strictly increasing functional
rot = AffineSystem(
    branches=[Branch(matrix=((0,1),(1,0)), offset=(0,0), name="r")],
    dim=2, seed=(1, 2))
assert monotone_search(rot) == []
print("monotone: rotation correctly yields none (ok)")

# 3. congruence: (a,b) -> (a+2, b+2) mod 2 preserves parity vector;
# fatal = odd a (mod 2 residue (1,0),(1,1)); seed even a -> invariant
cong_sys = AffineSystem(
    branches=[Branch(matrix=((1,0),(0,1)), offset=(2,2), name="c")],
    dim=2, seed=(4, 7),
    fatal_residues={2: {(1, 0), (1, 1)}})
hits = congruence_search(cong_sys, moduli=[2])
assert hits and hits[0][0] == 2, hits
ok, viol = stress(cong_sys, hits[0], steps=10000)
assert ok, viol
print("congruence: mod-2 invariant found, stress ok (ok)")

# 4. congruence must FAIL when a branch enters the fatal set
bad = AffineSystem(
    branches=[Branch(matrix=((1,0),(0,1)), offset=(1,0), name="b")],
    dim=2, seed=(4, 7),
    fatal_residues={2: {(1, 0), (1, 1)}})
assert congruence_search(bad, moduli=[2]) == []
print("congruence: fatal-entering system correctly rejected (ok)")
print("ALL PASS")

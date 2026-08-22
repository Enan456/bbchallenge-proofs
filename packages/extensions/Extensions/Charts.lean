import Bridge.Incision

/-!
# Geometric charts for the incision atlas (plan 3, task 5 — skeleton)

Exact (rational / integer) coordinate charts for plotting abstract orbit
states.  This package is deliberately **separate** from `packages/bbchallenge`
and is never imported by it: the certified trust base does not depend on
anything here.  Currently core-only; if invariant-region proofs ever need
real hyperbolic geometry (`ℝ`, `ℍ²`), mathlib gets added *here*, not in the
certified packages.

Everything numeric-side (floating point, plots, metrics) lives in
`qgkit/bb6/geometry/`; these Lean definitions are the exact counterparts the
Python charts mirror, so that any future invariant-region statement has a
formal home.
-/

namespace QIG.Extensions

open QIG.AntihydraRawTM

/-- Exact fraction (no normalization, no field structure — a coordinate, not
a number type). -/
structure Frac where
  num : Int
  den : Nat
deriving Repr, DecidableEq

/-- Projective simplex chart: `(a : m : c)` normalized by the total mass.
The death face `{m = 0}` is literally a face of the simplex. -/
def simplexChart (s : AState) : Frac × Frac × Frac :=
  let d := s.a + s.m + s.c
  (⟨s.a, d⟩, ⟨s.m, d⟩, ⟨s.c, d⟩)

/-- The simplex coordinates sum to one (numerators sum to the common
denominator). -/
theorem simplexChart_sum (s : AState) :
    (simplexChart s).1.num + (simplexChart s).2.1.num + (simplexChart s).2.2.num
      = ((s.a + s.m + s.c : Nat) : Int) := by
  simp [simplexChart]

/-- All three simplex coordinates share the same denominator: the total
mass. -/
theorem simplexChart_den (s : AState) :
    (simplexChart s).1.den = s.a + s.m + s.c ∧
      (simplexChart s).2.1.den = s.a + s.m + s.c ∧
      (simplexChart s).2.2.den = s.a + s.m + s.c :=
  ⟨rfl, rfl, rfl⟩

/-- Integer log₂ chart: the additive shadow of multiplicative growth. -/
def log2Chart (s : AState) : Nat × Nat × Nat :=
  (Nat.log2 (s.a + 1), Nat.log2 (s.m + 1), Nat.log2 (s.c + 1))

/-- Upper-half-plane surrogate: `x` the counter/block imbalance, `y` the
total mass (the scale coordinate; always positive, as required of a point
in the upper half-plane). -/
def h2Chart (s : AState) : Int × Nat :=
  ((s.a : Int) - (s.c : Int), s.a + s.m + s.c + 1)

theorem h2Chart_y_pos (s : AState) : 0 < (h2Chart s).2 := by
  simp [h2Chart]

/-- The event process stays strictly inside the upper half-plane. -/
theorem h2Chart_y_pos_eorbit {k : Nat} {s : AState} (h : eorbit k = some s) :
    0 < (h2Chart s).2 :=
  h2Chart_y_pos s

end QIG.Extensions

#print axioms QIG.Extensions.simplexChart_sum
#print axioms QIG.Extensions.h2Chart_y_pos

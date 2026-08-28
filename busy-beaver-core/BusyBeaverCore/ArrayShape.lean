/-!
# Dossier-5 foundation: the array-class shape language

The certified closures of dossier-2/3 rest on tapes describable by a
*fixed* number of integers (`holeTape`: a 1-field with two holes).  The
dossier-4 sweep showed the remaining structured holdouts are
**array-class**: their tapes are unboundedly growing sequences of
blocks — empirically, alternating words of 1-runs separated by single
0s, rewritten by local substitution episodes (e.g. block trisection
`(1) ↦ (1,0,1,0,1)`).

This module is the shape language for that class: a tape realization
function over a `List Nat` of block lengths, with the evaluation and
concatenation lemmas every future episode theorem will need.  Core
Lean only; axioms `[propext, Quot.sound]`.
-/

namespace QIG.ArrayShape

/-- Total width of `blocks` laid out with single-`0` separators:
`b₀ 0 b₁ 0 … 0 bₖ` occupies `(Σ bᵢ) + (k)` cells (one separator
between consecutive blocks). -/
def width : List Nat → Nat
  | [] => 0
  | [b] => b
  | b :: rest => b + 1 + width rest

/-- The array tape: blocks of `1`s of the given lengths, separated by
single `0`s, laid out rightward from `origin`; `0` outside. -/
def arrayTape (origin : Int) (blocks : List Nat) : Int → Bool :=
  fun q =>
    match blocks with
    | [] => false
    | b :: rest =>
        if origin ≤ q ∧ q < origin + (b : Int) then true
        else arrayTape (origin + (b : Int) + 1) rest q

/-- Inside the first block. -/
theorem arrayTape_head {o : Int} {b : Nat} {rest : List Nat} {q : Int}
    (h1 : o ≤ q) (h2 : q < o + (b : Int)) :
    arrayTape o (b :: rest) q = true := by
  unfold arrayTape
  rw [if_pos ⟨h1, h2⟩]

/-- Beyond the first block: evaluation defers to the tail, shifted
past the block and its separator. -/
theorem arrayTape_tail {o : Int} {b : Nat} {rest : List Nat} {q : Int}
    (h : ¬(o ≤ q ∧ q < o + (b : Int))) :
    arrayTape o (b :: rest) q
      = arrayTape (o + (b : Int) + 1) rest q := by
  rw [show arrayTape o (b :: rest) q
        = (if o ≤ q ∧ q < o + (b : Int) then true
           else arrayTape (o + (b : Int) + 1) rest q) from rfl,
      if_neg h]

/-- Left of the layout everything is `0`. -/
theorem arrayTape_before {o : Int} {blocks : List Nat} {q : Int}
    (h : q < o) : arrayTape o blocks q = false := by
  induction blocks generalizing o with
  | nil => rfl
  | cons b rest ih =>
      rw [arrayTape_tail (by intro ⟨h1, _⟩; omega)]
      exact ih (by omega)

/-- The separator cell after the first block reads `0` (the tail is
laid out strictly to its right). -/
theorem arrayTape_sep {o : Int} {b : Nat} {rest : List Nat} :
    arrayTape o (b :: rest) (o + (b : Int)) = false := by
  rw [arrayTape_tail (by intro ⟨_, h⟩; omega)]
  exact arrayTape_before (by omega)

/-- Right of the layout everything is `0`. -/
theorem arrayTape_after {o : Int} {blocks : List Nat} {q : Int}
    (h : o + (width blocks : Int) ≤ q) :
    arrayTape o blocks q = false := by
  induction blocks generalizing o with
  | nil => rfl
  | cons b rest ih =>
      cases rest with
      | nil =>
          rw [arrayTape_tail (by
            intro ⟨_, h2⟩
            simp [width] at h
            omega)]
          rfl
      | cons c cs =>
          rw [arrayTape_tail (by
            intro ⟨_, h2⟩
            simp [width] at h
            omega)]
          exact ih (by simp [width] at h ⊢; omega)

end QIG.ArrayShape
#print axioms QIG.ArrayShape.arrayTape_sep
#print axioms QIG.ArrayShape.arrayTape_after

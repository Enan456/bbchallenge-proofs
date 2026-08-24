import Forge.RawTM

/-!
# Forge instantiations: four machines as data

What used to be a bespoke ~200-line development per machine is now: a
transition table, a three-field `HaltSpec`, and two 12-case finite checks —
after which the generic theorems hand over halt localization and the
probe-safety contract.  The four machines of the program, instantiated:
Antihydra, dossier-1, dossier-2, dossier-3.
-/

namespace QIG.Forge

/-- Uniform instantiation bundle: everything a machine needs to enter the
forge. -/
structure Machine where
  tbl : St → Bool → Option Instr
  spec : HaltSpec
  hhalt : HaltIff tbl spec
  hentry : EntryOnly tbl spec
  hA : spec.haltSt ≠ St.A

/-- The machine's probe contract, delivered by the generic theorems. -/
theorem Machine.blank_nonhalting (M : Machine)
    (hsafe : ProbeSafe M.tbl M.spec blankStart) :
    ¬ RawHalts M.tbl blankStart :=
  blank_nonhalting_of_probe_safe M.tbl M.spec M.hhalt M.hentry M.hA hsafe

namespace Antihydra

def tbl : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.A, true, .R⟩
  | .B, false => some ⟨.C, false, .L⟩
  | .B, true => some ⟨.E, true, .L⟩
  | .C, false => some ⟨.D, true, .L⟩
  | .C, true => some ⟨.C, true, .L⟩
  | .D, false => some ⟨.A, true, .L⟩
  | .D, true => some ⟨.B, false, .L⟩
  | .E, false => some ⟨.F, true, .L⟩
  | .E, true => some ⟨.E, true, .R⟩
  | .F, false => none
  | .F, true => some ⟨.A, false, .R⟩

def spec : HaltSpec := ⟨.F, .E, .L, true⟩

def machine : Machine where
  tbl := tbl
  spec := spec
  hhalt := by
    intro s b
    cases s <;> cases b <;> simp [tbl, spec]
  hentry := by
    intro s b i h hnext
    cases s <;> cases b <;> simp only [tbl] at h <;> cases h <;>
      first
        | exact ⟨rfl, rfl, rfl, rfl⟩
        | exact absurd hnext (by decide)
  hA := by decide

end Antihydra

namespace Dossier1

def tbl : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.E, false, .L⟩
  | .B, false => some ⟨.B, true, .L⟩
  | .B, true => some ⟨.C, true, .R⟩
  | .C, false => some ⟨.F, false, .R⟩
  | .C, true => some ⟨.D, false, .R⟩
  | .D, false => some ⟨.E, true, .R⟩
  | .D, true => some ⟨.A, false, .L⟩
  | .E, false => some ⟨.A, true, .L⟩
  | .E, true => some ⟨.E, true, .R⟩
  | .F, false => none
  | .F, true => some ⟨.B, false, .R⟩

def spec : HaltSpec := ⟨.F, .C, .R, false⟩

def machine : Machine where
  tbl := tbl
  spec := spec
  hhalt := by
    intro s b
    cases s <;> cases b <;> simp [tbl, spec]
  hentry := by
    intro s b i h hnext
    cases s <;> cases b <;> simp only [tbl] at h <;> cases h <;>
      first
        | exact ⟨rfl, rfl, rfl, rfl⟩
        | exact absurd hnext (by decide)
  hA := by decide

end Dossier1

namespace Dossier2

def tbl : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.C, true, .R⟩
  | .B, false => some ⟨.C, true, .L⟩
  | .B, true => some ⟨.C, true, .L⟩
  | .C, false => some ⟨.E, true, .R⟩
  | .C, true => some ⟨.D, false, .L⟩
  | .D, false => some ⟨.B, true, .L⟩
  | .D, true => some ⟨.F, true, .R⟩
  | .E, false => none
  | .E, true => some ⟨.A, true, .R⟩
  | .F, false => some ⟨.D, false, .R⟩
  | .F, true => some ⟨.D, true, .R⟩

def spec : HaltSpec := ⟨.E, .C, .R, true⟩

def machine : Machine where
  tbl := tbl
  spec := spec
  hhalt := by
    intro s b
    cases s <;> cases b <;> simp [tbl, spec]
  hentry := by
    intro s b i h hnext
    cases s <;> cases b <;> simp only [tbl] at h <;> cases h <;>
      first
        | exact ⟨rfl, rfl, rfl, rfl⟩
        | exact absurd hnext (by decide)
  hA := by decide

end Dossier2

namespace Dossier3

def tbl : St → Bool → Option Instr
  | .A, false => some ⟨.B, true, .R⟩
  | .A, true => some ⟨.B, true, .R⟩
  | .B, false => some ⟨.C, true, .L⟩
  | .B, true => some ⟨.E, false, .R⟩
  | .C, false => none
  | .C, true => some ⟨.D, true, .L⟩
  | .D, false => some ⟨.A, false, .R⟩
  | .D, true => some ⟨.B, true, .L⟩
  | .E, false => some ⟨.A, true, .R⟩
  | .E, true => some ⟨.F, true, .L⟩
  | .F, false => some ⟨.E, false, .L⟩
  | .F, true => some ⟨.E, true, .L⟩

def spec : HaltSpec := ⟨.C, .B, .L, true⟩

def machine : Machine where
  tbl := tbl
  spec := spec
  hhalt := by
    intro s b
    cases s <;> cases b <;> simp [tbl, spec]
  hentry := by
    intro s b i h hnext
    cases s <;> cases b <;> simp only [tbl] at h <;> cases h <;>
      first
        | exact ⟨rfl, rfl, rfl, rfl⟩
        | exact absurd hnext (by decide)
  hA := by decide

end Dossier3

end QIG.Forge

#print axioms QIG.Forge.Antihydra.machine
#print axioms QIG.Forge.Dossier1.machine
#print axioms QIG.Forge.Dossier2.machine
#print axioms QIG.Forge.Dossier3.machine
#print axioms QIG.Forge.Machine.blank_nonhalting

import BusyBeaverCore.AntihydraRawTM
import BusyBeaverCore.Dossier1RawTM
import BusyBeaverCore.Dossier2RawTM
import BusyBeaverCore.Dossier3RawTM

/-!
# Standard-format parser and table-equality theorems (plan 1, task 1)

The hand-transcribed `instr` tables in `AntihydraRawTM` / `Dossier1RawTM` are
the single trust-critical transcription in the whole development.  This module
removes that trust requirement mechanically: a total parser from bbchallenge
standard-format machine codes to an encoded transition table, `decide`-proved
equal to the encoding of each hand-written table, plus a corrupted-code
negative control and injectivity of the encoding (so table equality really
does pin down the `instr` function).

**Axiom hygiene.**  The certified statements are over `List Char` literals,
not `String`: in this toolchain `String.toList` transitively references
`Classical.choice`, and every theorem here must stay at the main
development's `[propext, Quot.sound]` bar (`decide` on `Char`-list values is
axiom-free).  The `String` versions of the codes are provided for display,
with linking lemmas (`code_chars`) quarantined at the end of the file — those
two lemmas alone additionally report `Classical.choice`, which is expected
and documented.  No `native_decide` anywhere.
-/

namespace QIG.Parity

/-- Encoded table entry: `none` = undefined transition, otherwise
`(next-state index 0–5, write bit, direction-is-right)`. -/
abbrev Entry := Option (Nat × Bool × Bool)

def symOf : Char → Option Bool
  | '0' => some false
  | '1' => some true
  | _ => none

def dirOf : Char → Option Bool
  | 'L' => some false
  | 'R' => some true
  | _ => none

def stOf : Char → Option Nat
  | 'A' => some 0
  | 'B' => some 1
  | 'C' => some 2
  | 'D' => some 3
  | 'E' => some 4
  | 'F' => some 5
  | _ => none

/-- Parse a standard-format code character stream into entries.  Group
separators `_` are skipped; `---` is the undefined transition; otherwise an
entry is `<write><dir><next>`.

Informally: the community's machine notation, executable inside the
kernel — total, structural, and over `List Char` so that `decide` on it
remains axiom-clean (over `String` it would drag in `Classical.choice`). -/
def parseEntries : List Char → Option (List Entry)
  | [] => some []
  | '_' :: rest => parseEntries rest
  | '-' :: '-' :: '-' :: rest =>
      match parseEntries rest with
      | none => none
      | some es => some (none :: es)
  | w :: d :: s :: rest =>
      match symOf w, dirOf d, stOf s, parseEntries rest with
      | some wb, some db, some sn, some es => some (some (sn, wb, db) :: es)
      | _, _, _, _ => none
  | _ => none

/-- Parse a full 6-state standard-format machine code (12 entries). -/
def parseMachine (code : String) : Option (List Entry) :=
  match parseEntries code.toList with
  | some es => if es.length = 12 then some es else none
  | none => none

/-! ## Antihydra -/

namespace Antihydra

open QIG.AntihydraRawTM

def stIdx : State → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def dirR : Dir → Bool
  | .L => false | .R => true

def encodeEntry (i : Option Instr) : Entry :=
  i.map fun i => (stIdx i.next, i.write, dirR i.dir)

/-- Row-major encoding of a transition function, in the standard-format
order `A0 A1 B0 B1 … F0 F1`. -/
def tableOfF (f : State → Bool → Option Instr) : List Entry :=
  [encodeEntry (f .A false), encodeEntry (f .A true),
   encodeEntry (f .B false), encodeEntry (f .B true),
   encodeEntry (f .C false), encodeEntry (f .C true),
   encodeEntry (f .D false), encodeEntry (f .D true),
   encodeEntry (f .E false), encodeEntry (f .E true),
   encodeEntry (f .F false), encodeEntry (f .F true)]

/-- `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`, as characters. -/
def codeChars : List Char :=
  ['1', 'R', 'B', '1', 'R', 'A', '_', '0', 'L', 'C', '1', 'L', 'E', '_',
   '1', 'L', 'D', '1', 'L', 'C', '_', '1', 'L', 'A', '0', 'L', 'B', '_',
   '1', 'L', 'F', '1', 'R', 'E', '_', '-', '-', '-', '0', 'R', 'A']

/-- **The machine we reason about is the machine on the label.**  Parsing the
published standard-format code yields exactly the hand-written table.

Informally: the one human transcription in the trust base, checked by the
kernel.  The proof term is a single `decide`: the parser runs on the
41-character code *inside the proof checker*, and the resulting table is
compared to `instr` bit for bit.  No reviewer needs to squint at the
table again. -/
theorem parse_ok : parseEntries codeChars = some (tableOfF instr) := by decide

/-- Negative control: a corrupted code (last entry `0RA → 0RB`) does *not*
parse to our table, so `parse_ok` is not vacuous.

Informally: proof that the test can fail — flip one character and the
kernel notices.  A parity theorem that could not detect corruption would
prove nothing. -/
theorem parse_detects_corruption :
    parseEntries
      ['1', 'R', 'B', '1', 'R', 'A', '_', '0', 'L', 'C', '1', 'L', 'E', '_',
       '1', 'L', 'D', '1', 'L', 'C', '_', '1', 'L', 'A', '0', 'L', 'B', '_',
       '1', 'L', 'F', '1', 'R', 'E', '_', '-', '-', '-', '0', 'R', 'B']
      ≠ some (tableOfF instr) := by decide

theorem stIdx_inj {a b : State} (h : stIdx a = stIdx b) : a = b := by
  cases a <;> cases b <;> simp_all [stIdx]

theorem dirR_inj {a b : Dir} (h : dirR a = dirR b) : a = b := by
  cases a <;> cases b <;> simp_all [dirR]

theorem encodeEntry_inj {x y : Option Instr}
    (h : encodeEntry x = encodeEntry y) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some j => simp [encodeEntry] at h
  | some i => cases y with
    | none => simp [encodeEntry] at h
    | some j =>
        obtain ⟨ni, wi, di⟩ := i
        obtain ⟨nj, wj, dj⟩ := j
        simp [encodeEntry] at h
        obtain ⟨h1, h2, h3⟩ := h
        cases stIdx_inj h1
        cases dirR_inj h3
        cases h2
        rfl

/-- The encoding is injective on transition functions: table equality pins
down `instr` itself.

Informally: without this, `parse_ok` would only say the *encodings* agree;
with it, agreement of encodings forces agreement of the functions — so the
parse theorem really does determine the machine. -/
theorem tableOfF_inj {f g : State → Bool → Option Instr}
    (h : tableOfF f = tableOfF g) : f = g := by
  simp [tableOfF] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  funext s b
  cases s <;> cases b
  · exact encodeEntry_inj h1
  · exact encodeEntry_inj h2
  · exact encodeEntry_inj h3
  · exact encodeEntry_inj h4
  · exact encodeEntry_inj h5
  · exact encodeEntry_inj h6
  · exact encodeEntry_inj h7
  · exact encodeEntry_inj h8
  · exact encodeEntry_inj h9
  · exact encodeEntry_inj h10
  · exact encodeEntry_inj h11
  · exact encodeEntry_inj h12

/-- Corollary in the useful direction: any transition function whose encoding
is what the code parses to *is* `instr`. -/
theorem instr_unique {f : State → Bool → Option Instr}
    (h : parseEntries codeChars = some (tableOfF f)) : f = instr := by
  have hok := parse_ok
  rw [h] at hok
  exact tableOfF_inj (Option.some.inj hok)

end Antihydra

/-! ## Dossier-1 -/

namespace Dossier1

open QIG.Dossier1RawTM

def stIdx : State → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def dirR : Dir → Bool
  | .L => false | .R => true

def encodeEntry (i : Option Instr) : Entry :=
  i.map fun i => (stIdx i.next, i.write, dirR i.dir)

def tableOfF (f : State → Bool → Option Instr) : List Entry :=
  [encodeEntry (f .A false), encodeEntry (f .A true),
   encodeEntry (f .B false), encodeEntry (f .B true),
   encodeEntry (f .C false), encodeEntry (f .C true),
   encodeEntry (f .D false), encodeEntry (f .D true),
   encodeEntry (f .E false), encodeEntry (f .E true),
   encodeEntry (f .F false), encodeEntry (f .F true)]

/-- `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`, as characters. -/
def codeChars : List Char :=
  ['1', 'R', 'B', '0', 'L', 'E', '_', '1', 'L', 'B', '1', 'R', 'C', '_',
   '0', 'R', 'F', '0', 'R', 'D', '_', '1', 'R', 'E', '0', 'L', 'A', '_',
   '1', 'L', 'A', '1', 'R', 'E', '_', '-', '-', '-', '0', 'R', 'B']

theorem parse_ok : parseEntries codeChars = some (tableOfF instr) := by decide

/-- Negative control (entry `E0` corrupted `1LA → 1RA`). -/
theorem parse_detects_corruption :
    parseEntries
      ['1', 'R', 'B', '0', 'L', 'E', '_', '1', 'L', 'B', '1', 'R', 'C', '_',
       '0', 'R', 'F', '0', 'R', 'D', '_', '1', 'R', 'E', '0', 'L', 'A', '_',
       '1', 'R', 'A', '1', 'R', 'E', '_', '-', '-', '-', '0', 'R', 'B']
      ≠ some (tableOfF instr) := by decide

end Dossier1


/-! ## Dossier2 -/

namespace Dossier2

open QIG.Dossier2RawTM

def stIdx : State → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def dirR : Dir → Bool
  | .L => false | .R => true

def encodeEntry (i : Option Instr) : Entry :=
  i.map fun i => (stIdx i.next, i.write, dirR i.dir)

def tableOfF (f : State → Bool → Option Instr) : List Entry :=
  [encodeEntry (f .A false), encodeEntry (f .A true),
   encodeEntry (f .B false), encodeEntry (f .B true),
   encodeEntry (f .C false), encodeEntry (f .C true),
   encodeEntry (f .D false), encodeEntry (f .D true),
   encodeEntry (f .E false), encodeEntry (f .E true),
   encodeEntry (f .F false), encodeEntry (f .F true)]

/-- `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`, as characters. -/
def codeChars : List Char :=
  ['1', 'R', 'B', '1', 'R', 'C', '_', '1', 'L', 'C', '1', 'L', 'C', '_',
   '1', 'R', 'E', '0', 'L', 'D', '_', '1', 'L', 'B', '1', 'R', 'F', '_',
   '-', '-', '-', '1', 'R', 'A', '_', '0', 'R', 'D', '1', 'R', 'D']

theorem parse_ok : parseEntries codeChars = some (tableOfF instr) := by decide

end Dossier2

/-! ## Dossier3 -/

namespace Dossier3

open QIG.Dossier3RawTM

def stIdx : State → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def dirR : Dir → Bool
  | .L => false | .R => true

def encodeEntry (i : Option Instr) : Entry :=
  i.map fun i => (stIdx i.next, i.write, dirR i.dir)

def tableOfF (f : State → Bool → Option Instr) : List Entry :=
  [encodeEntry (f .A false), encodeEntry (f .A true),
   encodeEntry (f .B false), encodeEntry (f .B true),
   encodeEntry (f .C false), encodeEntry (f .C true),
   encodeEntry (f .D false), encodeEntry (f .D true),
   encodeEntry (f .E false), encodeEntry (f .E true),
   encodeEntry (f .F false), encodeEntry (f .F true)]

/-- `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`, as characters. -/
def codeChars : List Char :=
  ['1', 'R', 'B', '1', 'R', 'B', '_', '1', 'L', 'C', '0', 'R', 'E', '_',
   '-', '-', '-', '1', 'L', 'D', '_', '0', 'R', 'A', '1', 'L', 'B', '_',
   '1', 'R', 'A', '1', 'L', 'F', '_', '0', 'L', 'E', '1', 'L', 'E']

theorem parse_ok : parseEntries codeChars = some (tableOfF instr) := by decide

end Dossier3

/-! ## String display forms (quarantined: these two lemmas alone use
`String.toList`, which transitively reports `Classical.choice`) -/

def antihydraCode : String := "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

def dossier1Code : String := "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"

theorem antihydra_code_chars : antihydraCode.toList = Antihydra.codeChars := by
  decide

theorem dossier1_code_chars : dossier1Code.toList = Dossier1.codeChars := by
  decide

end QIG.Parity

#print axioms QIG.Parity.Antihydra.parse_ok
#print axioms QIG.Parity.Antihydra.parse_detects_corruption
#print axioms QIG.Parity.Antihydra.instr_unique
#print axioms QIG.Parity.Dossier1.parse_ok
#print axioms QIG.Parity.Dossier1.parse_detects_corruption
#print axioms QIG.Parity.Dossier2.parse_ok
#print axioms QIG.Parity.Dossier3.parse_ok
#print axioms QIG.Parity.antihydra_code_chars

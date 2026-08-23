import BusyBeaverCore.AntihydraRawTM
import BusyBeaverCore.Dossier1RawTM

/-!
# Differential-trace executable (plan 1, task 2)

Runs the *proved* semantics (`step` iterated from `blankStart`) and prints
one line per step: `index state head window`, where `window` is the 33 tape
cells `[head−16, head+16]`.  A Python reference implementation produces the
identical format from the standard-format code; byte-equality of the traces
is the differential-parity test.

The functional tape means step `i` costs `O(i)` cell reads, so keep `n` in
the low thousands — this is a semantics cross-check, not a simulator.
-/

def boolChar (b : Bool) : Char := if b then '1' else '0'

namespace TraceA

open QIG.AntihydraRawTM

def stChar : State → Char
  | .A => 'A' | .B => 'B' | .C => 'C' | .D => 'D' | .E => 'E' | .F => 'F'

def line (i : Nat) (c : Config) : String :=
  let win := String.ofList ((List.range 33).map fun (k : Nat) =>
    boolChar (c.tape (c.head - 16 + Int.ofNat k)))
  s!"{i} {stChar c.state} {c.head} {win}"

def run (n : Nat) : IO Unit := do
  let mut c := blankStart
  for i in [0:n] do
    IO.println (line i c)
    match step c with
    | none =>
        IO.println s!"{i + 1} HALT"
        return
    | some c' => c := c'

end TraceA

namespace TraceD

open QIG.Dossier1RawTM

def stChar : State → Char
  | .A => 'A' | .B => 'B' | .C => 'C' | .D => 'D' | .E => 'E' | .F => 'F'

def line (i : Nat) (c : Config) : String :=
  let win := String.ofList ((List.range 33).map fun (k : Nat) =>
    boolChar (c.tape (c.head - 16 + Int.ofNat k)))
  s!"{i} {stChar c.state} {c.head} {win}"

def run (n : Nat) : IO Unit := do
  let mut c := blankStart
  for i in [0:n] do
    IO.println (line i c)
    match step c with
    | none =>
        IO.println s!"{i + 1} HALT"
        return
    | some c' => c := c'

end TraceD

def main (args : List String) : IO Unit := do
  let machine := args.getD 0 "antihydra"
  let n := ((args.getD 1 "2000").toNat?).getD 2000
  match machine with
  | "antihydra" => TraceA.run n
  | "dossier1" => TraceD.run n
  | _ => IO.eprintln s!"unknown machine: {machine} (want antihydra|dossier1)"

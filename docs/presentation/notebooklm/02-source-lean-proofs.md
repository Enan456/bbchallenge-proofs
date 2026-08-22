# The Lean Proofs: From Raw Tape to a Single Conjecture

*NotebookLM source document 2 of 4 — the machine-checked mathematics.
Self-contained.*

## Two machines, one architecture

The project's formal work centers on two six-state, two-symbol Turing
machines from the BB(6) open set, written in the community's standard text
format:

- **Antihydra**: `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` — the most
  famous BB(6) cryptid.
- **Dossier-1**: `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` — an unsolved
  holdout with a richer, stack-like structure.

Both developments live in Lean 4, deliberately restricted to core Lean: no
Mathlib, no automation beyond the built-in `omega` arithmetic solver, and a
mechanically enforced axiom budget of exactly two universally trusted
axioms, `propext` and `Quot.sound`. The point of the austerity is
auditability: a reviewer can read the entire trust base — the transition
table, the tape, the step function — in minutes.

## Layer one: raw semantics and halt localization

A configuration is a control state, an integer head position, and a tape
modeled as a total function from integers to booleans. One step consults
the transition table; the single undefined entry (state F reading 0) is the
only way to halt. Three foundational theorems per machine:

1. The machine halts in one step exactly at that undefined transition.
2. State F is only ever *entered* from one specific transition — so any
   halt is preceded by a specific local tape pattern.
3. Halt localization: any halting run must pass through a reachable "probe"
   — the danger state reading a 0 whose critical neighbor is also 0.

This yields the safety contract: if every 0 the danger state ever reads has
a 1 on the critical side, the machine can never halt.

## Layer two: the collapse dynamics, proved rule by rule

Watch either machine at its records — the moments it reaches fresh tape —
and the tape is always solid blocks of ones separated by single zeros. The
block lengths evolve by exact arithmetic rules, and each rule became a
theorem giving the exact raw trajectory *for all block values*, along with
a safety certificate that no halt can occur during the rule.

For Antihydra there are three rules acting on triples (a, m, c): the
*hydra* rule (m ≥ 3) runs exactly 2c + 11 raw steps and sends
(a, m, c) to (a, m − 2, c + 3) with the counter a untouched — about 96
percent of all dynamics; the *drop* (m = 2) costs the counter one unit; the
*merge* (m = 1) feeds it two. The abstract orbit iterates these from
(2, 7, 2), reached from the blank tape by a proven 62-step startup. The
orbit dies — and only then can the machine possibly halt — exactly when a
drop fires with the counter at 1 or less. The conjecture `SafeOrbitA`
says the orbit never dies. The main theorem: **SafeOrbitA implies Antihydra
never halts from the blank tape** — machine-checked, no sorry, two axioms.

Dossier-1 is the same architecture with a deeper abstract state: a *stack*
of chain levels (a list of numbers) plus an active pair, with seven proven
transport rules including genuine collapse cascades where the last level
folds into its parent. Its conjecture `SafeOrbit` encodes a recursive
Collatz checkpoint law (odd n maps to (3n+7)/2). Main theorem: **SafeOrbit
implies dossier-1 never halts from the blank tape.**

## The bridge to the community's conjecture

The community states the Antihydra conjecture one-dimensionally: iterate
b → b + ⌊b/2⌋ from 8, keep a heads counter that gains 2 on even values and
loses 1 on odd values, and the machine halts if the counter would go
negative. A bridge theorem proves a step-for-step conjugacy between the
project's triple orbit and this 1-D process: the hidden change of variables
is b = m + 2(c−2)/3 + 5, the machine's counter block *is* the heads
counter, and the parities line up exactly — merges are the even steps,
drops are the odd ones. The proof runs the two processes in lock-step and
shows deaths coincide.

One honest delta is documented rather than hidden: the formal tape grammar
needs a non-empty counter block, so the formal orbit stops tracking the
machine one drop *earlier* than the community's process — death at counter
≤ 1 instead of exactly 0, and the sequence starts at 12 = H(8) because the
proven startup absorbs the first term. So the formal hypothesis is possibly
*stronger* than the wiki's conjecture by one boundary case, listed as open
follow-up work.

## Trust engineering: parity, parsing, and axiom hunting

Three supporting layers make the trust story checkable rather than takeable
on faith:

- **Parser parity.** The hand-typed transition tables were the one
  trust-critical transcription. A total parser from the standard text
  format, written in Lean, is proved by kernel computation to produce
  exactly the hand-written tables — with corrupted-code negative controls
  so the theorem cannot pass vacuously.
- **Differential testing.** The proved step function was made executable
  and byte-compared, step by step for thousands of steps, against an
  independent thirty-line Python simulator. The traces agree exactly, and
  the proven startup milestones appear at the right steps.
- **Axiom hunting.** Two subtle contamination channels were discovered and
  engineered around: Lean's `omega` tactic quietly uses the classical
  choice axiom when asked to prove a positive "and"/"or" goal (feed it only
  atomic goals and it stays clean), and the innocuous `String.toList`
  function drags classical choice into any proof that touches it (certify
  over character lists instead). Every headline theorem reports exactly
  `propext` and `Quot.sound`, verified by a gate script on every build.

## What is and is not claimed

Proven: every dynamical statement about both machines, the reductions, the
bridge, the parser parity. Assumed: the two orbit conjectures — one of
which is the famous Antihydra conjecture, believed true on random-walk
grounds and proven by no one. Decided: nothing. The machines' fates remain
open; what changed is that each fate now *is* a clean arithmetic statement.

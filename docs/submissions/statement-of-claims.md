# Statement of claims

Precise inventory of what this repository proves, what it assumes, and what
it does **not** claim.  Updated 2026-08-22 (packages split + bridge layer).

## Machine 1: Antihydra — `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`

### Proven, machine-checked, axioms `[propext, Quot.sound]`, no sorry

In `lean/BBChallenge/AntihydraRawTM.lean`:

- `step_eq_none_iff` — the machine halts in one step iff it is in state `F`
  reading `0`.
- `halt_requires_e_probe_00` — any halt from a non-`F` start passes through a
  reachable `E`-probe of a `00` pattern.
- `hydra_step` / `drop_step` / `merge_chain` — the three record transitions,
  exact step counts, for **all** block values, each with an `ESafeSeg`
  safety certificate.
- `safeOrbitA_nonhalting : SafeOrbitA → ¬ RawHalts blankStart` — non-halting
  from blank tape is formally reduced to the abstract triple-orbit
  conjecture `SafeOrbitA`.

In `packages/bbchallenge/Bridge/` (2026-08-22):

- `parse_ok` (axioms `[propext]`) — the bbchallenge standard-format code,
  parsed mechanically, equals the hand-written transition table (with a
  corrupted-code negative control, and encoding injectivity `instr_unique`).
- `astep_eq_none_iff` — the abstract orbit dies exactly on the death set
  `{m = 0} ∪ {m = 2, a ≤ 1}`.
- `eventSafe_iff_safeOrbitA` — **boundary-only checking is sound and
  complete**: the orbit sampled at incision events (one per counter
  movement, the intervening hydra volleys collapsed in closed form) dies iff
  the full orbit dies.
- `hydraSafe_iff_safeOrbitA` and `hydraSafe_nonhalting : HydraSafe →
  ¬ RawHalts blankStart` — the orbit conjecture is proved equivalent to a
  1-D statement in the community's own shape: iterate `b ↦ b + ⌊b/2⌋` from
  `b = 12` with a heads counter from `2` (`+2` on even `b`, `−1` on odd);
  `HydraSafe` says no odd value is ever faced with heads `≤ 1`.

### Assumed (the hypothesis; NOT proven)

`SafeOrbitA` / equivalently `HydraSafe`.  This is a (slightly strengthened)
form of the community's **Antihydra conjecture** (BusyBeaverWiki: `h₀ = 8`,
`H(n) = ⌊3n/2⌋`, counter `+2`/`−1`, halt at counter `−1`).  Two deliberate
deltas, both machine-checked where they live and documented in
`Bridge/Conjecture.lean`:

1. our sequence starts at `b = 12 = H(8)` with heads `= 2` — the 62-step
   startup absorbs the wiki's first term;
2. our death fires at heads `≤ 1` on an odd value, one counter-unit earlier
   than the wiki's `= 0`: the tape grammar `Realizes` requires a non-empty
   counter block, so the abstract orbit stops tracking the machine one drop
   sooner.  `HydraSafe` is therefore possibly strictly **stronger** than the
   wiki conjecture; closing that single boundary case (grammar extension to
   `a = 0`) is open follow-up work, listed in plan 2.

## Machine 2: dossier-1 — `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`

### Proven (axioms `[propext, Quot.sound]`, no sorry)

- Halt localization to the `C`-probe of `00`; all seven record transitions
  for all block values; the 35-step startup; the chain-state tape grammar;
  the segment induction; `safeOrbit_nonhalting : SafeOrbit → ¬ RawHalts
  blankStart` (`lean/BBChallenge/Dossier1RawTM.lean`).
- `parse_ok` for its standard-format code (`packages/bbchallenge`).

### Assumed

`SafeOrbit` — the machine's recursive Collatz checkpoint law (odd
`n → (3n+7)/2`, even recurses).  The formal 1-D bridge lemma (the analogue
of `hydraSafe_iff_safeOrbitA`) is **not yet built** for this machine.

## Differential validation (not proof, evidence)

- `tests/lean_parity/` — the Lean `step` semantics, run executably, is
  byte-identical for 2,000 steps against an independent ~30-line Python
  reference stepper on both machines; the proven startup anchors (step 62 →
  `B@6`, step 35 → `E@5`) hold in the independent trace.
- stage747–755 — the empirical macro systems: 100% exact replay over 10⁸
  steps, 13/13 and 33/33 obligations discharged.  Bounded-trace evidence
  only.

## Non-claims

- **No machine is decided by anything in this repository.**
- Empirical macro-obligation discharges are statements about bounded
  observed traces, not proofs.
- Stage756 incision-atlas figures and metrics are bounded empirical
  structure under heuristic event definitions (except Antihydra's exact
  mode, which mirrors the certified event process but is still just a
  finite prefix).
- The corrected open-set classification stands at 6 solid + 1 weak
  `PASS_EXACT_MACRO_SYSTEM` after the 2026-08-04 gate fix; the earlier count
  of 9 is refuted.

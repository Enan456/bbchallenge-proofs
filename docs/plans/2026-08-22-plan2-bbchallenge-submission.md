# Plan 2 — Package and submit the bbchallenge results

> **Execution status (2026-08-22):** Task 1 DONE for Antihydra
> (`Bridge/Conjecture.lean`: `hydraSafe_iff_safeOrbitA`,
> `hydraSafe_nonhalting`; wiki statement fetched and pinned; the heads
> `≤ 1` vs `= 0` death delta documented — closing it, and the dossier-1
> `(3n+7)/2` bridge, remain open).  Task 2 DONE
> (`docs/submissions/statement-of-claims.md`).  Task 3 partial (axiom-gate
> script done; LICENSE needs a user decision; toolchain stays on the
> rc pin).  Task 4 partial (Antihydra wiki page consulted 2026-08-22 for
> the conjecture statement; full registry/novelty sweep pending).
> Tasks 5–6 untouched (user sign-off gates).
>
> **Palomar (2026-08-22, later):** all three results are packaged and
> locally validated as entries for Terence Tao's Palomar registry
> (announced 2026-08-18) — Challenge/Solution pairs + comparator configs +
> per-entry `formalization.yaml` in `packages/bbchallenge`, validator
> `scripts/check_palomar.py`, toolchain moved to **stable v4.30.0**
> (superseding the "stays on the rc pin" note above).  See
> `docs/results/2026-08-22-palomar-validation.md`.  Submission blockers:
> root LICENSE (owner decision), push to the public remote, and owner
> sign-off — Palomar registration is a new, additional publication channel
> alongside this plan's wiki/forum track.

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking. **Per user preference, code
> implementation is routed through the Codex rescue agent
> (`codex:codex-rescue`), not general-purpose subagents.** Tasks 5–6 are
> outward-facing (posting to community venues) and require explicit user
> sign-off before execution — do not automate them.

**Goal:** Turn what is already proven into a submission the bbchallenge
community can evaluate: two axiom-clean, sorry-free Lean reductions —
`safeOrbitA_nonhalting : SafeOrbitA → ¬ RawHalts blankStart` (Antihydra) and
`safeOrbit_nonhalting : SafeOrbit → ¬ RawHalts blankStart` (dossier-1) —
plus the supporting empirical dossiers, packaged honestly as **conditional
reductions**, not as decisions of any machine.

**What we have / what is missing (inventory):**
- Done: both main theorems, all dynamical lemmas, startup runs, closure
  inductions; empirical discharge of 13/13 + 33/33 macro obligations
  (stage753); full open-set classification with the 2026-08-04 correction.
- Missing for submission: (a) a machine-checked bridge from our orbit form
  `SafeOrbitA` to the community's standard statement of the Antihydra
  conjecture, so reviewers recognize the hypothesis; (b) parity evidence
  (plan 1); (c) packaging — license, CI, statement-of-claims, registry due
  diligence (the README explicitly forbids submitting before checking the
  live registry and asking about unpublished verdicts).

---

### Task 1: Bridge lemma — `SafeOrbitA` ⟷ the standard Antihydra conjecture

The community states the Antihydra conjecture as a fact about the hydra
recurrence on a single integer (repeated `n ↦ n + ⌊n/2⌋`-type updates with a
two-counter side condition). Our form is about the `(a, m, c)` triple orbit.
A reviewer should not have to trust that these coincide.

**Files:**
- Create: `lean/BBChallenge/AntihydraConjecture.lean`

**Steps:**
- [ ] Write down the community-standard recurrence in Lean (source it from the
      BusyBeaverWiki Antihydra page; pin the wording in a docstring).
- [ ] Prove the correspondence: our `aorbit` is the standard sequence in
      disguise — exhibit the value map between `AState` triples and the
      standard `(hydra value, counter)` pairs, prove it commutes with one
      step of each system, and conclude `SafeOrbitA ↔ AntihydraConjecture`.
- [ ] If the equivalence turns out only one-directional
      (`Conjecture → SafeOrbitA`), that still suffices — document which
      direction is proven and state the main corollary
      `AntihydraConjecture → ¬ RawHalts blankStart`.
- [ ] Same exercise for dossier-1's `SafeOrbit` against its Collatz
      checkpoint law (odd `n → (3n+7)/2`), which we named in prose but never
      tied to `astep` formally.
- [ ] `#print axioms` stays `[propext, Quot.sound]`.

### Task 2: Statement-of-claims document

**Files:**
- Create: `docs/submissions/statement-of-claims.md`

**Steps:**
- [ ] One page per machine: exact theorem statement, exact hypothesis, what
      is empirical vs proven, reproduction commands, axiom report. Reuse the
      honest-scope language from
      `docs/results/2026-07-28-bb6-collatz-mass-classification.md`.
- [ ] Explicitly enumerate non-claims (no machine decided; macro-obligation
      discharges are bounded-trace evidence; the corrected 6-solid+1-weak
      PASS count with the 2026-08-04 gate fix).

### Task 3: Repo hardening

**Steps:**
- [ ] Add a LICENSE (repo currently has none — user to choose; MIT or
      CC-BY-4.0 are community-typical).
- [ ] CI from plan 1 task 5 (build + axiom gate + parity tests) running on
      the public repo.
- [ ] Decide toolchain: stay on `v4.30.0-rc2` or move to the nearest stable;
      rebuild and re-verify either way.
- [ ] README pass: current status lines, link the three learning docs, add
      the bridge-lemma statement once task 1 lands.
- [ ] Optional (nice-to-have, not blocking): the Set 1 kernel consolidation,
      so reviewers audit one raw-TM file instead of two clones.

### Task 4: Registry and novelty due diligence (research, no posting)

**Steps:**
- [ ] Check the live bbchallenge registry/wiki for the current status of
      Antihydra, dossier-1's code (`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`),
      and Dvisetu — any published or in-flight verdicts supersede this plan.
- [ ] Survey existing formal Antihydra reductions (the wiki's Antihydra page
      and forum) — if a comparable Rocq/Lean reduction already exists,
      reposition ours as an independent verification and cite it.
- [ ] Record findings in `docs/results/2026-08-XX-registry-due-diligence.md`.

### Task 5: Finalize the wiki/forum materials (user sign-off required)

**Steps:**
- [ ] Update the two draft `.mediawiki` pages in `docs/submissions/` with the
      bridge lemma, axiom reports, and repo link; have the user review the
      dossier-1 naming question (deliberately unnamed so far).
- [ ] Draft the forum/Discord post: short claim, hypothesis, reproduction
      one-liner, ask about unpublished verdicts *before* the wiki edit.

### Task 6: Publish (user executes or explicitly approves each step)

**Steps:**
- [ ] Public GitHub repo (or confirm the existing remote), tagged release.
- [ ] Zenodo (or equivalent) archival DOI of the tagged release.
- [ ] Forum post → incorporate feedback → wiki page.

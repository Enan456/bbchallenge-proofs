#!/usr/bin/env python3
"""phase-2.1 RAW-STEP LEAN GENERATOR.

Emits a complete conditional-closure package from a BB(6) machine table,
generalizing the nine hand-built tranche closures (dossiers 9-18) into
push-button form.

The four hand-built templates that span the design space are:

* Dossier9RawTM.lean  -- right-grower, halt-is-probe, one-sided
* Dossier13RawTM.lean -- left-grower,  halt-is-probe, one-sided
* Dossier14RawTM.lean -- two-sided, left records (probe pushes)
* Dossier16RawTM.lean -- two-sided, right records (probe pushes)

They are ~95% identical.  All four are instances of ONE parameterized
engine.  The generator takes five inputs and derives the rest:

  1. machine code           e.g. 1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB
  2. growth orientation     'R' (records at fresh right extremes) or 'L'
  3. probe descriptor       derived: the (state,read) of the `---` cell,
                            one-cell halt-is-probe (guard = the probed cell)
  4. record side            = orientation (which extreme carries records)
  5. audit row (optional)   experiments/outputs/audit_openset.jsonl row

Derived:
  * push/pop directions      push=L,pop=R for right-grower; swapped for left
  * push variant             'specialized' if the probe never moves in the
                             push direction (one-sided), else 'general'
                             (two-sided: probe may push -> push_step carries
                             the same localized safety hypothesis as the pops)
  * naming convention        'letter' (BProbeSafe/dsafe_compose...) for
                             specialized, 'generic' (ProbeSafe/bsafe_compose)
                             for general -- matching the hand-built corpus

The boilerplate engine (Config/step/stepN/RawHalts, the go/wfuel/wstep
sweep, worbit, the transport fuel-induction, the keystone) is copied
verbatim from the matching template file with probe-letter/dossier-number
retargeting, guaranteeing the delicate omega arithmetic is byte-for-byte
known-good.  Only the machine-specific sections are freshly generated:
the transition table, the corridor lemma, `go`, and `go_faithful`.

Artifacts emitted to a target dir:
  * busy-beaver-core/BusyBeaverCore/Dossier{N}RawTM.lean
  * qgkit/bb6/dossier{N}_mirror.py
  * tests/bb6/test_d{N}_theorems.py
  * packages/dossier1/Palomar/Dossier{N}Challenge.lean
  * packages/dossier1/Palomar/Dossier{N}Solution.lean
  * packages/dossier1/comparator-dossier{N}.json
  * packages/dossier1/palomar-meta/dossier{N}/formalization.yaml

Pitfalls honored (nine closures of lessons): never rw on stepN goals;
omega with not-(A and B) pulls Classical.choice; Lean core only;
set_option before doc-comments; maxRecDepth 100000; autoImplicit false.
"""
import os
import re
import argparse
from collections import deque

STATES = "ABCDEF"
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CORE = os.path.join(REPO, "busy-beaver-core", "BusyBeaverCore")

# master template file per (orientation, variant); each is a hand-built,
# axiom-clean, kernel-checked closure whose boilerplate we reuse verbatim.
MASTERS = {
    ("R", "specialized"): ("Dossier9RawTM.lean", "B", "9"),
    ("L", "specialized"): ("Dossier13RawTM.lean", "D", "13"),
    ("L", "general"): ("Dossier14RawTM.lean", "B", "14"),
    ("R", "general"): ("Dossier16RawTM.lean", "F", "16"),
}


# ---------------------------------------------------------------- parsing

def parse_code(code):
    """code -> {(state_letter, read_bit): (next_letter, write_bool, dir) | None}."""
    tbl = {}
    blocks = code.split("_")
    if len(blocks) != 6:
        raise ValueError(f"expected 6 state blocks, got {len(blocks)}: {code}")
    for si, block in enumerate(blocks):
        s = STATES[si]
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            if tr == "---":
                tbl[(s, b)] = None
            else:
                tbl[(s, b)] = (tr[2], tr[0] == "1", tr[1])
    return tbl


def bstr(v):
    return "true" if v else "false"


def rstr(b):
    return "false" if b == 0 else "true"


class Spec:
    def __init__(self, code, orient, N):
        self.code = code
        self.orient = orient
        self.N = str(N)
        self.tbl = parse_code(code)
        halts = [(s, b) for (s, b), tr in self.tbl.items() if tr is None]
        if len(halts) != 1:
            raise ValueError(f"expected exactly one `---` halt, got {halts}")
        self.probe, self.probe_read = halts[0]
        self.P = self.probe
        self.p = self.P.lower()
        self.push_dir = "L" if orient == "R" else "R"
        self.pop_dir = "R" if orient == "R" else "L"
        self.arr_sign = "+" if orient == "R" else "-"
        # does the probe state move in the push direction on its non-halt read?
        other = 1 - self.probe_read
        tro = self.tbl[(self.probe, other)]
        self.variant = ("general" if (tro is not None and tro[2] == self.push_dir)
                        else "specialized")
        self.conv = "letter" if self.variant == "specialized" else "generic"
        self.master_file, self.mP, self.mN = MASTERS[(orient, self.variant)]
        # doors: transitions INTO the probe state
        self.doors = [(s, b, self.tbl[(s, b)][1], self.tbl[(s, b)][2])
                      for (s, b), tr in sorted(self.tbl.items())
                      if tr is not None and tr[0] == self.probe]

    # name tokens per convention -------------------------------------------
    @property
    def ProbeSafe(self):
        return f"{self.P}ProbeSafe" if self.conv == "letter" else "ProbeSafe"

    @property
    def SafeSeg(self):
        return f"{self.P}SafeSeg" if self.conv == "letter" else "SafeSeg"

    @property
    def safe_compose(self):
        return f"{self.p}safe_compose" if self.conv == "letter" else "bsafe_compose"

    @property
    def probe_safe_of_segments(self):
        return (f"{self.p}probe_safe_of_segments" if self.conv == "letter"
                else "probe_safe_of_segments")

    @property
    def nonhalting(self):
        return f"nonhalting_of_{self.p}_probe_safe"

    @property
    def blank_nonhalting(self):
        return f"blank_nonhalting_of_{self.p}_probe_safe"

    @property
    def halt_requires_read1(self):
        return f"halt_requires_{self.p}_read_1"


# ---------------------------------------------------- machine-specific gen

def gen_instr(sp):
    out = [f"/-- The dossier-{sp.N} transition table.  `none` is the undefined halt",
           f"transition `{sp.P}{sp.probe_read}`. -/",
           "def instr : State → Bool → Option Instr"]
    for s in STATES:
        for b in (0, 1):
            tr = sp.tbl[(s, b)]
            if tr is None:
                out.append(f"  | State.{s}, {rstr(b)} => none")
            else:
                ns, w, d = tr
                out.append(f"  | State.{s}, {rstr(b)} => "
                           f"some ⟨State.{ns}, {bstr(w)}, Dir.{d}⟩")
    return "\n".join(out) + "\n"


def gen_go(sp):
    out = ["def go : Nat → State → List Bool → List Bool → "
           "Option (State × List Bool × Nat)",
           "  | 0, _, _, _ => none",
           "  | fuel + 1, st, em, rest =>",
           "    match st, rest.getD 0 false with"]
    for s in STATES:
        for b in (0, 1):
            tr = sp.tbl[(s, b)]
            rd = rstr(b)
            if tr is None:
                out.append(f"    | State.{s}, {rd} => none")
                continue
            ns, w, d = tr
            wv = bstr(w)
            if d == sp.push_dir:
                out.append(f"    | State.{s}, {rd} =>")
                out.append(f"        (go fuel State.{ns} ({wv} :: em) (rest.drop 1)).map")
                out.append("          (fun r => (r.1, r.2.1, 1 + r.2.2))")
            else:
                out.append(f"    | State.{s}, {rd} =>")
                out.append("        match em with")
                out.append(f"        | [] => some (State.{ns}, false :: {wv} :: rest.drop 1, 1)")
                out.append("        | e0 :: em2 =>")
                out.append(f"            (go fuel State.{ns} em2 (e0 :: {wv} :: rest.drop 1)).map")
                out.append("              (fun r => (r.1, r.2.1, 1 + r.2.2))")
    return "\n".join(out) + "\n"


def _safe_arg(sp, s):
    return "(fun _ => hr)" if s == sp.probe else "(fun h => absurd h (by decide))"


def gen_go_faithful(sp):
    fresh = ("Faithfulness of the sweep, by induction on fuel: every `some`\n"
             "output of `go` is realized by the raw machine in exactly the returned\n"
             f"step count, {sp.P}-probe-safely, landing on an arrival configuration of\n"
             "the returned word (head at the new base, the fresh "
             f"{'right' if sp.orient == 'R' else 'left'} extreme).")
    out = [f"/-- {fresh} -/",
           "theorem go_faithful :",
           "    ∀ (fuel : Nat) (st : State) (em rest : List Bool) (st' : State)",
           "      (w' : List Bool) (d : Nat),",
           "      go fuel st em rest = some (st', w', d) →",
           "      ∀ (base : Int) (cfg : Config), Inv st base em rest cfg →",
           "        ∃ (cfg' : Config) (base' : Int), stepN d cfg = some cfg' ∧",
           f"          Inv st' base' [] w' cfg' ∧ {sp.SafeSeg} cfg d ∧ 0 < d := by",
           "  intro fuel",
           "  induction fuel with",
           "  | zero =>",
           "      intro st em rest st' w' d hgo base cfg hInv",
           "      simp [go] at hgo",
           "  | succ fuel ih =>",
           "      intro st em rest st' w' d hgo base cfg hInv",
           "      simp only [go] at hgo",
           "      split at hgo"]
    first_pop = True
    for s in STATES:
        for b in (0, 1):
            tr = sp.tbl[(s, b)]
            if tr is None:
                out.append(f"      · -- {s}{b}: the halt probe — fail-closed")
                out.append("        simp at hgo")
                continue
            ns, w, d = tr
            wv = bstr(w)
            sa = _safe_arg(sp, s)
            if d == sp.push_dir:
                out.append(f"      · -- {s}{b}: push to {ns}")
                out.append("        next hr =>")
                out.append("          obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo")
                out.append("          subst hd")
                if sp.variant == "specialized":
                    out.append("          obtain ⟨cfg₂, h1, h2, h3⟩ := "
                               "push_step hInv (by rw [hr]; rfl) (by decide)")
                else:
                    out.append("          obtain ⟨cfg₂, h1, h2, h3⟩ := "
                               "push_step hInv (by rw [hr]; rfl)")
                    out.append(f"            {sa}")
                out.append("          obtain ⟨cfg', base', h1', h2', h3', _⟩ := "
                           "ih _ _ _ _ _ _ hrec base cfg₂ h2")
                out.append("          refine ⟨cfg', base', ?_, h2', ?_, by omega⟩")
                out.append("          · rw [stepN_add, h1]")
                out.append("            exact h1'")
                out.append(f"          · exact {sp.safe_compose} h1 h3 h3'")
            else:
                out.append(f"      · -- {s}{b}: pop to {ns}")
                out.append("        next hr =>")
                out.append("          split at hgo")
                if first_pop and sp.conv == "letter":
                    out.append("          · -- arrival")
                    out.append(f"            obtain ⟨hs, hw, hd⟩ : State.{ns} = st' ∧")
                    first_pop = False
                else:
                    out.append(f"          · obtain ⟨hs, hw, hd⟩ : State.{ns} = st' ∧")
                out.append(f"                false :: {wv} :: rest.drop 1 = w' ∧ 1 = d := by")
                out.append("              simpa using hgo")
                out.append("            subst hs; subst hw; subst hd")
                out.append("            obtain ⟨cfg', h1, h2, h3⟩ := "
                           "pop_step_nil hInv (by rw [hr]; rfl)")
                out.append(f"              {sa}")
                out.append(f"            exact ⟨cfg', base {sp.arr_sign} 1, h1, h2, h3, by omega⟩")
                out.append("          · next e0 em2 =>")
                out.append("              obtain ⟨d', hrec, hd⟩ := map_add1_eq_some hgo")
                out.append("              subst hd")
                out.append("              obtain ⟨cfg₂, h1, h2, h3⟩ := "
                           "pop_step_cons hInv (by rw [hr]; rfl)")
                out.append(f"                {sa}")
                out.append("              obtain ⟨cfg', base', h1', h2', h3', _⟩ := "
                           "ih _ _ _ _ _ _ hrec base cfg₂ h2")
                out.append("              refine ⟨cfg', base', ?_, h2', ?_, by omega⟩")
                out.append("              · rw [stepN_add, h1]")
                out.append("                exact h1'")
                out.append(f"              · exact {sp.safe_compose} h1 h3 h3'")
    return "\n".join(out) + "\n"


def gen_corridor(sp):
    """The corridor lemma `into_{P}...` : the entry funnel into the halt
    state, read off the table.  Documentation (not on the keystone's
    critical path); reproduces the three hand-built shapes."""
    P = sp.P
    hc = f"h{P}" if sp.conv == "letter" else "hP"
    doors = sp.doors
    dirsign = {"R": "+", "L": "-"}

    def door_name(s, b):
        return f"{s}{b}"

    if len(doors) == 1:
        s, b, w, d = doors[0]
        sign = dirsign[d]
        name = f"into_{P}_only_from_{door_name(s, b)}"
        doc = (f"/-- State `{P}` is entered only by `{s}` reading `{b}`.  The\n"
               f"entering write cannot touch the cell `{P}` then reads. -/")
        stmt = [f"theorem {name} {{c c' : Config}} (h : step c = some c')",
                f"    ({hc} : c'.state = State.{P}) :",
                f"    c'.head = c.head {sign} 1 ∧ c.state = State.{s} ∧",
                f"      c.tape c.head = {rstr(b)} ∧ c'.tape = writeAt c.tape c.head {bstr(w)} := by",
                "  cases hs : c.state <;> cases ht : c.tape c.head <;>",
                "    simp [step, instr, hs, ht] at h",
                "  all_goals",
                "    first",
                "      | exact ⟨by rw [← h]; simp [move], rfl, rfl, by rw [← h]⟩",
                f"      | (rw [← h] at {hc}; simp at {hc})"]
        return doc + "\n" + "\n".join(stmt) + "\n"

    same_dir = len({d for _, _, _, d in doors}) == 1
    same_state = len({s for s, _, _, _ in doors}) == 1

    if len(doors) == 2 and same_dir:
        d = doors[0][3]
        sign = dirsign[d]
        (s1, b1, w1, _), (s2, b2, w2, _) = doors
        name = f"into_{P}_only_from_{door_name(s1, b1)}_or_{door_name(s2, b2)}"
        doc = (f"/-- State `{P}` is entered only via `{s1}{b1}` or `{s2}{b2}`, both\n"
               f"moving {'right' if d == 'R' else 'left'} onto the probed cell, which their\n"
               "writes cannot touch. -/")
        stmt = [f"theorem {name} {{c c' : Config}} (h : step c = some c')",
                f"    ({hc} : c'.state = State.{P}) :",
                f"    c'.head = c.head {sign} 1 ∧",
                f"      ((c.state = State.{s1} ∧ c.tape c.head = {rstr(b1)} ∧",
                f"          c'.tape = writeAt c.tape c.head {bstr(w1)}) ∨",
                f"        (c.state = State.{s2} ∧ c.tape c.head = {rstr(b2)} ∧",
                f"          c'.tape = writeAt c.tape c.head {bstr(w2)})) := by",
                "  cases hs : c.state <;> cases ht : c.tape c.head <;>",
                "    simp [step, instr, hs, ht] at h",
                "  all_goals",
                "    first",
                "      | exact ⟨by rw [← h]; simp [move], Or.inl ⟨rfl, rfl, by rw [← h]⟩⟩",
                "      | exact ⟨by rw [← h]; simp [move], Or.inr ⟨rfl, rfl, by rw [← h]⟩⟩",
                f"      | (rw [← h] at {hc}; simp at {hc})"]
        return doc + "\n" + "\n".join(stmt) + "\n"

    if len(doors) == 2 and same_state:
        s = doors[0][0]
        (_, b1, w1, d1), (_, b2, w2, d2) = doors
        name = f"into_{P}_only_from_{s}"
        doc = (f"/-- State `{P}` is entered only from state `{s}`; the fatal cell\n"
               "was already a `1` before the entry step. -/")
        stmt = [f"theorem {name} {{c c' : Config}} (h : step c = some c')",
                f"    ({hc} : c'.state = State.{P}) :",
                f"    c.state = State.{s} ∧",
                f"      ((c.tape c.head = {rstr(b1)} ∧ c'.head = c.head {dirsign[d1]} 1 ∧",
                f"          c'.tape = writeAt c.tape c.head {bstr(w1)}) ∨",
                f"        (c.tape c.head = {rstr(b2)} ∧ c'.head = c.head {dirsign[d2]} 1 ∧",
                f"          c'.tape = writeAt c.tape c.head {bstr(w2)})) := by",
                "  cases hs : c.state <;> cases ht : c.tape c.head <;>",
                "    simp [step, instr, hs, ht] at h",
                "  all_goals",
                "    first",
                "      | exact ⟨rfl, Or.inl ⟨rfl, by rw [← h]; simp [move], by rw [← h]⟩⟩",
                "      | exact ⟨rfl, Or.inr ⟨rfl, by rw [← h]; simp [move], by rw [← h]⟩⟩",
                f"      | (rw [← h] at {hc}; simp at {hc})"]
        return doc + "\n" + "\n".join(stmt) + "\n"

    # Exotic door structure (>2 doors, or 2 doors that neither share a
    # direction nor a source state).  The corridor lemma is documentation
    # only (never on the keystone's critical path), but rather than emit an
    # unvalidated shape we fail loudly so the operator can hand-author it.
    raise NotImplementedError(
        f"corridor lemma shape not supported for doors={doors}; the closure "
        "keystone does not need it — remove the into_* region or hand-author "
        "the corridor for this door structure")


def gen_entry_probe(sp):
    """halt_requires_entry_probe : corridor form of halt localization.
    Generated only for the letter convention with >=2 same-direction doors
    (the d9/d13 shape)."""
    doors = sp.doors
    if not (sp.conv == "letter" and len(doors) == 2
            and len({d for _, _, _, d in doors}) == 1):
        return None
    P = sp.P
    d = doors[0][3]
    sign = "+" if d == "R" else "-"
    side = "right" if d == "R" else "left"
    corridor_name = f"into_{P}_only_from_{doors[0][0]}{doors[0][1]}_or_{doors[1][0]}{doors[1][1]}"
    (s1, b1, w1, _), (s2, b2, w2, _) = doors

    def hn(s):
        return "hFe" if f"h{s}" == "hF" else f"h{s}"

    h1, h2 = hn(s1), hn(s2)
    doc = (f"/-- Halt localization, corridor form: from any non-`{P}` start, a raw\n"
           f"halt forces a reachable `{s1}{b1}` or `{s2}{b2}` configuration whose\n"
           f"*{side}* neighbour is a `1` — the cell the machine will die on. -/")
    out = [doc,
           f"theorem halt_requires_entry_probe {{c : Config}} (hne : c.state ≠ State.{P})",
           "    (hh : RawHalts c) :",
           f"    ∃ d : Config, Reaches c d ∧ d.tape (d.head {sign} 1) = true ∧",
           f"      ((d.state = State.{s1} ∧ d.tape d.head = {rstr(b1)}) ∨",
           f"        (d.state = State.{s2} ∧ d.tape d.head = {rstr(b2)})) := by",
           "  obtain ⟨n, hn⟩ := hh",
           "  obtain ⟨k, _, d0, hd0, hstop⟩ := stepN_none_last n c hn",
           "  have hF := (step_eq_none_iff d0).mp hstop",
           "  cases k with",
           "  | zero =>",
           "      have hcd : c = d0 := by simpa [stepN] using hd0",
           "      exact absurd (hcd ▸ hF.1) hne",
           "  | succ k' =>",
           "      obtain ⟨e, he, hstepe⟩ := stepN_some_pred k' c d0 hd0",
           f"      obtain ⟨hhead, hcase⟩ := {corridor_name} hstepe hF.1",
           "      have hread : d0.tape d0.head = true := hF.2",
           "      cases hcase with",
           f"      | inl {h1} =>",
           f"          obtain ⟨hst, hrd, htape⟩ := {h1}",
           "          refine ⟨e, ⟨k', he⟩, ?_, Or.inl ⟨hst, hrd⟩⟩",
           "          rw [htape, hhead] at hread",
           f"          rwa [writeAt_other e.tape e.head (e.head {sign} 1) {bstr(w1)} (by omega)] at hread",
           f"      | inr {h2} =>",
           f"          obtain ⟨hst, hrd, htape⟩ := {h2}",
           "          refine ⟨e, ⟨k', he⟩, ?_, Or.inr ⟨hst, hrd⟩⟩",
           "          rw [htape, hhead] at hread",
           f"          rwa [writeAt_other e.tape e.head (e.head {sign} 1) {bstr(w2)} (by omega)] at hread"]
    return "\n".join(out) + "\n"


# --------------------------------------------------------- python mirror

# ------------------------------------------------------- assembly / retarget

def retarget(text, sp):
    """Retarget the master boilerplate from master probe/N to this machine's
    probe/N.  For regeneration (P==mP, N==mN) every rule is a no-op, so the
    boilerplate is byte-identical to the committed template."""
    mP, mN, P, N = sp.mP, sp.mN, sp.P, sp.N
    mp, p = mP.lower(), P.lower()

    def w(tok):
        return r"\b" + re.escape(tok) + r"\b"

    subs = []
    # dossier number in module identifiers
    subs.append((f"Dossier{mN}RawTM", f"Dossier{N}RawTM"))
    subs.append((f"SafeD{mN}Orbit", f"SafeD{N}Orbit"))
    subs.append((f"safeD{mN}Orbit_nonhalting", f"safeD{N}Orbit_nonhalting"))
    # theorem names carrying the probe letter (both conventions)
    subs.append((f"nonhalting_of_{mp}_probe_safe", f"nonhalting_of_{p}_probe_safe"))
    subs.append((f"blank_nonhalting_of_{mp}_probe_safe", f"blank_nonhalting_of_{p}_probe_safe"))
    subs.append((f"halt_requires_{mp}_read_1", f"halt_requires_{p}_read_1"))
    for a, b in subs:
        text = text.replace(a, b)
    # State.<probe> and letter-convention names / locals: word-boundary
    wb = []
    wb.append((f"State.{mP}", f"State.{P}"))
    if sp.conv == "letter":
        wb.append((f"{mP}ProbeSafe", f"{P}ProbeSafe"))
        wb.append((f"{mP}SafeSeg", f"{P}SafeSeg"))
        wb.append((f"{mp}safe_compose", f"{p}safe_compose"))
        wb.append((f"{mp}probe_safe_of_segments", f"{p}probe_safe_of_segments"))
        wb.append((f"hn{mP}", f"hn{P}"))
        wb.append((f"h{mP}", f"h{P}"))
    for a, b in wb:
        text = re.sub(w(a), b, text)
    # best-effort prose retarget (comments only; imperfect is acceptable)
    if mP != P:
        for pat, rep in [(f"`{mP}`", f"`{P}`"),
                         (f"{mP}-probe", f"{P}-probe"),
                         (f"state `{mP}`", f"state `{P}`")]:
            text = text.replace(pat, rep)
    return text


def replace_region(text, start, end, repl):
    i = text.index(start)
    j = text.index(end, i)
    return text[:i] + repl + text[j:]


def gen_header(sp):
    grow = "right" if sp.orient == "R" else "left"
    out = ["import Lean.Elab.Tactic.Omega",
           "",
           "set_option maxRecDepth 100000",
           "",
           "/-!",
           f"# Dossier-{sp.N} machine: raw semantics and conditional closure",
           "",
           "Bare-Lean model of the concrete BB(6) machine",
           "",
           f"`{sp.code}`",
           "",
           f"(dossier-{sp.N}: generated by qgkit/bb6/rawstep_generator.py from the",
           f"phase-2.1 raw-step template corpus.  Grows *{grow}* (records at fresh",
           f"{grow} extremes); the undefined transition is `{sp.P}{sp.probe_read}`, the halt",
           f"happens in state `{sp.P}` on the probed cell itself, so the probe-safety",
           f"predicate is simply \"state `{sp.P}` never reads a `1`\".)",
           "",
           "The certified layer is a single-raw-step word engine over the",
           "machine's record events: every raw move is a certified push or pop of",
           "list surgery on the two-list boundary `(em, rest)`, the executable",
           "sweep `go`/`wstep` is proven faithful (every `some` output realized by",
           "the raw machine in exactly the returned step count, probe-safely), and",
           "a segment-induction keystone discharges orbit safety into non-halting.",
           "",
           "Checked statements (no sorry, no extra axioms):",
           "",
           "* `step_eq_none_iff` — the machine halts in one step exactly at the",
           f"  unique undefined transition `{sp.P}{sp.probe_read}`.",
           "* `push_step` / `pop_step_cons` / `pop_step_nil` — the three one-step",
           "  episode lemmas.",
           "* `go_faithful` / `wstep_faithful` — the certified record-to-record",
           "  sweep is fail-closed and faithful.",
           f"* the word orbit `worbit` and the keystone `safeD{sp.N}Orbit_nonhalting`:",
           f"  `SafeD{sp.N}Orbit → ¬ RawHalts blankStart`.",
           "",
           f"`SafeD{sp.N}Orbit` is the single conjecture `∀ k, worbit k ≠ none`: the",
           "fail-closed record orbit never dies.  No `Faithful` assumption remains.",
           "-/"]
    return "\n".join(out) + "\n\n"


def gen_worbit_comment(sp):
    grow = "right" if sp.orient == "R" else "left"
    out = ["/-!",
           "## The word orbit and the keystone",
           "",
           f"The blank start realizes the virtual arrival `(A, [])` (head at its own",
           f"{grow} extreme over the empty word), so the orbit needs no raw startup",
           "prefix.  The word orbit is `wstep` iterated; the conjecture is the",
           "single clause that it never dies.",
           "-/"]
    return "\n".join(out) + "\n\n"


def build_lean(sp):
    master = open(os.path.join(CORE, sp.master_file), encoding="utf-8").read()
    t = retarget(master, sp)

    # 1. header
    ns_anchor = f"namespace QIG.Dossier{sp.N}RawTM"
    t = gen_header(sp) + t[t.index(ns_anchor):]

    # 2. instr
    t = replace_region(t, f"/-- The dossier-{sp.mN} transition table",
                        "def move : Int → Dir → Int",
                        gen_instr(sp) + "\n")

    # 3. corridor lemma
    t = replace_region(t, f"/-- State `{sp.P}` is entered only",
                        "/-- Any finite run ending in a halt contains",
                        gen_corridor(sp) + "\n")

    # 4. entry-probe (letter conv, 2 same-dir doors) or drop
    if sp.conv == "letter":
        ep = gen_entry_probe(sp)
        # region between read_1 proof and the ProbeSafe docstring
        pd_anchor = f"/-- The {sp.P}-probe-safety invariant"
        if ep is not None:
            t = replace_region(t, "/-- Halt localization, corridor form", pd_anchor,
                                ep + "\n")
        else:
            # remove the master's entry_probe entirely
            t = replace_region(t, "/-- Halt localization, corridor form", pd_anchor, "")

    # 5. go
    t = replace_region(t, "def go : Nat → State → List Bool → List Bool",
                        "theorem map_add1_eq_some", gen_go(sp) + "\n")

    # 6. go_faithful (replace its docstring too, to avoid a double doc-comment)
    t = replace_region(t, "/-- Faithfulness of the sweep", "/-- Generous fuel:",
                        gen_go_faithful(sp) + "\n")

    # 7. worbit comment (prose)
    t = replace_region(t, "/-!\n## The word orbit and the keystone",
                        "/-- The word orbit: `wstep` iterated",
                        gen_worbit_comment(sp))
    return t


# =====================================================================
# python mirror + differential test
# =====================================================================

def _orient_py(sp):
    """Orientation-specific python fragments (realize / run_raw / push dir)."""
    P = sp.P
    if sp.orient == "R":
        push_dir = "L"
        realize = (
            "def realize(st, em, rest, base):\n"
            '    """Raw config realizing Inv st base em rest (right-grower:\n'
            '    head at base - len(em), em above the head, rest downward)."""\n'
            "    tape = {}\n"
            "    for k, v in enumerate(em):\n"
            "        tape[base - len(em) + 1 + k] = v\n"
            "    for j, v in enumerate(rest):\n"
            "        tape[base - len(em) - j] = v\n"
            "    return st, base - len(em), tape\n")
        record = (
            "        if hd > hi:\n"
            "            hi = hd\n"
            "            recs.append((t, st,\n"
            "                         tuple(tape.get(x, 0) for x in range(hd, lo - 1, -1))))\n"
            "        elif hd < lo:\n"
            "            lo = hd\n")
        side = "right"
    else:
        push_dir = "R"
        realize = (
            "def realize(st, em, rest, base):\n"
            '    """Raw config realizing Inv st base em rest (left-grower:\n'
            '    head at base + len(em), em below the head, rest upward)."""\n'
            "    tape = {}\n"
            "    for k, v in enumerate(em):\n"
            "        tape[base + len(em) - 1 - k] = v\n"
            "    for j, v in enumerate(rest):\n"
            "        tape[base + len(em) + j] = v\n"
            "    return st, base + len(em), tape\n")
        record = (
            "        if hd < lo:\n"
            "            lo = hd\n"
            "            recs.append((t, st,\n"
            "                         tuple(tape.get(x, 0) for x in range(hd, hi + 1))))\n"
            "        elif hd > hi:\n"
            "            hi = hd\n")
        side = "left"
    return push_dir, realize, record, side


def run_differential(sp, horizon):
    """In-memory differential (same surgery as the Lean `go`): run the raw
    machine and the fail-closed word orbit, assert exact agreement on every
    record, probe safety, and no fuel exhaustion.  Returns (nrecords,
    max_frac).  Raises AssertionError / returns None-signal on any failure."""
    # mirror tuple order is (write, dir, next); sp.tbl is (next, write, dir)
    tbl = {(s, b): (None if sp.tbl[(s, b)] is None
                    else (1 if sp.tbl[(s, b)][1] else 0, sp.tbl[(s, b)][2], sp.tbl[(s, b)][0]))
           for s in STATES for b in (0, 1)}
    push_dir = "L" if sp.orient == "R" else "R"
    P, safe = sp.P, 1 - sp.probe_read

    def micro(st, em, rest):
        r = rest[0] if rest else 0
        tr = tbl[(st, r)]
        if tr is None:
            return None
        wv, d, ns = tr
        if rest:
            rest.popleft()
        if d == push_dir:
            em.appendleft(wv)
            return ("cont", ns)
        if em:
            rest.appendleft(wv)
            rest.appendleft(em.popleft())
            return ("cont", ns)
        rest.appendleft(wv)
        rest.appendleft(0)
        return ("arrival", ns, list(rest))

    def wfuel(w):
        return 64 * (len(w) + 64) * (len(w) + 64)

    def wstep(st, w):
        fuel = wfuel(w)
        em, rest = deque(), deque(w)
        dt = 0
        while fuel > 0:
            fuel -= 1
            out = micro(st, em, rest)
            if out is None:
                return None
            dt += 1
            if out[0] == "arrival":
                return (out[1], tuple(out[2]), dt, dt / wfuel(w))
            st = out[1]
        return None

    tape = {}
    st, hd = "A", 0
    lo = hi = 0
    recs = [(0, "A", ())]
    for t in range(horizon):
        b = tape.get(hd, 0)
        if sp.orient == "R":
            if hd > hi:
                hi = hd
                recs.append((t, st, tuple(tape.get(x, 0) for x in range(hd, lo - 1, -1))))
            elif hd < lo:
                lo = hd
        else:
            if hd < lo:
                lo = hd
                recs.append((t, st, tuple(tape.get(x, 0) for x in range(hd, hi + 1))))
            elif hd > hi:
                hi = hd
        if st == P:
            assert b == safe, f"probe unsafe t={t}"
        tr = tbl[(st, b)]
        assert tr is not None, f"raw halt t={t}"
        wv, d, ns = tr
        tape[hd] = wv
        hd += 1 if d == "R" else -1
        st = ns

    def eqw(u, v):
        n = max(len(u), len(v))
        return all((u[i] if i < len(u) else 0) == (v[i] if i < len(v) else 0)
                   for i in range(n))

    st, w = "A", ()
    t = 0
    max_frac = 0.0
    for i in range(1, len(recs)):
        out = wstep(st, w)
        assert out is not None, f"orbit died at {i}"
        st, w, dt, frac = out
        max_frac = max(max_frac, frac)
        t += dt
        rt, rs, rw = recs[i]
        assert t == rt and st == rs and eqw(w, rw), f"mismatch at {i}"
    assert max_frac < 1.0
    return len(recs) - 1, max_frac


def build_mirror(sp):
    push_dir, realize, record, side = _orient_py(sp)
    P, pr = sp.P, sp.probe_read
    return f'''#!/usr/bin/env python3
"""dossier-{sp.N} record-orbit mirror (differential validation).

Literal transcription of the Lean `go` / `wstep` sweep for the machine
`{sp.code}` (grows {side}; the fatal probe is the undefined transition
`{P}{pr}`).  `main()` runs the raw machine and the fail-closed word orbit
side by side over a 20M-step horizon and asserts they agree exactly on
every record (state, word up to trailing zeros, cumulative step count),
that state `{P}` never reads a `1`, and that the quadratic fuel is never
exhausted."""
from collections import deque

TM_CODE = '{sp.code}'
ANCHOR = ('A', ())
PROBE = '{P}'
PUSH_DIR = '{push_dir}'


def parse_tm(code):
    tbl = {{}}
    for si, block in enumerate(code.split('_')):
        for b in range(2):
            tr = block[3 * b:3 * b + 3]
            tbl[('ABCDEF'[si], b)] = None if tr == '---' else \\
                (int(tr[0]), tr[1], tr[2])
    return tbl


TBL = parse_tm(TM_CODE)


def micro(st, em, rest):
    """One Lean `go` micro-step; em/rest are deques (mutated).  Returns
    ('cont', st'), ('arrival', st', word-list), or None (halt probe)."""
    r = rest[0] if rest else 0
    tr = TBL[(st, r)]
    if tr is None:
        return None
    wv, d, ns = tr
    if rest:
        rest.popleft()
    if d == PUSH_DIR:
        em.appendleft(wv)
        return ('cont', ns)
    if em:
        rest.appendleft(wv)
        rest.appendleft(em.popleft())
        return ('cont', ns)
    rest.appendleft(wv)
    rest.appendleft(0)
    return ('arrival', ns, list(rest))


def wfuel(w):
    return 64 * (len(w) + 64) * (len(w) + 64)


def wstep(st, w):
    fuel = wfuel(w)
    em, rest = deque(), deque(w)
    dt = 0
    while fuel > 0:
        fuel -= 1
        out = micro(st, em, rest)
        if out is None:
            return None
        dt += 1
        if out[0] == 'arrival':
            return (out[1], tuple(out[2]), dt, dt / wfuel(w))
        st = out[1]
    return None


def record_orbit(n):
    """`worbit` iterated: the fail-closed record orbit, n records."""
    st, w = ANCHOR
    orbit = [(st, w)]
    for _ in range(n):
        out = wstep(st, w)
        if out is None:
            return orbit, False
        st, w = out[0], out[1]
        orbit.append((st, w))
    return orbit, True


{realize}

def raw_step(st, hd, tape):
    tr = TBL[(st, tape.get(hd, 0))]
    if tr is None:
        return None
    wv, d, ns = tr
    tape[hd] = wv
    return ns, hd + (1 if d == 'R' else -1), tape


def eqw(u, v):
    n = max(len(u), len(v))
    return all((u[i] if i < len(u) else 0) == (v[i] if i < len(v) else 0)
               for i in range(n))


def run_raw(steps):
    """Raw run: records at fresh {side} extremes, probe-safe at every step."""
    tape = {{}}
    st, hd = 'A', 0
    lo = hi = 0
    recs = [(0, 'A', ())]
    for t in range(steps):
        b = tape.get(hd, 0)
{record}        if st == PROBE:
            assert b == {1 - pr}, f'{P}-probe unsafe at t={{t}}'
        tr = TBL[(st, b)]
        assert tr is not None, f'raw halt at t={{t}}'
        wv, d, ns = tr
        tape[hd] = wv
        hd += 1 if d == 'R' else -1
        st = ns
    return recs


def differential(horizon):
    recs = run_raw(horizon)
    st, w = ANCHOR
    t = 0
    max_frac = 0.0
    for i in range(1, len(recs)):
        out = wstep(st, w)
        assert out is not None, f'orbit died at index {{i}}'
        st, w, dt, frac = out
        max_frac = max(max_frac, frac)
        t += dt
        rt, rs, rw = recs[i]
        assert t == rt, f'step count mismatch at record {{i}}: {{t}} != {{rt}}'
        assert st == rs, f'state mismatch at record {{i}}: {{st}} != {{rs}}'
        assert eqw(w, rw), f'word mismatch at record {{i}}'
    assert max_frac < 1.0
    return len(recs) - 1, max_frac


def main():
    horizon = 20_000_000
    n, max_frac = differential(horizon)
    print(f'dossier-{sp.N}: {{n}} record transitions exact over {{horizon}} raw '
          f'steps; max fuel fraction {{max_frac:.6f}}')


if __name__ == '__main__':
    main()
'''


def build_test(sp):
    """Differential pytest in the established convention (episode plants +
    record mirror + probe safety).  Built by retargeting the committed
    right-/left-grower template test."""
    tmpl_N = "9" if sp.orient == "R" else "13"
    tmpl_P = "B" if sp.orient == "R" else "D"
    path = os.path.join(REPO, "tests", "bb6", f"test_d{tmpl_N}_theorems.py")
    text = open(path, encoding="utf-8").read()
    P, pr, N = sp.P, sp.probe_read, sp.N
    # functional retargets
    text = re.sub(r"TM_CODE = '[^']*'", f"TM_CODE = '{sp.code}'", text)
    text = re.sub(r"random\.Random\(0x[0-9a-fA-F]+\)", f"random.Random(0x{N})", text)
    text = text.replace(f"st == '{tmpl_P}' and r == 1",
                        f"st == '{P}' and r == {pr}")
    text = text.replace(f"if st == '{tmpl_P}':", f"if st == '{P}':")
    # probe-safety assertion checks the SAFE read value (1 - fatal read)
    text = text.replace("assert b == 0, f'", f"assert b == {1 - pr}, f'")
    text = text.replace(f"'{tmpl_P}-probe", f"'{P}-probe")
    # labels + prose
    text = re.sub(rf"\bd{tmpl_N}\b", f"d{N}", text)
    text = text.replace(f"dossier-{tmpl_N}", f"dossier-{N}")
    text = text.replace(f"Dossier{tmpl_N}RawTM", f"Dossier{N}RawTM")
    text = text.replace(f"{tmpl_P}1", f"{P}{pr}")
    text = text.replace(f"{tmpl_P}Probe", f"{P}Probe")
    text = text.replace(f"{tmpl_P}-probe", f"{P}-probe")
    return text


# =====================================================================
# Palomar quadruple: Challenge / Solution / comparator / meta
# =====================================================================

def _splice_instr_go(sp, text):
    # called after retarget: the instr docstring already reads dossier-{sp.N}
    text = replace_region(text, f"/-- The dossier-{sp.N} transition table",
                          "def move : Int → Dir → Int", gen_instr(sp) + "\n")
    text = replace_region(text, "def go : Nat → State → List Bool → List Bool",
                          "/-- Generous fuel:", gen_go(sp) + "\n")
    return text


def retarget_palomar(text, sp, mN):
    # ONLY module/dossier-number identifiers.  The probe letter must NOT be
    # retargeted here: the Challenge/Solution boilerplate (stMap, stInv,
    # step_map, ...) enumerates all six states verbatim as an identity
    # renaming; the only machine-specific State references live in `instr`
    # and `go`, which are freshly spliced.
    for a, b in [(f"Dossier{mN}Challenge", f"Dossier{sp.N}Challenge"),
                 (f"Dossier{mN}RawTM", f"Dossier{sp.N}RawTM"),
                 (f"SafeD{mN}Orbit", f"SafeD{sp.N}Orbit"),
                 (f"safeD{mN}Orbit_nonhalting", f"safeD{sp.N}Orbit_nonhalting"),
                 (f"dossier-{mN}", f"dossier-{sp.N}"),
                 (f"dossier {mN}", f"dossier {sp.N}")]:
        text = text.replace(a, b)
    return text


def build_challenge(sp):
    mN = "9" if sp.orient == "R" else "13"
    text = open(os.path.join(REPO, "packages", "dossier1", "Palomar",
                             f"Dossier{mN}Challenge.lean"), encoding="utf-8").read()
    text = retarget_palomar(text, sp, mN)
    text = _splice_instr_go(sp, text)
    return text


def build_solution(sp):
    mN = "9" if sp.orient == "R" else "13"
    text = open(os.path.join(REPO, "packages", "dossier1", "Palomar",
                             f"Dossier{mN}Solution.lean"), encoding="utf-8").read()
    text = retarget_palomar(text, sp, mN)
    text = _splice_instr_go(sp, text)
    return text


def build_comparator(sp):
    import json
    obj = {
        "challenge_module": f"Palomar.Dossier{sp.N}Challenge",
        "solution_module": f"Palomar.Dossier{sp.N}Solution",
        "theorem_names": [f"Dossier{sp.N}Challenge.safeD{sp.N}Orbit_nonhalting"],
        "permitted_axioms": ["propext", "Quot.sound"],
    }
    return json.dumps(obj, indent=4) + "\n"


def build_meta(sp):
    grow = "right" if sp.orient == "R" else "left"
    return f'''version: v0.4

project:
  name: "Dossier-{sp.N} non-halting, reduced to its record-orbit conjecture"
  description: >-
    A machine-checked reduction, in core Lean 4 (no Mathlib), of the halting
    problem of the BB(6) holdout Turing machine dossier-{sp.N}
    ({sp.code}) to the conjecture that its fail-closed record orbit never
    dies (SafeD{sp.N}Orbit).  The certified layer is a single-raw-step word
    engine over the machine's record events (fresh {grow} extremes): every raw
    move is a certified push or pop of list surgery on a two-list boundary
    representation, the executable sweep (go/wstep) is proven faithful, failing
    closed only on the machine's fatal halt probe ({sp.P} reading 1, the
    undefined transition itself) and on fuel exhaustion, and a
    segment-induction keystone discharges orbit safety into non-halting
    (theorem safeD{sp.N}Orbit_nonhalting).  No Faithful assumption remains.
    The word calculus was validated against a python record mirror over a 20M
    raw-step horizon.  Nothing here decides the machine: the orbit conjecture
    itself remains open.  Generated by qgkit/bb6/rawstep_generator.py.
  authors:
    - "Enan Srivastava"
  responsible_maintainers:
    - "Enan Srivastava <enan332@gmail.com>"
  license: "MIT"

classification:
  arxiv: [math.LO, cs.CC]
  msc2020: ["03D10"]

sources:
  - title: "The Busy Beaver Challenge (bbchallenge) BB(6) project"
    type: web discussion
    url: "https://bbchallenge.org"
    relationship: formalizes
    note: >-
      The machine {sp.code} is one of the bbchallenge BB(6) holdout set;
      this development formalises its record-level dynamics and reduces its
      halting problem to the SafeD{sp.N}Orbit conjecture.
  - title: "bbchallenge deciders paper (Turing machine deciders, part I)"
    type: preprint
    url: "https://arxiv.org/abs/2504.20563"
    relationship: background

automation:
  methods:
    - method: agent
      note: >-
        Closure emitted push-button by the phase-2.1 raw-step Lean generator
        (qgkit/bb6/rawstep_generator.py) from the hand-built template corpus;
        the record calculus validated fail-closed by the project's Python
        pipeline against a 20M raw horizon; all proofs machine-checked by Lean.

review:
  status: self-assessed
  notes: >-
    No external human review.  Self-assessment: axiom audit (theorem uses only
    propext and Quot.sound), differential testing of the word engine against
    independent raw emulation (permanent pytest), and exact record-mirror
    validation of the executable sweep.

claims:
  - theorem: "Dossier{sp.N}Challenge.safeD{sp.N}Orbit_nonhalting"
    statement_informal: >-
      If the fail-closed record orbit of dossier-{sp.N} never dies
      (SafeD{sp.N}Orbit), then the machine {sp.code} never halts from the
      all-zero tape.
    status: "conditional"
    axioms: ["propext", "Quot.sound"]

provenance:
  relationship: "original"
  notes: >-
    Original development; the machine is one of the bbchallenge BB(6) holdouts.
    Proofs generated with an AI assistant (Claude, Anthropic); all results are
    checked by the Lean 4 kernel at the stated axiom set.
'''


def emit_all(sp, dirs):
    """Write all seven artifacts.  `dirs` maps artifact kind -> directory."""
    written = []

    def w(path, content):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        open(path, "w", encoding="utf-8").write(content)
        written.append(path)

    w(os.path.join(dirs["core"], f"Dossier{sp.N}RawTM.lean"), build_lean(sp))
    w(os.path.join(dirs["qgkit"], f"dossier{sp.N}_mirror.py"), build_mirror(sp))
    w(os.path.join(dirs["tests"], f"test_d{sp.N}_theorems.py"), build_test(sp))
    w(os.path.join(dirs["palomar"], f"Dossier{sp.N}Challenge.lean"), build_challenge(sp))
    w(os.path.join(dirs["palomar"], f"Dossier{sp.N}Solution.lean"), build_solution(sp))
    w(os.path.join(dirs["comparator"], f"comparator-dossier{sp.N}.json"), build_comparator(sp))
    w(os.path.join(dirs["meta"], f"dossier{sp.N}", "formalization.yaml"), build_meta(sp))
    return written


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--code", required=True)
    ap.add_argument("--orient", required=True, choices=["R", "L"])
    ap.add_argument("--N", required=True)
    ap.add_argument("--out", default="-")
    a = ap.parse_args()
    sp = Spec(a.code, a.orient, a.N)
    text = build_lean(sp)
    if a.out == "-":
        print(text)
    else:
        open(a.out, "w", encoding="utf-8").write(text)
        print(f"wrote {a.out}  (probe={sp.P}{sp.probe_read} orient={sp.orient} "
              f"variant={sp.variant} conv={sp.conv} master={sp.master_file} "
              f"doors={sp.doors})")

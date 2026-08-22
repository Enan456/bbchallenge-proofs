// Deck 2 — "Antihydra: from raw tape to one conjecture" (technical deep dive).
// Committed dark theme: midnight 21295C bg, teal 1C7293, mint 02C39A accent.
const pptxgen = require("pptxgenjs");
const pres = new pptxgen();
pres.layout = "LAYOUT_WIDE";

const BG = "21295C", PANEL = "2A3570", TEAL = "1C7293", MINT = "02C39A";
const WHITE = "FFFFFF", SOFT = "AFC3E8", GOLD = "F9E795";
const HEAD = "Cambria", BODY = "Calibri", MONO = "Courier New";

function bg(s) { s.background = { color: BG }; }
function panel(s, x, y, w, h, fill) {
  s.addShape(pres.ShapeType.roundRect, { x, y, w, h, rectRadius: 0.08, fill: { color: fill || PANEL } });
}
function disc(s, x, y, d, label, fill, txtColor) {
  s.addShape(pres.ShapeType.ellipse, { x, y, w: d, h: d, fill: { color: fill } });
  s.addText(label, { x, y, w: d, h: d, align: "center", valign: "middle",
    fontFace: HEAD, fontSize: 15, bold: true, color: txtColor, margin: 0 });
}
function title(s, t) {
  s.addText(t, { x: 0.7, y: 0.4, w: 12, h: 0.8, fontFace: HEAD, fontSize: 34, bold: true, color: WHITE });
}

// ---------- 1. Title
let s = pres.addSlide(); bg(s);
s.addText("Antihydra", { x: 0.9, y: 1.9, w: 11, h: 1.1, fontFace: HEAD, fontSize: 56, bold: true, color: WHITE });
s.addText("From raw tape to one conjecture — a technical walkthrough", { x: 0.92, y: 3.1, w: 10.5, h: 0.6, fontFace: BODY, fontSize: 20, color: SOFT });
s.addText("1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA", { x: 0.92, y: 3.85, w: 9, h: 0.4, fontFace: MONO, fontSize: 14, color: MINT });
s.addText("Core Lean 4 · no Mathlib · axioms [propext, Quot.sound] · no sorry", { x: 0.92, y: 6.6, w: 9, h: 0.4, fontFace: BODY, fontSize: 13, color: SOFT });
disc(s, 11.6, 5.9, 1.0, "AH", MINT, BG);
s.addNotes("Technical audience deck: the full reduction pipeline for Antihydra, plus the trust machinery, plus Palomar packaging.");

// ---------- 2. The machine
s = pres.addSlide(); bg(s);
title(s, "The machine");
const rowsT = [
  ["", "read 0", "read 1"],
  ["A", "1RB", "1RA"], ["B", "0LC", "1LE"], ["C", "1LD", "1LC"],
  ["D", "1LA", "0LB"], ["E", "1LF", "1RE"], ["F", "— halt —", "0RA"],
];
const tableRows = rowsT.map((r, i) => r.map((c, j) => ({
  text: c, options: {
    fontFace: j === 0 || i === 0 ? BODY : MONO, fontSize: 14, bold: i === 0 || j === 0,
    color: c === "— halt —" ? GOLD : WHITE, align: "center", valign: "middle",
    fill: { color: i === 0 ? TEAL : PANEL },
  },
})));
s.addTable(tableRows, { x: 0.7, y: 1.5, w: 5.4, h: 4.6, border: { type: "solid", color: BG, pt: 1.5 } });
s.addText([
  { text: "Six states, two symbols, one undefined transition: F reading 0 is the only way to halt", options: { bullet: true, breakLine: true } },
  { text: "Tape = total function ℤ → Bool; a configuration is (state, head, tape)", options: { bullet: true, breakLine: true } },
  { text: "The table is hand-transcribed once — then kernel-proved equal to the parsed standard-format code (parse_ok, with corrupted-code negative controls)", options: { bullet: true } },
], { x: 6.6, y: 1.7, w: 6.0, h: 3.6, fontFace: BODY, fontSize: 15, color: SOFT, paraSpaceAfter: 12 });
s.addNotes("Point at F0: the unique halting transition. Everything downstream localizes halting to reaching this cell pattern.");

// ---------- 3. Halt localization
s = pres.addSlide(); bg(s);
title(s, "Halt localization");
const chain3 = [
  ["step = none", "⇔  state F reads 0", "step_eq_none_iff"],
  ["F entered only via E0", "write 1, move left", "into_F_only_from_E0"],
  ["any halt ⇒ E-probe of 00", "a reachable E reading 0 with 0 to its left", "halt_requires_e_probe_00"],
  ["probe-safety ⇒ never halts", "every probed 0 has a 1 on its left", "nonhalting_of_e_probe_safe"],
];
chain3.forEach((c, i) => {
  const y = 1.45 + i * 1.35;
  disc(s, 0.8, y + 0.25, 0.62, String(i + 1), MINT, BG);
  panel(s, 1.7, y, 10.9, 1.15);
  s.addText(c[0], { x: 2.0, y: y + 0.12, w: 4.6, h: 0.5, fontFace: HEAD, fontSize: 17, bold: true, color: WHITE, margin: 0 });
  s.addText(c[1], { x: 2.0, y: y + 0.62, w: 4.9, h: 0.45, fontFace: BODY, fontSize: 12.5, color: SOFT, margin: 0 });
  s.addText(c[2], { x: 7.1, y: y + 0.32, w: 5.2, h: 0.5, fontFace: MONO, fontSize: 13, color: MINT, margin: 0 });
});
s.addNotes("The probe-safety contract is the interface between the elementary layer and the dynamics: discharge the invariant and the machine can never halt.");

// ---------- 4. The three rules
s = pres.addSlide(); bg(s);
title(s, "Three rules, exact for all block values");
const rules4 = [
  ["HYDRA   m ≥ 3", "(a, m, c) → (a, m−2, c+3)", "2c + 11 raw steps", "counter frozen — ~96% of all dynamics"],
  ["DROP   m = 2", "(a, 2, c) → (a−1, c+3, 2)", "2c + 15 raw steps", "counter pays 1 — dies if a ≤ 1"],
  ["MERGE   m = 1", "(a, 1, c) → (a+2, c+2, 2)", "2a + 2c + 22 raw steps", "counter gains 2"],
];
rules4.forEach((r, i) => {
  const x = 0.7 + i * 4.1;
  panel(s, x, 1.6, 3.8, 3.4);
  s.addText(r[0], { x: x + 0.25, y: 1.85, w: 3.3, h: 0.5, fontFace: HEAD, fontSize: 17, bold: true, color: i === 1 ? GOLD : MINT, margin: 0 });
  s.addText(r[1], { x: x + 0.25, y: 2.5, w: 3.3, h: 0.5, fontFace: MONO, fontSize: 14, bold: true, color: WHITE, margin: 0 });
  s.addText(r[2], { x: x + 0.25, y: 3.15, w: 3.3, h: 0.45, fontFace: MONO, fontSize: 13, color: SOFT, margin: 0 });
  s.addText(r[3], { x: x + 0.25, y: 3.75, w: 3.3, h: 1.0, fontFace: BODY, fontSize: 12.5, color: SOFT, margin: 0 });
});
panel(s, 0.7, 5.4, 11.9, 1.35, "1B2350");
s.addText("Each rule is a theorem: the exact raw trajectory plus an ESafeSeg certificate — every E-probe of a 0 during the rule provably has a 1 to its left.  The proofs enumerate the probes one by one.",
  { x: 1.0, y: 5.55, w: 11.3, h: 1.1, fontFace: BODY, fontSize: 14.5, color: WHITE, margin: 0 });
s.addNotes("hydra_step, drop_step, merge_chain: trajectory + safety, for all block values, via three sweep lemmas over runs of ones.");

// ---------- 5. Orbit + conjecture
s = pres.addSlide(); bg(s);
title(s, "The abstract orbit and its conjecture");
s.addText([
  { text: "aorbit: iterate the three rules from (2, 7, 2) — reached from blank tape by a proven 62-step startup", options: { bullet: true, breakLine: true } },
  { text: "Death set (exact):  m = 0  ∨  (m = 2 ∧ a ≤ 1)   — astep_dies_iff", options: { bullet: true, breakLine: true } },
  { text: "SafeOrbitA :  the orbit never dies", options: { bullet: true, breakLine: true } },
  { text: "Transport lemmas realize every abstract state as a tape pattern; segment induction stitches safe segments into probe safety", options: { bullet: true } },
], { x: 0.7, y: 1.5, w: 7.2, h: 3.4, fontFace: BODY, fontSize: 15, color: SOFT, paraSpaceAfter: 12 });
panel(s, 8.2, 1.6, 4.4, 3.1, PANEL);
s.addText("MAIN THEOREM", { x: 8.5, y: 1.85, w: 3.9, h: 0.4, fontFace: HEAD, fontSize: 14, bold: true, color: MINT, margin: 0 });
s.addText("safeOrbitA_nonhalting :\n  SafeOrbitA →\n  ¬ RawHalts blankStart", { x: 8.5, y: 2.35, w: 3.9, h: 1.6, fontFace: MONO, fontSize: 14, bold: true, color: WHITE, margin: 0 });
s.addText("axioms: [propext, Quot.sound]", { x: 8.5, y: 4.0, w: 3.9, h: 0.4, fontFace: MONO, fontSize: 11, color: SOFT, margin: 0 });
panel(s, 0.7, 5.15, 11.9, 1.55, "1B2350");
s.addText("Everything about the machine is proven.  The single assumption is a statement about the integer orbit alone — and the next slide shows it is the community's own conjecture.",
  { x: 1.0, y: 5.35, w: 11.3, h: 1.2, fontFace: BODY, fontSize: 14.5, color: WHITE, margin: 0 });
s.addNotes("Dispatcher orbit_segment: under SafeOrbitA every realized state advances safely to another realized state; the keystone turns infinitely many safe segments into EProbeSafe.");

// ---------- 6. The conjugacy
s = pres.addSlide(); bg(s);
title(s, "The conjugacy: orbit ⇔ hydra process");
const map6 = [
  ["hydra value", "b = m + 2·(c−2)/3 + 5"],
  ["heads counter", "= a  (the counter block)"],
  ["even b step", "= merge (heads + 2)"],
  ["odd b step", "= drop (heads − 1)"],
  ["death", "odd b with heads ≤ 1"],
  ["update", "b ← b + ⌊b/2⌋"],
];
map6.forEach((m, i) => {
  const x = 0.7 + (i % 2) * 6.1, y = 1.55 + Math.floor(i / 2) * 1.15;
  panel(s, x, y, 5.7, 0.95);
  s.addText(m[0], { x: x + 0.25, y, w: 2.3, h: 0.95, valign: "middle", fontFace: HEAD, fontSize: 15, bold: true, color: MINT, margin: 0 });
  s.addText(m[1], { x: x + 2.6, y, w: 3.0, h: 0.95, valign: "middle", fontFace: MONO, fontSize: 13.5, color: WHITE, margin: 0 });
});
panel(s, 0.7, 5.25, 6.6, 1.45, "1B2350");
s.addText("relHA_step: the two systems run in lock-step; deaths coincide exactly.\nhydraSafe_iff_safeOrbitA · hydraSafe_nonhalting",
  { x: 1.0, y: 5.42, w: 6.0, h: 1.15, fontFace: MONO, fontSize: 12.5, color: WHITE, margin: 0 });
panel(s, 7.6, 5.25, 5.0, 1.45, "4A3A1E");
s.addText("Honest delta: formal death at heads ≤ 1 vs the wiki's 0 — one boundary case stronger; open follow-up.",
  { x: 7.9, y: 5.42, w: 4.4, h: 1.15, fontFace: BODY, fontSize: 12.5, color: GOLD, margin: 0 });
s.addNotes("First event: b = 12 = H(8), heads = 2 — the proven startup absorbs the wiki's first term. Sequence check: 12, 18, 27, 40, 60...");

// ---------- 7. Incision + volley
s = pres.addSlide(); bg(s);
title(s, "Incision events and the closed-form volley");
panel(s, 0.7, 1.5, 11.9, 1.35);
s.addText("volley (a, m, c)  =  (a,  2 − m % 2,  c + 3·⌊(m−1)/2⌋)",
  { x: 1.0, y: 1.65, w: 7.6, h: 1.05, valign: "middle", fontFace: MONO, fontSize: 15, bold: true, color: WHITE, margin: 0 });
s.addText("one formula replaces\nthe whole hydra run",
  { x: 8.9, y: 1.65, w: 3.5, h: 1.05, valign: "middle", fontFace: BODY, italic: true, fontSize: 12.5, color: SOFT, margin: 0 });
s.addText([
  { text: "estep = boundary rule + volley: exactly one event per counter movement", options: { bullet: true, breakLine: true } },
  { text: "eventSafe_iff_safeOrbitA: the sampled process dies ⇔ the full orbit dies", options: { bullet: true, breakLine: true } },
  { text: "Soundness AND completeness — checking between events is provably redundant", options: { bullet: true, breakLine: true } },
  { text: "eventSafe_nonhalting: event safety alone already implies the machine never halts", options: { bullet: true } },
], { x: 0.7, y: 3.1, w: 7.3, h: 3.3, fontFace: BODY, fontSize: 15, color: SOFT, paraSpaceAfter: 12 });
panel(s, 8.4, 3.1, 4.2, 3.4, PANEL);
s.addText("WHY IT PAYS", { x: 8.7, y: 3.35, w: 3.6, h: 0.4, fontFace: HEAD, fontSize: 14, bold: true, color: MINT, margin: 0 });
s.addText("volleys grow without bound: the k-th event skips ~b² raw steps, b ≈ 12·1.5ᵏ",
  { x: 8.7, y: 3.85, w: 3.6, h: 1.3, fontFace: BODY, fontSize: 13, color: WHITE, margin: 0 });
s.addText("event 16 ≈ step 10⁸\nevent 20,000 ≈ step 10⁷⁰⁴⁶", { x: 8.7, y: 5.25, w: 3.6, h: 1.0, fontFace: MONO, fontSize: 13, bold: true, color: GOLD, margin: 0 });
s.addNotes("The volley is where the certified acceleration lives — proved by fuel induction, then the two orbit-interleaving lemmas give the equivalence.");

// ---------- 8. Acceleration chart
s = pres.addSlide(); bg(s);
title(s, "Certified acceleration, measured");
s.addChart(pres.ChartType.line, [{
  name: "log10 cumulative raw steps",
  labels: ["0", "16", "500", "2k", "4k", "6k", "8k", "10k", "12k", "14k", "16k", "18k"],
  values: [2.4, 8.3, 178.7, 707.0, 1411.4, 2115.7, 2820.1, 3524.5, 4228.8, 4933.2, 5637.5, 6341.9],
}], {
  x: 0.7, y: 1.5, w: 8.2, h: 5.2,
  chartColors: [MINT], lineSize: 3,
  showTitle: true, title: "log₁₀ of raw-step-equivalent horizon vs incision events", titleColor: WHITE, titleFontSize: 14,
  showLegend: false, showValue: false,
  catAxisTitle: "event k", showCatAxisTitle: true, catAxisTitleColor: SOFT, catAxisTitleFontSize: 11,
  catAxisLabelColor: SOFT, catAxisLabelFontSize: 10,
  valAxisLabelColor: SOFT, valAxisLabelFontSize: 10,
  valGridLine: { color: "3A4580", size: 1 }, catGridLine: { style: "none" },
  plotArea: { fill: { color: PANEL } },
});
panel(s, 9.3, 1.6, 3.3, 2.3, PANEL);
s.addText("10⁸", { x: 9.3, y: 1.8, w: 3.3, h: 0.9, align: "center", fontFace: HEAD, fontSize: 40, bold: true, color: WHITE, margin: 0 });
s.addText("raw steps covered by the first 16 events", { x: 9.5, y: 2.75, w: 2.9, h: 0.9, align: "center", fontFace: BODY, fontSize: 12, color: SOFT, margin: 0 });
panel(s, 9.3, 4.2, 3.3, 2.3, PANEL);
s.addText("7,046", { x: 9.3, y: 4.4, w: 3.3, h: 0.9, align: "center", fontFace: HEAD, fontSize: 38, bold: true, color: WHITE, margin: 0 });
s.addText("digits in the raw-step count matched by 20k events", { x: 9.5, y: 5.35, w: 2.9, h: 0.9, align: "center", fontFace: BODY, fontSize: 12, color: SOFT, margin: 0 });
s.addNotes("Data from the certified event process (stage756): exact per-event raw costs from the proven step counts, summed in closed form.");

// ---------- 9. Axiom hygiene
s = pres.addSlide(); bg(s);
title(s, "Axiom hygiene: keeping Classical.choice out");
const cols9 = [
  ["CONTAMINATES", "4A2530", GOLD, [
    "omega proving a positive ∧ / ∨ goal",
    "decide / rfl through String.toList",
    "quantified decide over finite inductives (fails outright in core)"]],
  ["STAYS CLEAN", "1E4034", MINT, [
    "omega on atomic goals — split with constructor, congr 1, Or.inl",
    "decide over List Char literals",
    "cases a <;> cases b <;> simp_all for finite injectivity"]],
];
cols9.forEach((c, i) => {
  const x = 0.7 + i * 6.1;
  panel(s, x, 1.5, 5.7, 4.0, c[1]);
  s.addText(c[0], { x: x + 0.3, y: 1.75, w: 5.1, h: 0.5, valign: "top", fontFace: HEAD, fontSize: 19, bold: true, color: c[2], margin: 0 });
  s.addText(c[3].map((t, j) => ({ text: t, options: { bullet: true, breakLine: j < c[3].length - 1 } })),
    { x: x + 0.3, y: 2.4, w: 5.1, h: 2.9, valign: "top", fontFace: BODY, fontSize: 14, color: WHITE, paraSpaceAfter: 12 });
});
panel(s, 0.7, 5.75, 11.9, 1.0, "1B2350");
s.addText("A gate script rebuilds all packages and fails on any axiom outside [propext, Quot.sound] — the two quarantined String display lemmas are the only documented exception.",
  { x: 1.0, y: 5.85, w: 11.3, h: 0.8, fontFace: BODY, fontSize: 13.5, color: WHITE, margin: 0 });
s.addNotes("Both discoveries were found by bisecting #print axioms output; they are recorded as project memory and in the results doc.");

// ---------- 10. Parity & differential testing
s = pres.addSlide(); bg(s);
title(s, "Is it the right machine? Parity evidence");
const rows10 = [
  ["parse_ok", "in-Lean parser of the standard format, kernel-proved equal to the hand-written table; corrupted-code controls prove it non-vacuous", "axioms: [propext]"],
  ["trace ⇔ reference", "the proved step function, run executably, is byte-identical for 2,000 steps vs an independent 30-line Python stepper (both machines)", "4/4 tests green"],
  ["startup anchors", "the proven milestones appear on schedule in the independent trace: step 62 → B@6 (Antihydra), step 35 → E@5 (dossier-1)", "matches exactly"],
];
rows10.forEach((r, i) => {
  const y = 1.5 + i * 1.75;
  panel(s, 0.7, y, 11.9, 1.5);
  s.addText(r[0], { x: 1.0, y: y + 0.15, w: 3.1, h: 0.6, fontFace: MONO, fontSize: 16, bold: true, color: MINT, margin: 0 });
  s.addText(r[1], { x: 4.3, y: y + 0.12, w: 5.9, h: 1.3, fontFace: BODY, fontSize: 13, color: WHITE, margin: 0 });
  s.addText(r[2], { x: 10.6, y: y + 0.15, w: 1.85, h: 1.2, fontFace: MONO, fontSize: 11.5, color: GOLD, margin: 0 });
});
s.addNotes("Three independent evidence layers tying the formal object to the published machine — the parity plan's tasks 1 and 2.");

// ---------- 11. Palomar packaging
s = pres.addSlide(); bg(s);
title(s, "Palomar packaging: Challenge / Solution / transport");
const flow11 = ["Challenge.lean\nself-contained statements\nzero imports · sorried", "Solution.lean\nsame declarations,\nreal proofs", "transport\ntype isomorphisms +\ncommutation lemmas", "certified theorems\nsafeOrbitA_nonhalting\n& friends"];
flow11.forEach((t, i) => {
  const x = 0.7 + i * 3.06;
  panel(s, x, 1.6, 2.75, 1.9, i === 3 ? "1E4034" : PANEL);
  s.addText(t, { x: x + 0.15, y: 1.6, w: 2.55, h: 1.9, align: "center", valign: "middle", fontFace: MONO, fontSize: 11.5, color: WHITE, margin: 0.05 });
  if (i < 3) s.addText("→", { x: x + 2.75, y: 1.6, w: 0.31, h: 1.9, align: "center", valign: "middle", fontFace: BODY, fontSize: 20, color: SOFT, margin: 0 });
});
s.addText([
  { text: "Comparator (Lean kernel + independent NanoDa kernel) will confirm Solution proves exactly the Challenge, using only permitted axioms", options: { bullet: true, breakLine: true } },
  { text: "All three entries pass the full local intake contract; challenges are 79–153 lines, comfortably auditable", options: { bullet: true, breakLine: true } },
  { text: "All four compared theorems: [propext, Quot.sound] — strictly inside Palomar's allowed set", options: { bullet: true, breakLine: true } },
  { text: "Remaining before submission: LICENSE choice, git push, owner sign-off", options: { bullet: true } },
], { x: 0.7, y: 3.9, w: 11.9, h: 2.8, fontFace: BODY, fontSize: 15, color: SOFT, paraSpaceAfter: 12 });
s.addNotes("The transport pattern is the reusable trick: self-contained auditable statements, big development behind them, mechanical bridge between.");

// ---------- 12. Close
s = pres.addSlide(); bg(s);
s.addText("One machine, one conjecture", { x: 0.9, y: 1.6, w: 11.5, h: 0.9, fontFace: HEAD, fontSize: 42, bold: true, color: WHITE });
s.addText("HydraSafe  →  Antihydra never halts", { x: 0.92, y: 2.75, w: 10, h: 0.6, fontFace: MONO, fontSize: 22, bold: true, color: MINT });
s.addText([
  { text: "The machine's entire dynamics are theorems; the open part is pure arithmetic", options: { bullet: true, breakLine: true } },
  { text: "Boundary-only checking is certified — the conjecture can be hunted at 10⁷⁰⁴⁶-step scale", options: { bullet: true, breakLine: true } },
  { text: "The same architecture is ready for the next cryptid", options: { bullet: true } },
], { x: 0.92, y: 3.7, w: 10.8, h: 2.2, fontFace: BODY, fontSize: 16, color: SOFT, paraSpaceAfter: 12 });
s.addText("bbchallenge-proofs · docs/learning · docs/results/2026-08-22-*", { x: 0.92, y: 6.5, w: 10, h: 0.4, fontFace: MONO, fontSize: 12, color: SOFT });
s.addNotes("End on the reduction framing and the invitation: the conjecture is now a clean target.");

pres.writeFile({ fileName: "antihydra-technical-deep-dive.pptx" }).then(() => console.log("deck2 written"));

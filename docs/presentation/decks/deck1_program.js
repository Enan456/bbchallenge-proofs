// Deck 1 — "The BB(6) Program": overview deck.
// Palette: Midnight Executive — navy 1E2761 dominant, ice CADCFC, white.
// Motif: numbered discs + rounded cards. Fonts: Cambria heads / Calibri body.
const pptxgen = require("pptxgenjs");
const pres = new pptxgen();
pres.layout = "LAYOUT_WIDE"; // 13.33 x 7.5

const NAVY = "1E2761", ICE = "CADCFC", WHITE = "FFFFFF";
const INK = "1A1A2E", MUTED = "5A6B8C", CARD = "EEF3FC";
const HEAD = "Cambria", BODY = "Calibri";
const W = 13.33, H = 7.5;

function darkBg(s) { s.background = { color: NAVY }; }
function lightBg(s) { s.background = { color: WHITE }; }
function disc(s, x, y, d, label, fill, txtColor) {
  s.addShape(pres.ShapeType.ellipse, { x, y, w: d, h: d, fill: { color: fill } });
  s.addText(label, { x, y, w: d, h: d, align: "center", valign: "middle",
    fontFace: HEAD, fontSize: d >= 0.6 ? 18 : 14, bold: true, color: txtColor, margin: 0 });
}
function card(s, x, y, w, h, fill) {
  s.addShape(pres.ShapeType.roundRect, { x, y, w, h, rectRadius: 0.08,
    fill: { color: fill }, shadow: { type: "outer", color: "9AA7C4", blur: 6, offset: 2, angle: 90, opacity: 0.35 } });
}

// ---------- 1. Title (dark)
let s = pres.addSlide(); darkBg(s);
s.addText("The BB(6) Program", { x: 0.9, y: 2.1, w: 11.5, h: 1.2, fontFace: HEAD,
  fontSize: 54, bold: true, color: WHITE });
s.addText("Machines, machine-checked proofs, and incision geometry\non the Busy Beaver frontier", {
  x: 0.92, y: 3.35, w: 10.5, h: 1.0, fontFace: BODY, fontSize: 20, color: ICE });
s.addText("1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA", { x: 0.92, y: 6.3, w: 8, h: 0.4,
  fontFace: "Courier New", fontSize: 13, color: "8FA3D0" });
s.addText("bbchallenge-proofs  ·  2026-08-22", { x: 0.92, y: 6.75, w: 8, h: 0.4,
  fontFace: BODY, fontSize: 13, color: "8FA3D0" });
disc(s, 11.5, 5.9, 1.0, "BB6", ICE, NAVY);
s.addNotes("The program in one line: classify the BB(6) open set, exactly emulate the structured machines, formally reduce two of them to single conjectures in Lean, prove boundary-only checking, and validate everything for Tao's Palomar registry.");

// ---------- 2. The game
s = pres.addSlide(); lightBg(s);
s.addText("The game: Busy Beaver", { x: 0.7, y: 0.45, w: 10, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addText("Among all n-state Turing machines started on a blank tape, which runs longest before halting?  BB(n) outgrows every computable function — it is the edge of what computation can know.",
  { x: 0.7, y: 1.45, w: 7.3, h: 1.6, fontFace: BODY, fontSize: 16, color: INK });
s.addText([
  { text: "BB(5) settled July 2024, machine-verified in Rocq (Coq)", options: { bullet: true, breakLine: true } },
  { text: "BB(6) is the frontier: value exceeds numbers writable in this universe", options: { bullet: true, breakLine: true } },
  { text: "“Cryptids”: machines whose halting encodes deep open arithmetic", options: { bullet: true } },
], { x: 0.7, y: 3.1, w: 7.3, h: 1.8, fontFace: BODY, fontSize: 15, color: INK, paraSpaceAfter: 8 });
card(s, 8.6, 1.45, 4.0, 2.2, CARD);
s.addText("47,176,870", { x: 8.6, y: 1.7, w: 4.0, h: 0.9, align: "center", fontFace: HEAD, fontSize: 40, bold: true, color: NAVY, margin: 0 });
s.addText("steps — BB(5), proven exactly", { x: 8.6, y: 2.6, w: 4.0, h: 0.5, align: "center", fontFace: BODY, fontSize: 13, color: MUTED, margin: 0 });
card(s, 8.6, 3.95, 4.0, 2.2, CARD);
s.addText("1,158", { x: 8.6, y: 4.2, w: 4.0, h: 0.9, align: "center", fontFace: HEAD, fontSize: 40, bold: true, color: NAVY, margin: 0 });
s.addText("BB(6) machines still undecided", { x: 8.6, y: 5.1, w: 4.0, h: 0.5, align: "center", fontFace: BODY, fontSize: 13, color: MUTED, margin: 0 });
s.addNotes("Set the stakes: BB(5) is done and formal; BB(6) has an official open set of 1,158 machines that resist all known deciders.");

// ---------- 3. Taxonomy chart
s = pres.addSlide(); lightBg(s);
s.addText("What the open set looks like", { x: 0.7, y: 0.45, w: 11, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addText("Every holdout classified through the Collatz-lens record structure (stage745, 0 errors). Collapse-like behavior is the dominant phenotype — and exactly two machines are literal 1-D Collatz.",
  { x: 0.7, y: 1.4, w: 11.9, h: 0.8, fontFace: BODY, fontSize: 15, color: INK });
s.addChart(pres.ChartType.bar, [{
  name: "machines",
  labels: ["Growing-dimension", "Compact growth (cryptid-shaped)", "Bounded varying", "Exact 1-D Collatz projection"],
  values: [1006, 51, 35, 2],
}], {
  x: 0.9, y: 2.4, w: 11.5, h: 4.4, barDir: "bar",
  chartColors: [NAVY, "3A4A8C", "7C8DBB", "B8C6E8"],
  showValue: true, dataLabelPosition: "outEnd", dataLabelColor: INK, dataLabelFontSize: 13,
  showTitle: false, showLegend: false,
  catAxisLabelColor: INK, catAxisLabelFontSize: 13,
  valAxisLabelColor: MUTED, valAxisLabelFontSize: 11,
  valGridLine: { color: "DDE4F2", size: 1 }, catGridLine: { style: "none" },
});
s.addNotes("1,094-holdout sweep: 1006 growing-dim, 51 compact-growth, 35 bounded-varying, 2 exact vector-Collatz projections (Dvisetu and one peer). Honest labeling: classification only, nothing decided.");

// ---------- 4. Exact emulation
s = pres.addSlide(); lightBg(s);
s.addText("Exact emulation, fail-closed", { x: 0.7, y: 0.45, w: 11, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addText("A macro system is a set of arithmetic rules: “from a record of shape X, exactly f(k) raw steps reach shape Y.”  Rules must replay the raw machine perfectly — or the fit is rejected.",
  { x: 0.7, y: 1.4, w: 11.9, h: 0.9, fontFace: BODY, fontSize: 15, color: INK });
const stats4 = [
  ["100%", "exact replay, in & out of sample, over 10⁸ raw steps"],
  ["13 / 13", "Antihydra rule obligations discharged (stage753)"],
  ["33 / 33", "dossier-1 rule obligations discharged"],
  ["6 + 1", "solid + weak exact-macro passes after the 2026-08-04 gate fix"],
];
stats4.forEach((t, i) => {
  const x = 0.7 + (i % 2) * 6.1, y = 2.6 + Math.floor(i / 2) * 2.15;
  card(s, x, y, 5.7, 1.85, CARD);
  s.addText(t[0], { x: x + 0.25, y: y + 0.2, w: 2.6, h: 0.9, fontFace: HEAD, fontSize: 34, bold: true, color: NAVY, margin: 0 });
  s.addText(t[1], { x: x + 0.25, y: y + 1.05, w: 5.2, h: 0.7, fontFace: BODY, fontSize: 13, color: MUTED, margin: 0 });
});
s.addNotes("Emulation is evidence, not proof — and it is fail-closed: the earlier unsound bouncer certificates were demoted, and the PASS gate was tightened, refuting two of nine. Corrections are documented, not buried.");

// ---------- 5. The reductions
s = pres.addSlide(); lightBg(s);
s.addText("Two machines, formally reduced", { x: 0.7, y: 0.45, w: 11, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
const machines = [
  ["Antihydra", "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA",
   "safeOrbitA_nonhalting :  SafeOrbitA → ¬ halts",
   "Three record rules (hydra / drop / merge) proven for all block values; 62-step startup; orbit conjecture = the community's Antihydra conjecture."],
  ["Dossier-1", "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB",
   "safeOrbit_nonhalting :  SafeOrbit → ¬ halts",
   "Seven rules over a stack of chain levels with collapse cascades; 35-step startup; conjecture is a recursive (3n+7)/2 checkpoint law."],
];
machines.forEach((m, i) => {
  const y = 1.5 + i * 2.85;
  card(s, 0.7, y, 11.9, 2.55, CARD);
  disc(s, 1.0, y + 0.35, 0.7, i === 0 ? "A" : "D", NAVY, WHITE);
  s.addText(m[0], { x: 1.95, y: y + 0.3, w: 4.5, h: 0.6, fontFace: HEAD, fontSize: 24, bold: true, color: INK, margin: 0 });
  s.addText(m[1], { x: 6.0, y: y + 0.42, w: 6.4, h: 0.4, fontFace: "Courier New", fontSize: 11, color: MUTED, margin: 0 });
  s.addText(m[2], { x: 1.95, y: y + 1.0, w: 10.3, h: 0.5, fontFace: "Courier New", fontSize: 15, bold: true, color: NAVY, margin: 0 });
  s.addText(m[3], { x: 1.95, y: y + 1.6, w: 10.3, h: 0.85, fontFace: BODY, fontSize: 13, color: INK, margin: 0 });
});
s.addNotes("Core Lean 4 only, no Mathlib, no sorry; axioms exactly [propext, Quot.sound], enforced by a gate script. Every dynamical fact proven; only the arithmetic conjecture is assumed.");

// ---------- 6. The hydra bridge
s = pres.addSlide(); lightBg(s);
s.addText("The bridge to the real conjecture", { x: 0.7, y: 0.45, w: 11, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addText("The community states Antihydra's conjecture 1-dimensionally.  A machine-checked conjugacy proves our orbit hypothesis is exactly that statement (one boundary case stronger).",
  { x: 0.7, y: 1.4, w: 11.9, h: 0.85, fontFace: BODY, fontSize: 15, color: INK });
const steps6 = ["b ← 12", "even b :  heads + 2", "odd b :  heads − 1", "b ← b + ⌊b/2⌋"];
steps6.forEach((t, i) => {
  const x = 0.7 + i * 3.12;
  card(s, x, 2.6, 2.8, 1.1, NAVY);
  s.addText(t, { x, y: 2.6, w: 2.8, h: 1.1, align: "center", valign: "middle", fontFace: "Courier New", fontSize: 15, bold: true, color: WHITE, margin: 0.05 });
  if (i < 3) s.addText("→", { x: x + 2.8, y: 2.6, w: 0.34, h: 1.1, align: "center", valign: "middle", fontFace: BODY, fontSize: 20, color: MUTED, margin: 0 });
});
card(s, 0.7, 4.1, 5.8, 2.5, CARD);
s.addText("The change of variables", { x: 0.95, y: 4.3, w: 5.3, h: 0.5, fontFace: HEAD, fontSize: 18, bold: true, color: INK, margin: 0 });
s.addText("b  =  m + 2·(c−2)/3 + 5\nheads  =  a   (the machine's counter block)\nmerges are the even steps, drops the odd ones",
  { x: 0.95, y: 4.85, w: 5.3, h: 1.6, fontFace: "Courier New", fontSize: 13, color: NAVY, margin: 0 });
card(s, 6.8, 4.1, 5.8, 2.5, "FFF4E8");
s.addText("The honest delta", { x: 7.05, y: 4.3, w: 5.3, h: 0.5, fontFace: HEAD, fontSize: 18, bold: true, color: "8A4B12", margin: 0 });
s.addText("Formal death fires at heads ≤ 1; the wiki's at 0. The tape grammar needs a non-empty counter block, so the hypothesis is one drop stronger — documented, and closing it is listed follow-up work.",
  { x: 7.05, y: 4.85, w: 5.3, h: 1.6, fontFace: BODY, fontSize: 13, color: "6B4A2B", margin: 0 });
s.addNotes("hydraSafe_iff_safeOrbitA and hydraSafe_nonhalting: the two processes run in lock-step and die together. First event b = 12 = H(8), heads 2 — the startup absorbs the wiki's first term.");

// ---------- 7. Incision theorem
s = pres.addSlide(); lightBg(s);
s.addText("Check only where the cut can happen", { x: 0.7, y: 0.45, w: 11.9, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addText([
  { text: "Death set is explicit:  m = 0, or a drop (m = 2) with counter ≤ 1", options: { bullet: true, breakLine: true } },
  { text: "Volley: every hydra run collapses to one closed-form jump", options: { bullet: true, breakLine: true } },
  { text: "Event process = one boundary rule + one volley, per counter move", options: { bullet: true, breakLine: true } },
  { text: "Theorem: event process dies  ⇔  full orbit dies  (sound AND complete)", options: { bullet: true } },
], { x: 0.7, y: 1.5, w: 6.9, h: 2.6, fontFace: BODY, fontSize: 15, color: INK, paraSpaceAfter: 10 });
card(s, 0.7, 4.35, 6.9, 2.3, NAVY);
s.addText("eventSafe_iff_safeOrbitA", { x: 1.0, y: 4.6, w: 6.3, h: 0.5, fontFace: "Courier New", fontSize: 17, bold: true, color: ICE, margin: 0 });
s.addText("certified in core Lean · axioms [propext, Quot.sound]\nchained: event safety alone ⇒ Antihydra never halts",
  { x: 1.0, y: 5.2, w: 6.3, h: 1.2, fontFace: BODY, fontSize: 14, color: WHITE, margin: 0 });
card(s, 8.0, 1.5, 4.6, 2.4, CARD);
s.addText("16", { x: 8.0, y: 1.75, w: 4.6, h: 1.0, align: "center", fontFace: HEAD, fontSize: 48, bold: true, color: NAVY, margin: 0 });
s.addText("incision events cover the first 10⁸ raw machine steps", { x: 8.25, y: 2.8, w: 4.1, h: 0.8, align: "center", fontFace: BODY, fontSize: 13, color: MUTED, margin: 0 });
card(s, 8.0, 4.25, 4.6, 2.4, CARD);
s.addText("10⁷⁰⁴⁶", { x: 8.0, y: 4.5, w: 4.6, h: 1.0, align: "center", fontFace: HEAD, fontSize: 44, bold: true, color: NAVY, margin: 0 });
s.addText("raw-step equivalent of 20,000 events — a different regime, not an optimization", { x: 8.25, y: 5.55, w: 4.1, h: 0.9, align: "center", fontFace: BODY, fontSize: 13, color: MUTED, margin: 0 });
s.addNotes("The incision theorem is the certified version of 'only check at the boundaries'. Completeness matters: you provably lose nothing by never looking between events.");

// ---------- 8. Atlas findings (chart)
s = pres.addSlide(); lightBg(s);
s.addText("The incision atlas (stage756)", { x: 0.7, y: 0.45, w: 11, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addChart(pres.ChartType.line, [{
  name: "heads counter",
  labels: ["0", "2k", "4k", "6k", "8k", "10k", "12k", "14k", "16k", "18k", "20k"],
  values: [2, 1035, 2071, 3020, 3897, 4861, 5855, 6891, 7942, 8945, 9919],
}], {
  x: 0.7, y: 1.6, w: 7.3, h: 4.9,
  chartColors: [NAVY], lineSize: 3, lineSmooth: false,
  showTitle: true, title: "Heads counter across 20,000 certified events", titleColor: INK, titleFontSize: 14,
  showLegend: false, showValue: false,
  catAxisTitle: "event k", showCatAxisTitle: true, catAxisTitleColor: MUTED, catAxisTitleFontSize: 11,
  catAxisLabelColor: MUTED, catAxisLabelFontSize: 10,
  valAxisLabelColor: MUTED, valAxisLabelFontSize: 10,
  valGridLine: { color: "DDE4F2", size: 1 }, catGridLine: { style: "none" },
});
const stats8 = [
  ["+0.5 / event", "measured counter drift — exactly the random-walk expectation"],
  ["margin 4", "closest approach to the death condition in 20k events"],
  ["3 + 2", "machines pairing up into identical incision profiles (delta-rule families)"],
];
stats8.forEach((t, i) => {
  const y = 1.6 + i * 1.7;
  card(s, 8.35, y, 4.25, 1.45, CARD);
  s.addText(t[0], { x: 8.6, y: y + 0.12, w: 3.8, h: 0.55, fontFace: HEAD, fontSize: 21, bold: true, color: NAVY, margin: 0 });
  s.addText(t[1], { x: 8.6, y: y + 0.68, w: 3.8, h: 0.72, fontFace: BODY, fontSize: 11.5, color: MUTED, margin: 0 });
});
s.addNotes("Real data from the certified event process. Honest finding: raw simplex/hyperbolic charts degenerate toward the dominant coordinate — log-scaled charts are the refinement before invariant hunting.");

// ---------- 9. Trust engineering
s = pres.addSlide(); lightBg(s);
s.addText("Trust engineering", { x: 0.7, y: 0.45, w: 11, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
const rows9 = [
  ["1", "Axiom gate", "Every theorem reports exactly [propext, Quot.sound]; a script fails the build otherwise. Two contamination channels found and engineered out (omega on compound goals; String.toList)."],
  ["2", "Parser parity", "A Lean parser of the standard machine format is kernel-proved equal to the hand-written tables — with corrupted-code negative controls."],
  ["3", "Differential testing", "The proved step function, run executably, is byte-identical for thousands of steps against an independent 30-line Python stepper."],
  ["4", "Fail-closed corrections", "Unsound certificates demoted; the PASS gate retightened and two verdicts publicly refuted. Corrections are results, not embarrassments."],
];
rows9.forEach((r, i) => {
  const y = 1.5 + i * 1.35;
  disc(s, 0.75, y + 0.18, 0.62, r[0], NAVY, WHITE);
  s.addText(r[1], { x: 1.75, y: y + 0.24, w: 3.05, h: 0.5, valign: "top", fontFace: HEAD, fontSize: 18, bold: true, color: INK, margin: 0 });
  s.addText(r[2], { x: 4.9, y: y + 0.24, w: 7.7, h: 1.05, valign: "top", fontFace: BODY, fontSize: 12.5, color: MUTED, margin: 0 });
});
s.addNotes("The discipline is the product: honest labels on everything empirical, mechanical checks on everything formal.");

// ---------- 10. Palomar
s = pres.addSlide(); lightBg(s);
s.addText("Validated for Tao's Palomar registry", { x: 0.7, y: 0.45, w: 11.9, h: 0.8, fontFace: HEAD, fontSize: 38, bold: true, color: INK });
s.addText("Palomar (announced 2026-08-18): a registry of Lean-verified mathematics.  Small auditable Challenge + proving Solution, mechanically compared by kernel replay, three permitted axioms.",
  { x: 0.7, y: 1.4, w: 11.9, h: 0.85, fontFace: BODY, fontSize: 15, color: INK });
const entries10 = [
  ["Antihydra", "120-line challenge · machine + hydra process", "antihydra_nonhalting"],
  ["Incision", "79-line challenge · pure arithmetic", "boundary_checking_complete"],
  ["Dossier-1", "153-line challenge · machine + chain orbit", "dossier1_nonhalting"],
];
entries10.forEach((e, i) => {
  const x = 0.7 + i * 4.1;
  card(s, x, 2.55, 3.8, 2.6, CARD);
  s.addText(e[0], { x: x + 0.25, y: 2.8, w: 3.3, h: 0.5, fontFace: HEAD, fontSize: 20, bold: true, color: INK, margin: 0 });
  s.addText(e[1], { x: x + 0.25, y: 3.35, w: 3.3, h: 0.8, fontFace: BODY, fontSize: 12.5, color: MUTED, margin: 0 });
  s.addText(e[2], { x: x + 0.25, y: 4.25, w: 3.3, h: 0.6, fontFace: "Courier New", fontSize: 11.5, bold: true, color: NAVY, margin: 0 });
});
card(s, 0.7, 5.5, 11.9, 1.25, "E8F5EC");
s.addText("Every mechanical intake check passes — solutions transport the certified theorems across self-contained challenge definitions.  Remaining: a LICENSE choice, a git push, and owner sign-off.",
  { x: 1.0, y: 5.62, w: 11.3, h: 1.0, fontFace: BODY, fontSize: 14, color: "1E5631", margin: 0 });
s.addNotes("One entry per comparator config; provenance rules forced three separate metadata files (Antihydra formalizes the wiki analysis; the other two are original first presentations). Nothing submitted without sign-off.");

// ---------- 11. Close (dark)
s = pres.addSlide(); darkBg(s);
s.addText("Where this stands", { x: 0.9, y: 0.7, w: 11, h: 0.9, fontFace: HEAD, fontSize: 40, bold: true, color: WHITE });
const cols11 = [
  ["PROVEN", "Every dynamical fact about both machines · the reductions · the bridge · the incision theorem · parser parity", ICE],
  ["ASSUMED", "Two orbit conjectures — one is the Antihydra conjecture itself. Believed true; proven by no one.", "F9E795"],
  ["NEXT", "Close the heads ≤ 1 boundary case · dossier-1's 1-D bridge · log-scaled atlas · Palomar submission on sign-off", "97E8C0"],
];
cols11.forEach((c, i) => {
  const x = 0.9 + i * 4.0;
  s.addShape(pres.ShapeType.roundRect, { x, y: 2.0, w: 3.7, h: 3.2, rectRadius: 0.08, fill: { color: "27336F" } });
  s.addText(c[0], { x: x + 0.3, y: 2.28, w: 3.1, h: 0.5, valign: "top", fontFace: HEAD, fontSize: 20, bold: true, color: c[2], margin: 0 });
  s.addText(c[1], { x: x + 0.3, y: 2.88, w: 3.1, h: 2.15, valign: "top", fontFace: BODY, fontSize: 13.5, color: WHITE, margin: 0 });
});
s.addText("Nothing here decides any machine — each machine's fate is now a clean piece of arithmetic, plus the certified tools to hunt it.",
  { x: 0.9, y: 6.1, w: 11.5, h: 0.8, fontFace: BODY, italic: true, fontSize: 16, color: ICE });
s.addNotes("Close on the honest framing: reduction, not decision — and a template architecture for the rest of the open set.");

pres.writeFile({ fileName: "bb6-program-overview.pptx" }).then(() => console.log("deck1 written"));

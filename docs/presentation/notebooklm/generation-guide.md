# NotebookLM generation guide — podcasts and videos

How to turn the four source documents in this folder into a podcast series
(Audio Overviews) and explainer videos (Video Overviews) with Google
NotebookLM.

## Setup (once)

1. Go to <https://notebooklm.google.com> and sign in.
2. **Create a notebook** named `BB(6) Proofs — bbchallenge program`.
3. **Add sources** — upload these four files (Sources → Add → upload):
   - `01-source-program-overview.md`
   - `02-source-lean-proofs.md`
   - `03-source-incision-geometry.md`
   - `04-source-palomar.md`
   Optionally also upload `docs/submissions/statement-of-claims.md` and
   `docs/results/2026-08-22-packages-bridge-incision.md` from this repo for
   deeper grounding.

## The podcast series (Audio Overviews)

NotebookLM generates one Audio Overview at a time per notebook; regenerate
with a different focus prompt for each episode (download each MP3 before
generating the next). In the notebook: **Studio → Audio Overview →
Customize**, paste the episode prompt, generate, download.

**Episode 1 — "The Beaver Hunt" (overview, ~10 min).**
> Focus on source 1 (the program overview). Explain what the Busy Beaver
> problem is, why BB(6) is the frontier, what a cryptid is, and walk
> through the five stages of this project end to end. Keep it accessible —
> no Lean syntax — but keep every number honest, and emphasize the honesty
> discipline: nothing here decides any machine.

**Episode 2 — "One Conjecture Away" (the proofs, ~15 min).**
> Focus on source 2 (the Lean proofs). Tell the story of reducing Antihydra
> and dossier-1 to single conjectures: the raw tape layer, halt
> localization, the three record rules and their exact step counts, the
> abstract orbit, and the bridge theorem with the change of variables
> b = m + 2(c−2)/3 + 5. Spend real time on the trust engineering: parser
> parity, differential testing, and the two axiom-contamination surprises
> (omega on compound goals, String.toList). Explain the honest delta
> between the formal hypothesis and the wiki's conjecture.

**Episode 3 — "Cutting at the Boundary" (incision geometry, ~12 min).**
> Focus on source 3. Explain incisions, the explicit death set, the
> closed-form volley, and the soundness-and-completeness theorem for
> boundary-only checking. Make the acceleration vivid: 16 events cover a
> hundred million raw steps; 20,000 events equal a number with seven
> thousand digits. Then the non-Euclidean hypothesis — log, simplex,
> hyperbolic charts, death as a simplex face — including the honesty box
> and the first family-matching result.

**Episode 4 — "Registry Day" (Palomar, ~10 min).**
> Focus on source 4. Tell the Palomar story: what Tao announced, how the
> Challenge/Solution/Comparator design resists overclaiming, what the
> three entries are, why the Solutions needed transport developments, what
> the local validation found (everything passes except the license), and
> why claiming *less* is what makes the entries eligible.

## The videos (Video Overviews)

In the notebook: **Studio → Video Overview → Customize**. Two suggested
videos:

**Video A — program explainer (general audience).**
> Base the video on sources 1 and 3. Structure: the Busy Beaver game → the
> BB(6) open set and cryptids → collapse-like behavior → reduce a machine
> to one conjecture → check only at the incisions → what would remain to
> be done. Use the numbers 1,158 machines / 6+1 exact passes / 16 events ≈
> 10⁸ steps / two axioms as recurring anchors.

**Video B — technical walkthrough (formal-methods audience).**
> Base the video on sources 2 and 4. Structure: trust base design in core
> Lean → halt localization → rule trajectories with safety certificates →
> segment induction → the hydra bridge and its honest delta → parser
> parity and differential testing → Palomar Challenge/Solution mechanics
> and the transport pattern. Keep the axiom story ([propext, Quot.sound],
> and how Classical.choice was kept out) as the through-line.

## Notes

- The four sources are deliberately self-contained: NotebookLM sees only
  what is uploaded, so each document restates the needed context.
- Facts in the sources are faithful to the repo's results documents as of
  2026-08-22; regenerate them if results move (they live in
  `docs/presentation/notebooklm/`).
- NotebookLM output is generative: spot-check numbers against
  `docs/submissions/statement-of-claims.md` before publishing any episode.

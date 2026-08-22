# docs/presentation — podcasts, videos, and slide decks

Everything needed to present the program, in three parts.

## 1. NotebookLM kit (`notebooklm/`)

Four self-contained narrative source documents plus a generation guide:

| file | covers |
|---|---|
| `01-source-program-overview.md` | the whole program, five stages, honesty discipline |
| `02-source-lean-proofs.md` | both machine reductions, the hydra bridge, trust engineering |
| `03-source-incision-geometry.md` | boundary-only checking, the atlas, the non-Euclidean hypothesis |
| `04-source-palomar.md` | the Palomar registry story and validation |
| `generation-guide.md` | exact steps + per-episode customization prompts for a 4-episode podcast series (Audio Overviews) and 2 videos (Video Overviews) |

Workflow: sign in at <https://notebooklm.google.com>, create a notebook,
upload the four sources, then follow `generation-guide.md` — it contains a
ready-to-paste focus prompt for each episode/video. Spot-check generated
audio/video against `docs/submissions/statement-of-claims.md` before
publishing (NotebookLM output is generative).

## 2. Slide decks (`decks/`)

Two decks, built with pptxgenjs via the Anthropic `pptx` skill
(`document-skills@anthropic-agent-skills`), validated (OOXML schema +
relationship checks) and visually QA'd from rendered slides:

| deck | audience | slides |
|---|---|---|
| `bb6-program-overview.pptx` | general / overview | 11 — the game, the taxonomy (native chart of 1006/51/35/2), emulation, the two reductions, the bridge, the incision theorem, atlas data (native chart), trust engineering, Palomar, close |
| `antihydra-technical-deep-dive.pptx` | formal methods / technical | 12 — the transition table, halt localization chain, the three rules, orbit + conjecture, the conjugacy, volley + incision theorem, measured acceleration (native chart), axiom hygiene, parity evidence, Palomar packaging, close |

Every slide carries speaker notes. Charts are native PowerPoint charts fed
with real data from the certified event process. Regenerate after content
changes with:

```sh
cd docs/presentation/decks
node deck1_program.js && node deck2_technical.js
```

PDF renders of both decks sit alongside the .pptx files for quick preview.

## 3. Facts discipline

All numbers in the sources and decks trace to
`docs/submissions/statement-of-claims.md` and
`docs/results/2026-08-22-*.md` as of 2026-08-22. If results move, update
those first, then regenerate this folder.

# Proof generators for the dossier-2/3 conditional closure

These python scripts generated (and regenerate) the certified layers in
`BusyBeaverCore/Dossier2RawTM.lean` / `Dossier3RawTM.lean`:

- `atomgen2.py` — simulation-driven fixed-window atom theorems
  (cross/terminate/fuse/edge/march/spawn-variant)
- `epicompile.py` + `plans_d2.py` + `mirror_plans.py` — the episode
  compiler: seven spawn-entry-to-spawn-entry episode theorems per
  machine over `holeTape` shapes (D3 = systematic mirror of the D2
  plans)
- `anchorgen2.py` + `gen_composite.py` — composite startup anchors:
  short concrete runs (term-mode `stepN_chain` gluing, `rfl` tape
  facts, one-step evaluator lemmas — never `rw` on a `stepN` goal, or
  the elaborator's post-rewrite `rfl` attempt will try to evaluate the
  whole run) joined by literal episode-theorem instances
- `abstract_d2.lean` / `abstract_d3.lean` + `insert_abstract.py` — the
  abstract five-integer orbit, transport, and conditional finals
- `vpredict.py` / `metastep_check.py` — the validated interaction
  calculus and the exact python mirror of `metaStep`

Everything they emit is checked by Lean; the generators are convenience,
not trust surface.

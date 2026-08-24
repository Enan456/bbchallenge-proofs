#!/usr/bin/env bash
# Axiom-gated build of all Lean packages (plan 1, task 5).
#
# Builds busy-beaver-core/, packages/dossier1/, packages/flying-dragon/ and fails if any
# `#print axioms` report contains an axiom outside the allowed set.
# The only tolerated exception is Bridge/Format.lean's two quarantined
# String-display lemmas (`*_code_chars`), which are documented to use
# `Classical.choice` via `String.toList`.
#
# Usage: scripts/check_lean.sh   (from the repo root)

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"

LOG="$(mktemp)"
trap 'rm -f "$LOG"' EXIT

for pkg in busy-beaver-core packages/dossier1 packages/flying-dragon packages/forge; do
  echo "== lake build: $pkg"
  (cd "$ROOT/$pkg" && lake build) 2>&1 | tee -a "$LOG"
done

echo "== axiom gate"
# Every axiom report must be a subset of [propext, Classical.choice, Quot.sound],
# and Classical.choice may appear ONLY on the quarantined _code_chars lemmas.
BAD=0
grep "depends on axioms" "$LOG" | while IFS= read -r line; do
  axioms=$(echo "$line" | sed -E 's/.*depends on axioms: \[(.*)\].*/\1/')
  decl=$(echo "$line" | sed -E "s/.*'([^']+)'.*/\1/")
  for ax in $(echo "$axioms" | tr -d ',' ); do
    case "$ax" in
      propext|Quot.sound) ;;
      Classical.choice)
        case "$decl" in
          *code_chars) ;;
          *) echo "FORBIDDEN axiom Classical.choice in $decl"; exit 1 ;;
        esac ;;
      *) echo "FORBIDDEN axiom $ax in $decl"; exit 1 ;;
    esac
  done
done || BAD=1

if grep -q "sorryAx" "$LOG"; then
  echo "FORBIDDEN: sorryAx present"
  BAD=1
fi

if [ "$BAD" -ne 0 ]; then
  echo "axiom gate FAILED"
  exit 1
fi
echo "axiom gate OK"

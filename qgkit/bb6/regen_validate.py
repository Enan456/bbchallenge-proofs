#!/usr/bin/env python3
"""Regeneration acceptance harness: regenerate d9/d13/d14/d16 with the
generator and diff each against the committed hand-built file.  Reports,
for every def/theorem, whether it matches (ignoring comments)."""
import os
import sys
import re
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rawstep_generator as G  # noqa

REPO = G.REPO
CORE = G.CORE
SCRATCH = os.environ.get("REGEN_SCRATCH",
                         "/private/tmp/claude-501/-Users-enan-Documents-bbchallenge-proofs/"
                         "cf6f9179-4bab-4e6b-9f6c-ff143cc5776c/scratchpad/gen")

CASES = {
    "9": ("1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB", "R"),
    "13": ("1RB1RC_1LC0RC_0RA0LD_0LE---_0LF1LD_1LC1LE", "L"),
    "14": ("1RB1LC_1RC---_1LD1LC_1RE0LC_1RF0RE_1RA0RD", "L"),
    "16": ("1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---", "R"),
}


def strip_comments(text):
    """Remove /- ... -/ block comments and -- line comments and blank lines,
    for a structural (def/theorem-level) comparison."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    out = []
    for line in text.splitlines():
        line = re.sub(r"--.*$", "", line)
        if line.strip():
            out.append(line.rstrip())
    return "\n".join(out)


def main():
    os.makedirs(SCRATCH, exist_ok=True)
    all_ok = True
    for N, (code, orient) in CASES.items():
        sp = G.Spec(code, orient, N)
        gen = G.build_lean(sp)
        genpath = os.path.join(SCRATCH, f"Dossier{N}RawTM.gen.lean")
        open(genpath, "w", encoding="utf-8").write(gen)
        committed = open(os.path.join(CORE, f"Dossier{N}RawTM.lean"), encoding="utf-8").read()
        cs, gs = strip_comments(committed), strip_comments(gen)
        match = cs == gs
        all_ok = all_ok and match
        print(f"=== d{N}: probe={sp.P}{sp.probe_read} orient={orient} "
              f"variant={sp.variant} conv={sp.conv} doors={sp.doors}")
        print(f"    code-structural match (comments ignored): {match}")
        if not match:
            # show a compact diff of the stripped versions
            import difflib
            cl, gl = cs.splitlines(), gs.splitlines()
            diff = list(difflib.unified_diff(cl, gl, "committed", "generated", lineterm=""))
            print("\n".join(diff[:80]))
    print()
    print("ALL FOUR STRUCTURALLY IDENTICAL" if all_ok else "MISMATCHES REMAIN")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())

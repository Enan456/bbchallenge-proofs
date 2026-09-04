#!/usr/bin/env python3
"""Local Palomar pre-submission validator.

Mechanically re-implements the intake checks of the Palomar registry
(palomar-registry.org; policy at PalomarRegistry/PalomarPolicy@CONTRIBUTING.md)
for the three Challenge/Solution entries in packages/dossier1:

  * comparator.json shape: exactly the required keys, permitted_axioms a
    subset of {propext, Quot.sound, Classical.choice}, nonempty theorem list;
  * Challenge limits: <= 1000 lines / 100 KiB (warning above 300 / 32 KiB),
    and an EMPTY import list (core-only transitive closure);
  * Challenge/Solution declaration match: every top-level declaration chunk
    of the Challenge (defs, inductives, structures with their docstrings)
    must appear verbatim, in order, in the Solution; every sorried Challenge
    theorem's signature must appear verbatim with a non-sorry proof;
  * formalization.yaml: the mechanically required fields and the
    original/source-based provenance alternative;
  * lean-toolchain >= v4.28.0 in leanprover/lean4:<version> form, lakefile +
    lake-manifest.json present;
  * root LICENSE presence (expected to FAIL until the owner picks one).

This mirrors, but does not replace, Palomar's server-side pipeline: the
authoritative statement/type comparison is done by Comparator (kernel +
NanoDa replay) at submission time.  What this script adds locally is the
structural layer, on top of `lake build` (which elaborates both modules) and
the `#print axioms` gate in scripts/check_lean.sh.

Run from the repo root: ./.venv/bin/python scripts/check_palomar.py
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

import yaml

REPO = pathlib.Path(__file__).resolve().parents[1]
PKG = REPO / "packages" / "dossier1"

ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
REQUIRED_KEYS = {"challenge_module", "solution_module", "theorem_names",
                 "permitted_axioms"}
OPTIONAL_KEYS = {"definition_names", "enable_nanoda"}

# Generated raw-step closures (phase-2.2 batch); grown incrementally as each
# machine goes green.
NEW_DOSSIERS: list[int] = [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 100]

ENTRIES = [
    ("antihydra", "comparator-antihydra.json",
     "palomar-meta/antihydra/formalization.yaml"),
    ("incision", "comparator-incision.json",
     "palomar-meta/incision/formalization.yaml"),
    ("dossier1", "comparator-dossier1.json",
     "palomar-meta/dossier1/formalization.yaml"),
    ("dossier2cryptid", "comparator-dossier2cryptid.json",
     "palomar-meta/dossier2cryptid/formalization.yaml"),
    ("dossier3cryptid", "comparator-dossier3cryptid.json",
     "palomar-meta/dossier3cryptid/formalization.yaml"),
    ("dvisetu", "comparator-dvisetu.json",
     "palomar-meta/dvisetu/formalization.yaml"),
    ("rank1", "comparator-rank1.json",
     "palomar-meta/rank1/formalization.yaml"),
] + [
    (f"dossier{n}", f"comparator-dossier{n}.json",
     f"palomar-meta/dossier{n}/formalization.yaml")
    for n in list(range(7, 19)) + NEW_DOSSIERS
]

failures: list[str] = []
warnings: list[str] = []


def fail(msg: str) -> None:
    failures.append(msg)
    print(f"  FAIL  {msg}")


def warn(msg: str) -> None:
    warnings.append(msg)
    print(f"  warn  {msg}")


def ok(msg: str) -> None:
    print(f"  ok    {msg}")


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)  # block/doc comments
    src = re.sub(r"--[^\n]*", "", src)
    return src


DECL_RE = re.compile(r"^(def|inductive|structure|theorem|abbrev)\s+(\S+)",
                     re.MULTILINE)


def decl_chunks(src: str):
    """Split the comment-stripped namespace body into per-declaration
    chunks: (kind, name, token list)."""
    body = strip_comments(src)
    matches = list(DECL_RE.finditer(body))
    chunks = []
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(body)
        text = body[m.start():end]
        # drop a trailing 'end <ns>' if captured
        text = re.sub(r"\bend\s+\S+\s*$", "", text)
        chunks.append((m.group(1), m.group(2), text.split()))
    return chunks


def find_sublist(hay: list[str], needle: list[str], start: int) -> int:
    """Index just past the first occurrence of needle in hay at or after
    start, or -1."""
    n = len(needle)
    for i in range(start, len(hay) - n + 1):
        if hay[i:i + n] == needle:
            return i + n
    return -1


def module_path(module: str) -> pathlib.Path:
    return PKG / (module.replace(".", "/") + ".lean")


def check_entry(name: str, cfg_rel: str, meta_rel: str) -> None:
    print(f"== entry: {name}")
    cfg_path = PKG / cfg_rel

    # --- comparator.json shape
    cfg = json.loads(cfg_path.read_text())
    keys = set(cfg)
    if not REQUIRED_KEYS <= keys:
        fail(f"{cfg_rel}: missing keys {REQUIRED_KEYS - keys}")
    if keys - REQUIRED_KEYS - OPTIONAL_KEYS:
        fail(f"{cfg_rel}: unexpected keys {keys - REQUIRED_KEYS - OPTIONAL_KEYS}")
    if not cfg["theorem_names"]:
        fail(f"{cfg_rel}: theorem_names empty")
    bad_ax = set(cfg["permitted_axioms"]) - ALLOWED_AXIOMS
    if bad_ax:
        fail(f"{cfg_rel}: axioms outside Palomar's allowed set: {bad_ax}")
    else:
        ok(f"comparator config shape valid; axioms {cfg['permitted_axioms']}")

    # --- challenge limits + imports
    ch_path = module_path(cfg["challenge_module"])
    ch_src = ch_path.read_text()
    n_lines, n_bytes = len(ch_src.splitlines()), len(ch_src.encode())
    if n_lines > 1000 or n_bytes > 100 * 1024:
        fail(f"challenge exceeds hard limit: {n_lines} lines / {n_bytes} B")
    elif n_lines > 300 or n_bytes > 32 * 1024:
        warn(f"challenge above audit-comfort threshold: {n_lines} lines")
    else:
        ok(f"challenge size {n_lines} lines / {n_bytes} B")
    if re.search(r"^import ", ch_src, re.MULTILINE):
        fail("challenge has imports (must be core-only)")
    else:
        ok("challenge imports: none (Lean core only)")

    # --- challenge/solution declaration match
    sol_src = module_path(cfg["solution_module"]).read_text()
    sol_tokens = strip_comments(sol_src).split()
    short_names = {t.split(".")[-1] for t in cfg["theorem_names"]}
    pos = 0
    for kind, dname, tokens in decl_chunks(ch_src):
        if kind == "theorem":
            if tokens[-1] != "sorry" or tokens[-2] != ":=":
                fail(f"challenge theorem {dname} is not sorried")
                continue
            sig = tokens[:-1]  # keep ':=', drop 'sorry'
            newpos = find_sublist(sol_tokens, sig, pos)
            if newpos < 0:
                fail(f"solution lacks verbatim signature of theorem {dname}")
            else:
                after = sol_tokens[newpos:newpos + 1]
                if after == ["sorry"]:
                    fail(f"solution proof of {dname} is sorry")
                else:
                    ok(f"theorem {dname}: signature matched, proof non-sorry")
                pos = newpos
            short_names.discard(dname)
        else:
            newpos = find_sublist(sol_tokens, tokens, pos)
            if newpos < 0:
                fail(f"solution lacks verbatim {kind} {dname}")
            else:
                pos = newpos
    if short_names:
        fail(f"theorem_names not found among sorried challenge theorems: "
             f"{short_names}")
    else:
        ok("all compared theorems are sorried in challenge & matched in solution")

    # --- formalization.yaml
    meta_path = PKG / meta_rel
    if meta_path.name != "formalization.yaml":
        fail(f"{meta_rel}: basename must be formalization.yaml")
    meta = yaml.safe_load(meta_path.read_text())
    proj = meta.get("project", {})
    for field in ("name", "description", "authors", "license",
                  "responsible_maintainers"):
        if not proj.get(field):
            fail(f"{meta_rel}: project.{field} missing/empty")
    if len(proj.get("description", "")) > 10_000:
        fail(f"{meta_rel}: description over 10,000 chars")
    cls = meta.get("classification", {})
    if not (1 <= len(cls.get("arxiv", [])) <= 8):
        fail(f"{meta_rel}: classification.arxiv needs 1-8 codes")
    am = meta.get("automation", {}).get("methods", [])
    if not am or not all(m.get("method") for m in am):
        fail(f"{meta_rel}: automation.methods invalid")
    if not meta.get("review", {}).get("status"):
        fail(f"{meta_rel}: review.status missing")
    sources = meta.get("sources", [])
    rels = {"formalizes", "adapts", "independently-proves", "background",
            "other"}
    if not sources or not all(
            s.get("title") and s.get("relationship") in rels for s in sources):
        fail(f"{meta_rel}: sources missing/invalid")
    originals = [s for s in sources if s.get("type") == "original-proof"]
    substantive = [s for s in sources if s.get("relationship") in
                   ("formalizes", "adapts", "independently-proves")]
    if originals:
        if substantive or any(s.get("relationship") != "other"
                              for s in originals):
            fail(f"{meta_rel}: original-proof mixed with substantive "
                 "relationships")
        else:
            ok("provenance: original (valid)")
    elif substantive:
        ok("provenance: source-based (valid)")
    else:
        fail(f"{meta_rel}: satisfies neither provenance alternative")


def check_project() -> None:
    print("== project-level")
    tc = (PKG / "lean-toolchain").read_text().strip()
    m = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(-rc\d+)?", tc)
    if not m:
        fail(f"lean-toolchain not in release form: {tc}")
    else:
        ver = tuple(int(x) for x in m.groups()[:3])
        if ver < (4, 28, 0):
            fail(f"toolchain {tc} older than Palomar minimum v4.28.0")
        elif m.group(4):
            warn(f"toolchain {tc} is a release candidate")
        else:
            ok(f"toolchain {tc} (>= v4.28.0)")
    for f in ("lakefile.toml", "lake-manifest.json"):
        if (PKG / f).exists():
            ok(f"{f} present")
        else:
            fail(f"{f} missing")
    lic = [p for p in REPO.iterdir() if p.name.upper().split(".")[0] in
           ("LICENSE", "LICENCE", "COPYING", "UNLICENSE", "OFL")]
    if lic:
        ok(f"root licence file: {lic[0].name}")
    else:
        fail("root LICENSE missing (BLOCKER: owner must choose an SPDX "
             "licence; formalization.yaml proposes MIT)")


def main() -> int:
    check_project()
    for entry in ENTRIES:
        check_entry(*entry)
    print()
    print(f"{len(failures)} failure(s), {len(warnings)} warning(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

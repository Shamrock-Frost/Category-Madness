#!/usr/bin/env python3
"""Build forest/registry.json from the trees in forest/ (the decision registry, D-WF-02).

The trees are primary; this file is a derived index for CI (scripts/forest_check.py,
scripts/check_citations.py) and for the retrieval MCP (mcp/). CI verifies that the
checked-in registry equals the output of this script.

Usage:  python3 scripts/build_registry.py [--check]
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FOREST = ROOT / "forest"
OUT = FOREST / "registry.json"

META_RE = re.compile(r"^\\meta\{([^}]+)\}\{(.*)\}$", re.M)
TITLE_RE = re.compile(r"^\\title\{(.*)\}$", re.M)
TAXON_RE = re.compile(r"^\\taxon\{(.*)\}$", re.M)
TAG_RE = re.compile(r"^\\tag\{(.*)\}$", re.M)
REF_RE = re.compile(r"\\(?:ref|transclude)\{([^}]+)\}")

ADDRESS_SCHEME = {
    "decision": "D-<AREA>-<nn> -> dec-<area>-<nnnn>",
    "acceptance-test": "AT-<AREA>-<n> -> at-<area>-<nnnn>",
    "open-question": "OQ-<AREA>-<n> -> oq-<area>-<nnnn>",
    "milestone": "M<n> -> ms-<nnnn>; phase -1 -> ms-design",
    "chapter": "<area>-0000 (ch, krn, rt, up, ft, sp, tl, wf, rm, bib, rev)",
    "reference": "bib-<nnnn> in document order",
    "workflow-notes": "wf-<nnnn> (wf-0001 is the porting report)",
    "generated-declaration": "lean-<hash8> (D-WF-01, not yet produced)",
}


def strip_markup(s: str) -> str:
    """Reduce forester inline markup to plain text for titles."""
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r"\\(?:code|strong|em)\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\ref\{([^}]+)\}", r"\1", s)
    return s


def parse_tree(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    meta = {k: strip_markup(v) for k, v in META_RE.findall(text)}
    title = TITLE_RE.search(text)
    taxon = TAXON_RE.search(text)
    addr = path.stem
    refs = sorted({r for r in REF_RE.findall(text) if r != addr})
    node = {
        "id": meta.get("id", addr),
        "taxon": taxon.group(1) if taxon else None,
        "title": strip_markup(title.group(1)) if title else addr,
        "tags": TAG_RE.findall(text),
        "meta": meta,
        "status": meta.get("status"),
        "refs": refs,
        "file": str(path.relative_to(ROOT)),
    }
    if node["taxon"] == "Decision":
        node["acceptance"] = [r for r in refs if r.startswith("at-")]
    return node


def build() -> dict:
    nodes = {p.stem: parse_tree(p) for p in sorted(FOREST.glob("*.tree"))}
    # reverse index (dependents / backlinks), D-WF-02 "affected declarations" will join this
    backlinks: dict[str, list[str]] = {a: [] for a in nodes}
    for a, n in nodes.items():
        for r in n["refs"]:
            if r in backlinks:
                backlinks[r].append(a)
    for a, n in nodes.items():
        n["backlinks"] = sorted(backlinks[a])
    by_id = {n["id"]: a for a, n in nodes.items() if n["id"] != a}
    return {"address-scheme": ADDRESS_SCHEME, "id-to-address": dict(sorted(by_id.items())), "nodes": nodes}


def main() -> int:
    reg = build()
    text = json.dumps(reg, indent=2, ensure_ascii=False) + "\n"
    if "--check" in sys.argv:
        current = OUT.read_text(encoding="utf-8") if OUT.exists() else ""
        if current != text:
            print("forest/registry.json is stale; run scripts/build_registry.py", file=sys.stderr)
            return 1
        print("registry up to date:", len(reg["nodes"]), "nodes")
        return 0
    OUT.write_text(text, encoding="utf-8")
    print("wrote", OUT.relative_to(ROOT), "with", len(reg["nodes"]), "nodes")
    return 0


if __name__ == "__main__":
    sys.exit(main())

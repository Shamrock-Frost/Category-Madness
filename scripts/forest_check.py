#!/usr/bin/env python3
"""Structural checks on the forest (D-WF-02, D-WF-03). Run in CI.

  * every \\ref / \\transclude target exists;
  * braces balance in every tree (forester would reject the file otherwise);
  * every Decision node carries the D-WF-02 fields (id, status, origin, supersedes,
    superseded-by) and its status is one of frozen / provisional / later / superseded;
  * nothing references a superseded decision (D-WF-02: "CI checks that cited nodes exist
    and are not superseded");
  * every Acceptance test node has a revision-aware lifecycle status;
  * forest/registry.json is up to date with the trees.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FOREST = ROOT / "forest"

REF_RE = re.compile(r"\\(?:ref|transclude)\{([^}]+)\}")
META_RE = re.compile(r"^\\meta\{([^}]+)\}\{(.*)\}$", re.M)
TAXON_RE = re.compile(r"^\\taxon\{(.*)\}$", re.M)

DECISION_STATUSES = {"frozen", "provisional", "later", "superseded"}
AT_STATUSES = {"proposed", "stated", "proved", "failed", "blocked", "deferred", "retired"}
REQUIRED_DECISION_META = {"id", "status", "origin", "supersedes", "superseded-by"}


def main() -> int:
    errors: list[str] = []
    trees = {p.stem: p.read_text(encoding="utf-8") for p in sorted(FOREST.glob("*.tree"))}
    if not trees:
        errors.append("no trees found under forest/")

    superseded: set[str] = set()
    for addr, text in trees.items():
        meta = dict(META_RE.findall(text))
        taxon = TAXON_RE.search(text)
        taxon = taxon.group(1) if taxon else ""
        if taxon == "Decision" and meta.get("status") == "superseded":
            superseded.add(addr)

    for addr, text in trees.items():
        depth = 0
        for i, ch in enumerate(text):
            depth += ch == "{"
            depth -= ch == "}"
            if depth < 0:
                errors.append(f"{addr}: unbalanced braces at offset {i}")
                break
        if depth > 0:
            errors.append(f"{addr}: {depth} unclosed brace(s)")
        meta = dict(META_RE.findall(text))
        taxon = TAXON_RE.search(text)
        taxon = taxon.group(1) if taxon else ""
        if not re.search(r"^\\title\{", text, re.M):
            errors.append(f"{addr}: missing \\title")
        if taxon == "Decision":
            missing = REQUIRED_DECISION_META - meta.keys()
            if missing:
                errors.append(f"{addr}: decision missing meta {sorted(missing)}")
            if meta.get("status") not in DECISION_STATUSES:
                errors.append(f"{addr}: decision status {meta.get('status')!r} not in {sorted(DECISION_STATUSES)}")
            if meta.get("status") == "superseded" and meta.get("superseded-by", "none") == "none":
                errors.append(f"{addr}: superseded decision must name superseded-by")
        if taxon == "Acceptance test" and meta.get("status") not in AT_STATUSES:
            errors.append(f"{addr}: acceptance-test status {meta.get('status')!r} not in {sorted(AT_STATUSES)}")
        for target in REF_RE.findall(text):
            if target not in trees:
                errors.append(f"{addr}: reference to unknown node {target}")
            elif target in superseded and addr not in superseded:
                errors.append(f"{addr}: cites superseded decision {target}")

    res = subprocess.run([sys.executable, str(ROOT / "scripts" / "build_registry.py"), "--check"], capture_output=True, text=True)
    if res.returncode != 0:
        errors.append(res.stderr.strip() or res.stdout.strip())

    for e in errors:
        print("error:", e, file=sys.stderr)
    print(f"forest_check: {len(trees)} trees, {len(errors)} error(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

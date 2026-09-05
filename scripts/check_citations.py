#!/usr/bin/env python3
"""D-WF-02 / D-WF-04 (3): PRs must cite the decision nodes they rely on; CI checks that the
cited nodes exist and are not superseded.

Usage:
    python3 scripts/check_citations.py <file-with-PR-body-or-commit-messages>
    git log --format=%B origin/prima-materia..HEAD | python3 scripts/check_citations.py -

Citations are recognised in either form: the identifier (D-RT-16, AT-FD-1, OQ-SP-1, M-F)
or the forest address (dec-rt-0003, at-kr-0002, …). At least one decision citation is
required; unknown or superseded citations fail.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "forest" / "registry.json"

ID_RE = re.compile(r"\b(?:D|AT|OQ)-[A-Z]{2}-\d+\b")
MILESTONE_RE = re.compile(r"\bM(?:-F|[0-7])\b")
ADDR_RE = re.compile(r"\b(?:dec|at|oq)-[a-z]{2}-\d{4}\b|\bms-(?:\d{4}|design|foundation)\b")


def normalise_id(ident: str) -> str:
    kind, area, n = ident.split("-")
    return f"{kind}-{area}-{int(n):02d}" if kind == "D" else f"{kind}-{area}-{int(n)}"


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    text = sys.stdin.read() if sys.argv[1] == "-" else Path(sys.argv[1]).read_text(encoding="utf-8")
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))
    nodes, by_id = reg["nodes"], reg["id-to-address"]

    cited: set[str] = set(ADDR_RE.findall(text))
    unknown: list[str] = []
    for ident in ID_RE.findall(text):
        addr = by_id.get(normalise_id(ident))
        if addr:
            cited.add(addr)
        else:
            unknown.append(ident)
    for ident in MILESTONE_RE.findall(text):
        cited.add("ms-foundation" if ident == "M-F" else f"ms-{int(ident[1:]):04d}")
    unknown += [a for a in cited if a not in nodes]
    superseded = [a for a in cited if a in nodes and nodes[a]["status"] == "superseded"]
    decisions = [a for a in cited if a in nodes and nodes[a]["taxon"] == "Decision"]

    ok = not unknown and not superseded and decisions
    for a in unknown:
        print(f"error: cited node does not exist: {a}", file=sys.stderr)
    for a in superseded:
        print(f"error: cited decision is superseded: {a} -> {nodes[a]['meta'].get('superseded-by')}", file=sys.stderr)
    if not decisions:
        print("error: no decision node cited (D-WF-04 (3): a PR must cite the decisions it relies on)", file=sys.stderr)
    print("cited:", ", ".join(sorted(cited)) or "nothing")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

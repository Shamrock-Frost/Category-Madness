#!/usr/bin/env python3
"""Validate design-revision lineage and acceptance records (D-WF-09/10/13)."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DESIGN = ROOT / "design"
FOREST = ROOT / "forest"
CROSSWALK = DESIGN / "decision-supersession.json"
REGISTRY = FOREST / "registry.json"
META_RE = re.compile(r"^\\meta\{([^}]+)\}\{(.*)\}$", re.M)
DECISION_RE = re.compile(r"^### (D-[A-Z]{2}-\d+) · ", re.M)
AT_STATUSES = {"proposed", "stated", "proved", "failed", "blocked", "deferred", "retired"}


def address(ident: str) -> str:
    kind, area, number = ident.split("-")
    prefix = {"D": "dec", "AT": "at", "OQ": "oq"}[kind]
    return f"{prefix}-{area.lower()}-{int(number):04d}"


def metadata(path: Path) -> dict[str, str]:
    return dict(META_RE.findall(path.read_text(encoding="utf-8")))


def main() -> int:
    errors: list[str] = []
    crosswalk = json.loads(CROSSWALK.read_text(encoding="utf-8"))
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    nodes = registry["nodes"]
    by_id = registry["id-to-address"]

    if crosswalk.get("revision") != 1:
        errors.append("decision crosswalk must identify revision 1")

    pairs = crosswalk.get("supersession", [])
    old_ids = [entry["superseded"] for entry in pairs]
    current_ids = [entry["current"] for entry in pairs]
    if len(pairs) != 81 or len(set(old_ids)) != 81 or len(set(current_ids)) != 81:
        errors.append("expected 81 unique decision supersession pairs")

    for name, expected in crosswalk.get("historical_files_sha256", {}).items():
        path = DESIGN / "history" / "v0" / name
        if not path.exists():
            errors.append(f"missing historical design file: {name}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            errors.append(f"historical design hash changed: {name}")

    for entry in pairs:
        old_id, current_id = entry["superseded"], entry["current"]
        old_addr, current_addr = address(old_id), address(current_id)
        old_path, current_path = FOREST / f"{old_addr}.tree", FOREST / f"{current_addr}.tree"
        if not old_path.exists() or not current_path.exists():
            errors.append(f"missing lineage node: {old_id} -> {current_id}")
            continue
        old_meta, current_meta = metadata(old_path), metadata(current_path)
        if old_meta.get("status") != "superseded" or old_meta.get("superseded-by") != current_addr:
            errors.append(f"bad historical lineage: {old_id} -> {current_id}")
        if current_meta.get("supersedes") != old_addr or current_meta.get("superseded-by") != "none":
            errors.append(f"bad current lineage: {current_id} <- {old_id}")
        if by_id.get(old_id) != old_addr or by_id.get(current_id) != current_addr:
            errors.append(f"registry lineage mismatch: {old_id} -> {current_id}")

    active_decisions: set[str] = set()
    for path in sorted(DESIGN.glob("[0-9][0-9]-*.md")):
        active_decisions.update(DECISION_RE.findall(path.read_text(encoding="utf-8")))
    expected_current = set(current_ids) | set(crosswalk.get("new_decisions", []))
    if active_decisions != expected_current:
        missing = sorted(expected_current - active_decisions)
        extra = sorted(active_decisions - expected_current)
        errors.append(f"active decision coverage mismatch; missing={missing}, extra={extra}")

    acceptance_paths = sorted(FOREST.glob("at-*.tree"))
    for path in acceptance_paths:
        meta = metadata(path)
        if meta.get("statement-version") != "1":
            errors.append(f"{path.stem}: statement-version must be 1")
        if meta.get("status") not in AT_STATUSES:
            errors.append(f"{path.stem}: invalid acceptance status {meta.get('status')!r}")
    for ident in [f"AT-FD-{n}" for n in range(1, 12)]:
        if by_id.get(ident) != address(ident):
            errors.append(f"missing foundation gate: {ident}")
    retired = set(crosswalk.get("retired_tests", []))
    actual_retired = {metadata(path).get("id") for path in acceptance_paths if metadata(path).get("status") == "retired"}
    if actual_retired != retired:
        errors.append(f"retired test mismatch: expected={sorted(retired)}, actual={sorted(actual_retired)}")

    if any(node["file"].startswith("forest/history/") for node in nodes.values()):
        errors.append("historical forest files must not appear in the active registry")

    for error in errors:
        print("error:", error, file=sys.stderr)
    print(
        f"check_revision: {len(pairs)} lineage pairs, {len(active_decisions)} active decisions, "
        f"{len(acceptance_paths)} acceptance records, {len(errors)} error(s)"
    )
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

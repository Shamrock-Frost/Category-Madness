#!/usr/bin/env python3
"""Seal linter, job 1: the import ban (D-CH-22, D-TL-17 (1)).

No file under Theory/ may import Mathlib.CategoryTheory.*, Mathlib.AlgebraicTopology.*,
Kernel.*, or Root.*. Tactic imports (Mathlib.Tactic.*, Aesop, …) are allowed everywhere.

Additionally (D-CH-21 layering): Interface/ may import Kernel/Root (it is their public
face) but Theory/ may import only Interface.* and tactic libraries; Interface-Stub/ may
import nothing from Kernel/Root at all (it must be bodiless axioms, D-RT-28 (4)).

Runs against empty directories at M0 and simply passes.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

BANNED_IN_THEORY = (
    "Mathlib.CategoryTheory",
    "Mathlib.AlgebraicTopology",
    "Kernel",
    "Root",
)
BANNED_IN_STUB = ("Kernel", "Root", "Mathlib.CategoryTheory", "Mathlib.AlgebraicTopology")

IMPORT_RE = re.compile(r"^\s*import\s+(\S+)", re.M)


def banned(module: str, prefixes: tuple[str, ...]) -> bool:
    return any(module == p or module.startswith(p + ".") for p in prefixes)


def scan(directory: Path, prefixes: tuple[str, ...], label: str) -> list[str]:
    errors = []
    if not directory.exists():
        return errors
    for path in sorted(directory.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for m in IMPORT_RE.finditer(text):
            if banned(m.group(1), prefixes):
                line = text[: m.start()].count("\n") + 1
                errors.append(f"{path.relative_to(ROOT)}:{line}: {label} imports {m.group(1)}")
    return errors


def main() -> int:
    errors = scan(ROOT / "Theory", BANNED_IN_THEORY, "Theory/ (sealed, D-CH-22)")
    errors += scan(ROOT / "Interface-Stub", BANNED_IN_STUB, "Interface-Stub/ (must be bodiless, D-RT-28)")
    for e in errors:
        print("error:", e, file=sys.stderr)
    print(f"check_imports: {len(errors)} violation(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

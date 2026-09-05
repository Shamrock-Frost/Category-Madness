#!/usr/bin/env python3
"""Seal linter, job 3: statement hygiene (D-RT-28 (3), D-TL-17 (3)).

Every exported theorem in Interface/ is stated purely in interface vocabulary: a CI grep
enforces that Interface/ mentions no kernel or Mathlib category-theory names in
statements. This script is that grep. It looks at the *signature* part of each
declaration (everything before `:=` / `where` / `by`), so that proofs in Interface/,
which legitimately use Root/Kernel lemmas, are not flagged.

Banned name prefixes in signatures: CategoryTheory., SSet, SimplexCategory, Kernel., Root.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INTERFACE = ROOT / "Interface"

BANNED = re.compile(r"\b(?:CategoryTheory\.\w+|SSet\b|SimplexCategory\b|SimplicialObject\b|Kernel\.\w+|Root\.\w+)")
DECL_START = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*(theorem|lemma|def|abbrev|opaque|axiom|structure|class|instance|inductive)\b")
BODY_START = re.compile(r"(?<![:<>=!])(:=|\bwhere\b|\bby\b|\|\s)")


def signatures(text: str):
    """Yield (lineno, signature text) for each declaration."""
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        if DECL_START.match(lines[i]):
            start = i
            buf = []
            while i < len(lines):
                code = lines[i].split("--", 1)[0]
                m = BODY_START.search(code)
                if m:
                    buf.append(code[: m.start()])
                    break
                buf.append(code)
                i += 1
                if i < len(lines) and (DECL_START.match(lines[i]) or not lines[i].strip()):
                    break
            yield start + 1, " ".join(buf)
        i += 1


def main() -> int:
    errors: list[str] = []
    if INTERFACE.exists():
        for path in sorted(INTERFACE.rglob("*.lean")):
            for lineno, sig in signatures(path.read_text(encoding="utf-8")):
                for m in BANNED.finditer(sig):
                    errors.append(f"{path.relative_to(ROOT)}:{lineno}: signature mentions {m.group(0)}")
    for e in errors:
        print("error:", e, file=sys.stderr)
    print(f"check_statement_hygiene: {len(errors)} violation(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

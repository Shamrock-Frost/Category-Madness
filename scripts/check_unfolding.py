#!/usr/bin/env python3
"""Seal linter, job 2: the unfolding ban (D-TL-06 (2)) — syntax-level approximation.

D-TL-06 (2) calls for a Lean linter over syntax plus an Expr-level check that no proof
term in Theory/ references a `_def` lemma or a kernel constant. The Lean linter does not
exist yet (it is Lean code, scheduled with the seal at M3). Until then this script rejects
the textual forms that can never be legitimate in Theory/:

    unseal …            with_unfolding_all       delta …
    rw [foo_def]        simp [… foo_def …]       unfold <name> where <name> is sealed
    set_option … in ways that defeat the seal (e.g. `pp.all`-style is fine; unfolding is not)

Sealed names are read from Interface/SEALED (one constant per line, generated with the
interface at M3; empty now). The Expr-level check remains a TODO owned by D-TL-06.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEORY = ROOT / "Theory"
SEALED_LIST = ROOT / "Interface" / "SEALED"

ALWAYS_BANNED = [
    (re.compile(r"\bunseal\b"), "unseal"),
    (re.compile(r"\bwith_unfolding_all\b"), "with_unfolding_all"),
    (re.compile(r"(?<![\w.])delta\b"), "delta"),
    (re.compile(r"\b\w+_def\b(?!\s*:)"), "reference to a *_def equation lemma"),
    (re.compile(r"\bset_option\s+(?:pp\.proofs|autoImplicit)\s+true\b"), "banned set_option"),
]


def sealed_names() -> list[str]:
    if not SEALED_LIST.exists():
        return []
    return [l.strip() for l in SEALED_LIST.read_text(encoding="utf-8").splitlines() if l.strip() and not l.startswith("#")]


def main() -> int:
    errors: list[str] = []
    sealed = sealed_names()
    sealed_re = None
    if sealed:
        names = "|".join(re.escape(n) for n in sealed)
        sealed_re = re.compile(rf"\b(?:unfold|simp|dsimp|delta)\b[^\n]*\[[^\]]*\b(?:{names})\b")
    if THEORY.exists():
        for path in sorted(THEORY.rglob("*.lean")):
            for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                code = line.split("--", 1)[0]
                for rx, what in ALWAYS_BANNED:
                    if rx.search(code):
                        errors.append(f"{path.relative_to(ROOT)}:{lineno}: {what}")
                if sealed_re and sealed_re.search(code):
                    errors.append(f"{path.relative_to(ROOT)}:{lineno}: unfolds a sealed constant")
    for e in errors:
        print("error:", e, file=sys.stderr)
    print(f"check_unfolding: {len(errors)} violation(s) ({len(sealed)} sealed names known)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

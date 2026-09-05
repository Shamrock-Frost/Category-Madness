#!/usr/bin/env python3
"""AT-FD-2 builds, signatures, compiled audits and timings.

Cites: D-RT-28, D-TL-17, D-TL-18, AT-FD-2, AT-FD-11.
The isolated stub shares only third-party packages, never project build products.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "build" / "seal"


def run(args: list[str], cwd: Path, label: str, *, expect: str | None = None,
        env: dict[str, str] | None = None) -> float:
    start = time.perf_counter()
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.perf_counter() - start
    (OUT / f"{label}.log").write_text(result.stdout, encoding="utf-8")
    if expect is None:
        if result.returncode:
            raise RuntimeError(f"{label} failed:\n{result.stdout}")
    elif result.returncode == 0 or expect not in result.stdout:
        raise RuntimeError(f"{label}: expected failure containing {expect!r}:\n{result.stdout}")
    print(f"{label}: {'rejected as expected' if expect else 'passed'} ({elapsed:.3f}s)", flush=True)
    return elapsed


def audit(cwd: Path, mode: str) -> dict:
    path = cwd / "SealAudit.lean"
    path.write_text('import Prototype.Audit\nimport Theory\nimport Prototype.Universes\n'
                    f'#audit_seal "{mode}"\n', encoding="utf-8")
    report = OUT / f"{mode}.json"
    try:
        run(["lake", "env", "lean", str(path)], cwd, f"{mode}-audit",
            env={**os.environ, "SEAL_AUDIT_OUTPUT": str(report)})
    finally:
        path.unlink()
    return json.loads(report.read_text(encoding="utf-8"))


def signatures(report: dict) -> list[tuple]:
    return [(d["name"], d["levels"], d["type"]) for d in report["declarations"]]


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    if not list((ROOT / "Theory").rglob("*.lean")):
        raise RuntimeError("a nonempty Theory client is required")
    timings = {}
    timings["implementation_build"] = run(["lake", "build"], ROOT, "implementation-build")
    run(["lake", "build", "Audit"], ROOT, "audit-build")
    implementation = audit(ROOT, "implementation")
    fixtures = {"ProjectAxiom": "SEAL_AXIOM", "Sorry": "SEAL_AXIOM",
                "PrivateLeak": "SEAL_LEAK", "ImplementationEquation": "rfl"}
    for name, diagnostic in fixtures.items():
        run(["lake", "env", "lean", f"Prototype/Negative/{name}.lean"], ROOT,
            f"implementation-negative-{name}", expect=diagnostic)
    run(["lake", "env", "lean", "Prototype/Negative/StubAxiom.lean"], ROOT,
        "implementation-stub-axiom-control")
    with tempfile.TemporaryDirectory(prefix="stub-", dir=OUT) as temporary:
        stub = Path(temporary)
        shutil.copytree(ROOT, stub, dirs_exist_ok=True,
                        ignore=shutil.ignore_patterns(".git", ".lake", "build", "__pycache__"))
        for source in (ROOT / "Interface-Stub").rglob("*.lean"):
            destination = stub / "Interface" / source.relative_to(ROOT / "Interface-Stub")
            if not destination.is_file():
                raise RuntimeError(f"stub has no implementation counterpart: {source}")
            shutil.copyfile(source, destination)
        packages = ROOT / ".lake" / "packages"
        if packages.is_dir():
            (stub / ".lake").mkdir()
            (stub / ".lake" / "packages").symlink_to(packages, target_is_directory=True)
        timings["stub_build"] = run(["lake", "build", "Theory", "Foundation", "Audit"], stub,
                                     "stub-build")
        stub_report = audit(stub, "stub")
        if signatures(implementation) != signatures(stub_report):
            raise RuntimeError("implementation/stub declaration names, universes or types differ")
        for name, diagnostic in {**fixtures, "StubAxiom": "SEAL_AXIOM"}.items():
            run(["lake", "env", "lean", f"Prototype/Negative/{name}.lean"], stub,
                f"stub-negative-{name}", expect=diagnostic)
        timings["stub_client"] = run(["lake", "env", "lean", "Theory/Prototype/Monoid.lean"],
                                      stub, "stub-client")
    timings["implementation_client"] = run(
        ["lake", "env", "lean", "Theory/Prototype/Monoid.lean"], ROOT, "implementation-client")
    summary = {"result": "passed", "declarations": len(implementation["declarations"]),
               "signatures_identical": True, "negative_checks": 9,
               "timings_seconds": timings}
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("seal: both builds, identical signatures, audits and nine negative checks passed")


if __name__ == "__main__":
    main()

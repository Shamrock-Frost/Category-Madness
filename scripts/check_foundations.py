#!/usr/bin/env python3
"""Verify the pinned inventory, axiom audit, and minimal forest export round-trip.
Cites: D-KR-14, D-KR-18, D-CH-20, D-WF-08, D-WF-10, AT-KR-0, AT-FD-1, AT-FD-7.

Builds the audited targets. --write refreshes derived evidence; the default checks it.
The existing sorry fixture is elaborated in a separate temporary source, never
imported by Foundations or by the successful foundation audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "build/foundation-inventory"
MATHLIB = ROOT / ".lake/packages/mathlib"
SNAPSHOT = ROOT / "docs/foundations/inventory.json"
SIGNATURES = ROOT / "docs/foundations/signatures.md"
FIXTURE = ROOT / "Prototype/Negative/Sorry.lean"
AUDIT = ROOT / "scripts/FoundationAudit.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(*args: str, env: dict | None = None) -> str:
    result = subprocess.run(args, cwd=ROOT, env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{' '.join(args)} failed:\n{result.stdout}{result.stderr}")
    return result.stdout


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def serialized(value: object) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def finalize(rows: list[dict]) -> list[dict]:
    for row in rows:
        row["typeExpressionSha256"] = digest(row.pop("typeExpression").encode())
        module = row["module"]
        row["source"] = module.replace(".", "/") + ".lean" if module else None
        row["citedDecisions"] = []
        if module and not module.startswith("Mathlib."):
            source = ROOT / row["source"]
            row["citedDecisions"] = sorted(set(re.findall(r"\b(?:D|AT)-[A-Z]{2}-\d+\b", source.read_text())))
        row["flags"] = {
            "sealed": False,
            "kernel": row["name"].startswith("Kernel."),
            "root": row["name"].startswith("Root."),
            "prototype": row["name"].startswith("Prototype."),
            "dependency": module is not None and module.startswith("Mathlib."),
            "quarantined": False,
        }
    # Reverse edges are deliberately scoped to this exported inventory.
    for row in rows:
        row["reverseDependencies"] = sorted(
            other["name"] for other in rows
            if row["name"] in other["statementDependencies"] + other["proofDependencies"]
        )
    return rows


def source_scan() -> dict:
    directories = [
        "Mathlib/AlgebraicTopology/SimplicialSet",
        "Mathlib/AlgebraicTopology/Quasicategory",
        "Mathlib/AlgebraicTopology/Reedy",
    ]
    pattern = r"CategoryWithWeakEquivalences|WeakEquivalence|ModelCategory|ReedyStructure|KanComplex.*nerve|nerve.*KanComplex"
    files = sorted(p for d in directories for p in (MATHLIB / d).rglob("*.lean"))
    manifest = {str(p.relative_to(MATHLIB)): digest(p.read_bytes()) for p in files}
    matches = [
        {"source": str(p.relative_to(MATHLIB)), "line": n, "text": line.strip()}
        for p in files
        for n, line in enumerate(p.read_text().splitlines(), 1)
        if re.search(pattern, line)
    ]
    return {
        "directories": directories, "pattern": pattern, "fileCount": len(files),
        "sourceManifestSha256": digest(serialized(manifest).encode()), "matches": matches,
        "scope": "Bounded source search; not a proof of global nonexistence.",
    }


def gap_records() -> list[dict]:
    records = [
        {
            "id": "sset-model-structure",
            "source": "Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean",
            "requiredText": "Quillen model category structure (TODO)",
            "status": "upstream-todo",
            "consequence": "Cofibrations and Kan fibrations are available. The selected import closure has no SSet CategoryWithWeakEquivalences or ModelCategory instance; Inventory.lean checks both failures. Do not assume canonical weak equivalences, model factorizations, or derived homotopy limits from this pin.",
        },
        {
            "id": "reedy-diagram-model",
            "source": "Mathlib/AlgebraicTopology/Reedy/Basic.lean",
            "requiredText": "Construct the Reedy model category structure",
            "status": "upstream-todo",
            "consequence": "ReedyStructure and unique factorizations are available; a Reedy model structure on diagrams is an explicit upstream TODO. Augmented labelled arities still require their own structure and model lemmas (AT-FD-7).",
        },
    ]
    for row in records:
        source = (MATHLIB / row["source"]).read_text().splitlines()
        hits = [n for n, text in enumerate(source, 1) if row["requiredText"] in text]
        if not hits:
            raise RuntimeError(f"Gap evidence changed: {row['id']}; review the pinned inventory")
        row["lines"] = hits
    records += [
        {"id": "groupoid-nerve-kan", "status": "not-located",
         "consequence": "Ordinary nerves and strict Segal laws are available. No groupoid-nerve Kan result was located in the scanned directories, and its instance is absent from the selected imports. The ordinary groupoid example does not certify a Kan nerve."},
        {"id": "relative-derived-mapping", "status": "project-obligation",
         "consequence": "SSet.RelativeMorphism is a strict relative map with a homotopy-class API. It is not the fixed-label derived MapRel or categorical MapCat required by D-RT-23. Available restriction fibrations require an explicit mono and Kan target."},
        {"id": "augmented-arities", "status": "project-obligation",
         "consequence": "Category-of-elements machinery is available. Kernel.Augmented implements incidence, the set-level equation families, a lawful additive-label algebra, an active-map obstruction, and a supplied 2-category's binary cell model. Extending that binary model to an augmented algebra and proving the general 2-category/discrete-nerve comparison, free/arity and nerve presentation, labelled diagram model, walking nerves, coherent Mod, and small-space classifier laws remain construction obligations (AT-FD-7 and dependent gates)."},
    ]
    return records


def fixture_roundtrip(write: bool) -> dict:
    fixture_source = "\n".join(
        line for line in FIXTURE.read_text().splitlines() if not line.startswith("import ")
    )
    # Only shared exporter definitions precede the quarantined fixture.
    helper = AUDIT.read_text().split("\nrun_cmd do\n", 1)[0]
    path = OUT / "roundtrip.lean"
    raw = OUT / "roundtrip.json"
    path.write_text(helper + "\n" + fixture_source + '\nrun_cmd do\n'
                    '  FoundationExport.writeDeclarations #["Theory.unproved".toName] '
                    '"build/foundation-inventory/roundtrip.json"\n')
    run("lake", "env", "lean", str(path))
    row = json.loads(raw.read_text())[0]
    if row["status"] != "stated" or row["approvedAxioms"] or "sorryAx" not in row["axioms"]:
        raise RuntimeError("The unfinished fixture was incorrectly certified")
    if row["kind"] != "theorem":
        raise RuntimeError("The round-trip fixture must be a stated theorem")
    name = row["name"]
    addr = "lean-" + name.lower().replace(".", "-") + "-" + digest(name.encode())[:8]
    tree = (
        f"\\title{{{name} · quarantined exporter fixture}}\n"
        "\\taxon{Lean declaration}\n"
        f"\\meta{{lean-name}}{{{name}}}\n"
        "\\meta{status}{stated}\n"
        "\\meta{kind}{theorem}\n"
        f"\\meta{{type}}{{{row['type']}}}\n"
        "\\meta{axioms}{sorryAx}\n"
        "\\meta{quarantined}{true}\n"
        "\\meta{source}{Prototype/Negative/Sorry.lean}\n"
        "\\meta{generator}{scripts/check_foundations.py}\n"
        "\\tag{generated}\n\\tag{negative-fixture}\n"
        "\\p{Generated from the Lean environment for the minimal export round-trip. "
        "This unfinished statement is rejected by the axiom audit and is never imported by certified targets. "
        "It is not a mathematical result.}\n"
        "\\p{Cites: \\ref{dec-wf-0008}, \\ref{dec-wf-0010}, \\ref{at-kr-0000}.}\n"
    )
    target = ROOT / "forest" / f"{addr}.tree"
    compare_or_write(target, tree, write)
    # Parse the generated forest node back through the same parser as the registry.
    from build_registry import parse_tree
    restored = parse_tree(target)
    for key, expected in {"lean-name": name, "status": row["status"], "type": row["type"],
                          "axioms": "sorryAx", "quarantined": "true"}.items():
        if restored["meta"].get(key) != expected:
            raise RuntimeError(f"Export round-trip lost {key}")
    return {"declaration": name, "forestAddress": addr, "status": row["status"],
            "axioms": row["axioms"], "quarantined": True,
            "typeExpressionSha256": digest(row["typeExpression"].encode()),
            "sourceSha256": digest(FIXTURE.read_bytes()), "roundtrip": "passed"}


def compare_or_write(path: Path, content: str, write: bool) -> None:
    if write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    elif not path.exists() or path.read_text() != content:
        raise RuntimeError(f"{path.relative_to(ROOT)} is stale; run scripts/check_foundations.py --write")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    run("lake", "build", "Foundations", "Augmented", "Theory")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pin = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    revision = run("git", "-C", str(MATHLIB), "rev-parse", "HEAD").strip()
    if revision != pin["rev"]:
        raise RuntimeError("Mathlib checkout does not match lake-manifest.json")
    if run("git", "-C", str(MATHLIB), "status", "--porcelain", "--untracked-files=no", "--", "Mathlib").strip():
        raise RuntimeError("Mathlib sources are modified; cannot certify the pinned inventory")
    lean_version = run("lake", "env", "lean", "--version").strip()
    version = re.search(r"version ([^, ]+)", lean_version).group(1)
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if not toolchain.endswith(":v" + version):
        raise RuntimeError("The active Lean version does not match lean-toolchain")
    env = dict(os.environ, CATEGORY_MADNESS_INVENTORY_OUT=str(OUT / "raw.json"))
    audit_output = run("lake", "env", "lean", "scripts/FoundationAudit.lean", env=env)
    rows = finalize(json.loads((OUT / "raw.json").read_text()))
    if not all(r["approvedAxioms"] and set(r["axioms"]) <= ALLOWED for r in rows):
        raise RuntimeError("Unapproved dependency or project axiom in inventory")
    # These implementation modules each declare audited constants. An omitted
    # aggregate import or stale aggregate artifact must not silently skip one.
    augmented_modules = {str(p.relative_to(ROOT).with_suffix("")).replace("/", ".")
                         for p in (ROOT / "Kernel/Augmented").glob("*.lean")}
    missing_modules = augmented_modules - {r["module"] for r in rows}
    if missing_modules:
        raise RuntimeError(f"Augmented implementation missing from audit: {sorted(missing_modules)}; "
                           "check Augmented.lean imports and rebuild stale artifacts")
    sources = set([
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "Foundations.lean", "Augmented.lean",
        "scripts/FoundationAudit.lean", "scripts/check_foundations.py",
        "Prototype/Negative/Sorry.lean", "Interface/CategorySpec.lean",
        "Kernel/Matrix.lean", "Root/MatrixCategory.lean", "Prototype/MatrixCategoryExamples.lean",
        "Prototype/Universes/Matrix.lean", "Prototype/Universes/Reindex.lean",
        "Prototype/Universes/Examples.lean",
    ])
    sources.update(str(p.relative_to(ROOT)) for d in ["Kernel/Foundations", "Root/Foundations", "Kernel/Augmented"]
                   for p in (ROOT / d).glob("*.lean"))
    hashes = {p: digest((ROOT / p).read_bytes()) for p in sorted(sources)}
    dependencies = {r["source"] for r in rows if r["flags"]["dependency"]}
    for gap in gap_records():
        if "source" in gap:
            dependencies.add(gap["source"])
    dep_hashes = {p: digest((MATHLIB / p).read_bytes()) for p in sorted(dependencies)}
    evidence = {
        "schemaVersion": 1, "leanToolchain": toolchain, "leanVersion": version,
        "mathlibRevision": revision, "mathlibRequestedRevision": pin["inputRev"],
        "allowedAxioms": sorted(ALLOWED), "sourceSha256": hashes,
        "dependencySourceSha256": dep_hashes, "declarations": rows,
        "gaps": gap_records(), "sourceScan": source_scan(),
        "exportRoundtrip": fixture_roundtrip(args.write),
        "checks": ["compiled foundational signatures, augmented algebra equations and models", "scoped transitive axiom audit",
                   "exact declaration names and types from environment", "dependency pins and source hashes",
                   "bounded upstream gap evidence", "stated theorem export/parse round-trip"],
        "scope": "Initial foundation work and the early set-level part of AT-FD-7. The augmented equation families and a nontrivial lawful model are checked; the general 2-category/discrete-nerve comparison, free/arity presentation and labelled diagram model remain open. Root/walking/Mod/classifier records remain minimal type contracts with explicit inputs.",
    }
    compare_or_write(SNAPSHOT, serialized(evidence), args.write)
    signature_names = {
        "SmallSpace", "ClassifierData", "ShapeSignature", "labels", "Labelled", "Diagram",
        "liftSSet", "liftSSetHomEquiv", "liftLabelsEquivalence", "RootSignature",
        "WalkingSignature", "RelativeChoice", "MonadNerves", "MonadCollection",
        "RelativeMappingSpace", "ModSignature", "CategoryOn", "CategoryCollection",
    }
    table = [
        "# Checked universe signatures", "",
        "Generated by scripts/check_foundations.py from the Lean environment. Do not edit.", "",
        "These are minimal type contracts. Their semantic construction obligations are described in README.md.", "",
        "| Declaration | Universe parameters | Elaborated type |", "|---|---|---|",
    ]
    for row in rows:
        if row["flags"]["dependency"] or row["name"].rsplit(".", 1)[-1] not in signature_names:
            continue
        typ = " ".join(row["type"].split()).replace("|", r"\|")
        table.append(f"| {row['name']} | {', '.join(row['universeParameters'])} | {typ} |")
    compare_or_write(SIGNATURES, "\n".join(table) + "\n", args.write)
    print(audit_output.strip())
    print(f"check_foundations: {len(rows)} inventory entries, pins and sources verified; "
          "unfinished theorem remains stated after forest round-trip")
    if args.write:
        print("Regenerate forest/registry.json with scripts/build_registry.py")


if __name__ == "__main__":
    main()

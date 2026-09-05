# Category Madness

Category Madness is a Lean 4 research library exploring a common, sealed interface for
ordinary, enriched, internal, and higher category theory. The current candidate root is
a reduced augmented virtual double ∞-category. Design revision 1 keeps that root
provisional until a focused foundation-feasibility milestone tests its semantics and
implementation boundary.

**Status: M0 complete; M-F started.** The first Lean prototype covers matrix-family
universes and entry lifts. See `Prototype/Universes/README.md` for its scope and check
record. No complete foundation gate is marked proved.

## Start here

| Path | Purpose | Active reference |
|---|---|---|
| `design/11-foundation-feasibility.md` | Eleven M-F gates with dependencies, evidence, and failure responses | D-FD-01 |
| `design/12-revision-notes.md` | Review disposition, revised test scopes, and the full supersession crosswalk | revision 1 |
| `forest/index.tree` | Primary active specification and navigation | D-WF-08/09 |
| `forest/registry.json` | Derived machine-readable registry | D-WF-09 |
| `design/history/v0/` | Byte-for-byte original design archive | historical |
| `forest/history/v0/` | Forest snapshot from before revision 1 | historical |
| `Prototype/` | Small M-F experiments and negative fixtures | D-CH-25, AT-FD-* |
| `Kernel/`, `Root/`, `Interface/`, `Interface-Stub/`, `Theory/` | Three-stage implementation and seal | D-CH-21, D-RT-28 |
| `scripts/` | Port, registry, citation, seal, and trust checks | D-TL-17, D-WF-09/10 |
| `mcp/server.py` | Read-only retrieval over active forest records | D-WF-12 |

Historical decisions remain resolvable with status `superseded`, but active searches
omit them and CI rejects them as citations. Current decisions have fresh IDs recorded in
`design/decision-supersession.json`. Every acceptance record is statement version 1 and
starts at `proposed`, except retired AT-RT-4 and AT-FT-8.

## Working here

Read `AGENTS.md`, then use the active forest rather than the historical snapshots. The
first work queue is M-F (`forest/ms-foundation.tree`), starting with inventory, universe,
and seal prototypes before augmented shapes and the end-to-end nondiscrete example.

Run the local checks:

```sh
python3 scripts/forest_check.py
python3 scripts/check_imports.py
python3 scripts/check_unfolding.py
python3 scripts/check_statement_hygiene.py
python3 mcp/server.py --selftest
```

Reproduce the active forest after an authorized design revision:

```sh
python3 scripts/port_design.py
python3 scripts/build_registry.py
python3 scripts/forest_check.py
```

The Lean toolchain remains pinned in `lean-toolchain` and `lakefile.toml`. Run
`lake build` to check the default targets, including `Prototype`. CI runs on
`prima-materia`; its source detection includes M-F prototypes.

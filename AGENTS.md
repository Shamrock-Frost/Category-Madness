# AGENTS.md — operating manual

This repository is built by agents against definitions frozen by a human (D-CH-06,
D-WF-04). This file says how to work here. It is provisional (D-TL-01): amend it by PR
if the conventions stop fitting.

## 1. Find the decision before you act

Every design choice is a node in `forest/` with an ID. **Retrieve, do not re-derive**
(D-WF-05): an agent that cannot find the decision node will re-derive the decision,
usually differently.

- By ID: `D-RT-03` is `forest/dec-rt-0003.tree`; `AT-KR-2` is `forest/at-kr-0002.tree`;
  `OQ-SP-1` is `forest/oq-sp-0001.tree`; `M3` is `forest/ms-0003.tree`.
- By search: `python3 mcp/server.py` is an MCP server (`search`, `get`, `neighbors`,
  `open_tasks`, `decision`, `acceptance`); `forest/registry.json` is the index behind it.
- By reading: `forest/index.tree` → chapter trees (`ch-0000`, `krn-0000`, `rt-0000`, …).

Statuses: `frozen` decisions are not editable; change them only by adding a new decision
node that supersedes them (D-WF-02). `provisional` decisions may be amended by a PR that
edits the node and applies the change mechanically (D-TL-01). `later` means not before
the named milestone.

## 2. What a PR must do (D-WF-04 (3))

1. **Cite the decisions it relies on**, by ID or address, in the PR body. CI
   (`scripts/check_citations.py`) fails a PR that cites nothing, cites an unknown node,
   or cites a superseded decision.
2. **Add no sealed constant without a decision** (D-RT-13, two tiers: constants need a
   superseding decision; interface lemmas provable in `Root/` do not).
3. **Keep the swap test green** (`scripts/swap_test.sh`, D-TL-06 (4)).
4. **Regenerate the human layer**; never hand-edit `Generated/` (D-TL-02).
5. **Leave the forest buildable**: `python3 scripts/forest_check.py` and
   `python3 scripts/build_registry.py` (commit the updated `forest/registry.json`).
6. **Update node status** when you state or prove an acceptance test
   (`\meta{status}{stated|proved}` on the `at-*` node, D-WF-03), or resolve an open
   question (record the answer as a decision node; the question then cites it).

## 3. The seal (D-CH-09, D-RT-13, D-TL-06)

- `Theory/` imports only `Interface.*` and tactic libraries. Never
  `Mathlib.CategoryTheory.*`, `Mathlib.AlgebraicTopology.*`, `Kernel.*`, `Root.*`.
- No unfolding of sealed constants in `Theory/`: no `unseal`, `with_unfolding_all`,
  `delta`, `unfold <sealed>`, `simp [<sealed>]`, `rw [foo_def]`, no `rfl` against an
  implementation. If a proof closes by `rfl` against an implementation it is wrong for
  this library (D-CH-01).
- Universal objects are witnesses of Prop-valued universal properties; theorems
  quantify over witnesses; no `limit F` constant (D-CH-02, D-UP-06).
- Limits are shape-indexed and unbiased; no binary coherence (D-CH-03).
- Everything is universe-polymorphic; `autoImplicit false` (D-RT-12, D-TL-06 (6)).
- Definitional equality is allowed only in `Kernel/` and `Root/`.

## 4. Layout (D-TL-08)

```
design/          frozen phase −1 documents (history; do not edit)
forest/          the forest (primary); one tree per decision / AT / OQ / milestone / reference
Kernel/          stage 0: Mathlib scaffolding, shapes, Kan machinery      (-- KERNEL)
Root/            stage 1: VDC∞, Mod, Mat(Set), Category, the self-hosting theorem
Interface/       the seal: opaque / irreducible constants + API lemmas
Interface-Stub/  generated: same statements as bodiless axioms (swap test)
Theory/{UP,FT,SP}  stage 2: everything else, interface vocabulary only
Generated/       the human layer: notation, abbrevs, thin API (never hand-edited)
scripts/         linters, forest tooling, the port script
mcp/             retrieval MCP (read-only)
```

Naming: `Structure.field_property`, snake_case theorems, dot notation, no abbreviations,
theorems named for their conclusion (D-TL-08).

## 5. Picking work (D-WF-04 (2))

Pick `stated` acceptance tests and `sorry` nodes in dependency order, preferring nodes
that unblock the most dependents: `open_tasks` in the MCP sorts by that. At M0 nothing
is stated; the open work is listed in `forest/ms-0000.tree` and `forest/wf-0001.tree`.

## 6. Commit messages

Cite decisions in the body (`Cites: D-KR-06, AT-KR-8`). Do not put model identifiers
in commits, PR text, or code comments.

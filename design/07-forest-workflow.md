# 07 · Forest and workflow

The forester (v5) forest is the bookkeeping system and, after M0, the primary
human-facing document. Every non-private Lean declaration has a node. Design decisions,
acceptance tests, milestones, and open questions are nodes. Human prose is a layer of
nodes that transclude the generated ones (→ D-CH-07).

### D-WF-01 · Generated nodes
**Decision.** A Lean program (`lake exe forest-export`) walks the environment for
every module under `Kernel/`, `Root/`, `Interface/`, `Theory/` and emits one `.tree`
per non-private declaration into `build/forest/` (gitignored, rebuilt in CI). Each node has:
- title: fully qualified name; taxon from the declaration kind (`Definition`, `Theorem`,
  `Lemma`, `Structure`, `Class`, `Instance`, `Opaque`);
- the statement (pretty-printed signature in a code block) and the docstring;
- status: `proved` / `sorry` (from `collectAxioms`), plus `sealed` if in `Interface/`,
  `kernel` if in `Kernel/`;
- dependencies: nodes for each constant used in the type and, for theorems, in the proof
  (from `Expr.getUsedConstants`), split into "in statement" and "in proof";
- dependents (reverse index, computed after the walk);
- source link with line range (from `declaration_ranges`);
- the decisions it cites (from a `@[decision D-RT-03]`-style attribute or a docstring tag).
Addresses are deterministic from the name (hash-suffixed) so links survive renames of
the file layout but not of the declaration.
**Rationale.** Agents will navigate by dependency and status, not by file. Humans will
read prose that transcludes these.
**Status.** frozen (fields provisional).

### D-WF-02 · Decision registry
**Decision.** Every `D-<AREA>-<nn>` in these documents becomes a tree with fields
*decision, rationale, rejected alternatives, acceptance tests (refs), affected
declarations (backlinks from D-WF-01), status, supersedes/superseded-by, origin*.
Statuses: `frozen`, `provisional`, `later`, `superseded`. Changing a `frozen` decision
requires a new decision node that supersedes it; the old node is never edited.
PRs must cite the decision nodes they rely on; CI checks that cited nodes exist and are
not `superseded`.
**Status.** frozen.

### D-WF-03 · Acceptance-test nodes
**Decision.** Every `AT-<AREA>-<n>` becomes a tree with the informal statement, the Lean
declaration(s) once stated, and a status derived from D-WF-01 (`unstated` / `stated` /
`proved`). A definition-level decision is `validated` when all its acceptance tests are
`proved`; the registry shows this.
**Status.** frozen.

### D-WF-04 · The agent loop
**Decision.**
1. A human freezes definitions for a milestone (→ 08) by marking decisions `frozen` and
   stating the acceptance tests in Lean (`sorry` bodies are fine; statements are not).
2. Agents pick `stated` acceptance tests and `sorry` nodes, in dependency order,
   preferring nodes that unblock the most dependents.
3. A PR must: cite decisions; add no new sealed constants without a decision; keep the
   swap test green; regenerate the human layer; leave the forest buildable.
4. Definitions are not agent-editable in `frozen` areas; in `provisional` areas
   amendments go through → D-TL-01.
5. Nightly: kernel-backed full build (→ D-RT-13 (5)), forest rebuild and publish,
   benchmark nodes.
**Status.** frozen.

### D-WF-05 · Retrieval MCP
**Decision.** Yes. A read-only MCP server (`mcp/`) over the built forest and the Lean
environment, run locally by agents and humans, rebuilt in CI. Tools (MVP):
- `search(query, k, filter)`: hybrid lexical + embedding search over node bodies
  (generated and handwritten), docstrings, decision text; filters by taxon/status/area;
- `get(address)`: full node;
- `neighbors(address, direction)`: dependencies / dependents / cited decisions;
- `open_tasks(area, kind)`: `stated`/`sorry` nodes, sorted by unblocked-dependents;
- `decision(id)` and `acceptance(id)`: registry lookups with status;
- `type_search(pattern)`: Loogle-style search over the environment for the project's
  namespaces.
No write tools; changes go through PRs. Index sources: `build/forest/` plus the
handwritten `forest/`. The server is a thin wrapper; the forest is the index.
**Rationale.** An agent that cannot find the decision node will re-derive the decision,
usually differently. Retrieval at task time is how frozen decisions actually bind.
Grepping thirteen million lines is not a plan.
**Status.** frozen (MVP tool list provisional).

### D-WF-06 · Human prose as a layer
**Decision.** Handwritten trees in `forest/` are prose that transclude generated nodes
(`\transclude`) and cite decisions; they never restate a signature. These design
documents become handwritten trees at the port. Chapters mirror this document set.
**Status.** frozen.

### D-WF-07 · Addresses
**Decision.** Nested address scheme by area and sub-area, e.g. `krn-shp-0012`
(kernel/shapes), `rt-vdc-0003` (root/vdc), `up-lim-0007`, `ft-yon-0002`, `sp-univ-0001`,
`tl-lint-0004`, `wf-mcp-0001`, `dec-0031` (decisions), `at-0044` (acceptance tests),
`ms-0003` (milestones), `oq-0012` (open questions); generated declaration nodes
`lean-<hash8>`. The M0 porting agent adapts this to forester v5's addressing and records
the mapping from the `D-`/`AT-`/`OQ-` IDs used here.
**Status.** provisional.

## Porting instructions (phase −1 → M0)

1. Create the forest skeleton with the address scheme; one tree per document section
   marked `D-`, `AT-`, `OQ-`, plus one tree per milestone in → 08.
2. Preserve *Rationale* and *Rejected* verbatim; they are what future agents will search for.
3. Implement `forest-export` (D-WF-01) against an empty Lean project so the pipeline
   exists before any mathematics does.
4. Stand up the MCP MVP (D-WF-05) over the ported forest.
5. Report gaps: any decision that could not be expressed as a node with the fields of
   D-WF-02 is an open question for the human.

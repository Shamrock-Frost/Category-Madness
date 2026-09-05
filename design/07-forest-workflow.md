# 07 · Forest and workflow — revision 1

The decision registry starts at M0. The full forest export and retrieval service expand
after M-F, when declarations and proofs provide useful content. Historical decisions
remain immutable and are not active work items.

### D-WF-08 · Generated declaration nodes
**Decision.** Generate nodes from the Lean environment with qualified name, declaration
kind, pretty-printed type, docstring, source position, statement/proof dependencies,
reverse dependencies, cited decision IDs, and proof status from the axiom audit.
Exported/sealed/kernel/prototype flags are independent of proof status. A declaration
using an unapproved axiom is not “proved” for registry purposes. Deterministic addresses
include the declaration name; record rename redirects when practical.
**Rationale.** Agents need the actual dependency graph and mathematical validation state.
**Rejected.** Proof status based only on whether a source body visibly contains `sorry`.
**Acceptance.** M0 minimal round-trip; complete exporter with real M-F declarations at M1.
**Status.** frozen fields in principle; encoding provisional.

### D-WF-09 · Decision registry and supersession
**Decision.** Each decision has a stable ID, decision/rationale/rejected text, tests,
status, affected declarations, and supersession links. Revision 1 gives changed
historical decisions new IDs; `12-revision-notes.md` is the crosswalk and `history/v0/`
contains the exact old text. Current references resolve to current IDs; references to
history are explicitly marked historical. Future changes to a frozen decision also
receive a new ID. A human-authorized design revision may supersede frozen choices;
permission is not requested again for the already authorized revision.
**Rationale.** Preserve why choices changed without letting old claims govern new proofs.
**Rejected.** Reusing a frozen ID for a changed mathematical statement or deleting its rationale.
**Acceptance.** Revision crosswalk validation and M0/M-F registry audit.
**Status.** frozen policy; current provisional choices remain amendable by recorded decisions.

### D-WF-10 · Acceptance records
**Decision.** Each acceptance test records its informal scope, exact Lean declarations
when available, dependencies, statement version, and status: proposed, stated, proved,
failed, blocked, deferred, or retired. Only a checked proof of the current statement
with approved axioms gives proved status. Revising a test's scope resets its validation;
old statements remain in history. The acceptance IDs in the phase −1 text did not yet
name checked Lean declarations; changed scopes in revision 1 are explicitly listed.
A decision is validated only when all tests required for its current export have passed.
**Rationale.** A renamed or weakened statement is not evidence for the original claim.
**Rejected.** Counting a retired false target as passed or silently inheriting proof status.
**Acceptance.** All AT-FD records and the M-F exit audit.
**Status.** frozen policy.

### D-WF-11 · Work loop
**Decision.**
1. M0 records definitions as candidates and tests as proposed. M-F states and proves
   the critical tests, with foundational prerequisites pulled forward as needed.
2. Failed tests return a concrete counterexample or missing hypothesis. Revise the
   candidate and all dependent claims before assigning more downstream proof work.
3. Only freeze a mathematical interface after its mandatory gates pass. Agents then
   work on stated tests in dependency order; broad automation does not precede the
   definition-level feasibility checks.
4. PRs cite active decisions, preserve the complete specification, pass both builds and
   the axiom audit on the same candidate, and update acceptance/dependency records.
5. Nightly jobs may rebuild documentation and run extra benchmarks, but cannot be the
   first kernel-backed validation of a merged foundational change.
**Rationale.** The early task is research and falsification, followed by scalable proof work.
**Rejected.** A frozen false statement with unrestricted agents assigned to prove it.
**Acceptance.** AT-FD-11 and the M3 merge gates.
**Status.** frozen policy.

### D-WF-12 · Retrieval service
**Decision.** Begin with searchable Markdown/registry records and exact declaration
lookup. After M-F, the optional read-only MCP provides search, get, dependency neighbors,
open tasks, decisions, acceptances, and type search over the built environment. Index
active nodes by default; historical nodes require an explicit history filter. Hybrid
embedding search is an enhancement, not an M0 mathematical prerequisite.
**Rationale.** Retrieval should expose validated work and unresolved dependencies accurately.
**Rejected.** Building a large search stack before there is a meaningful proof corpus.
**Acceptance.** Current-versus-historical retrieval examples and dependency-order tasks.
**Status.** provisional, expand at M1/M3 as useful.

### D-WF-13 · Human prose
**Decision.** Handwritten forest nodes preserve rationale, hypotheses, and unresolved
questions. They transclude generated signatures rather than restating them. The current
revision's Markdown is authoritative until it is ported; history is ported as history.
**Rationale.** Documentation needs both machine-checked statements and their design context.
**Rejected.** Treating generated statement text as a replacement for a decision's reasoning.
**Acceptance.** M0 port check and the M1 exporter integration.
**Status.** frozen policy; port implementation provisional.

### D-WF-14 · Addresses
**Decision.** Keep human decision/test IDs stable and map them to forest addresses.
Generated declaration addresses may be hashed, with full names retained as metadata.
Milestones include M-F between M0 and M1. The exact forester v5 syntax is checked
against the pinned tool before generating the forest.
**Rationale.** IDs used in proof work must resolve independently of a documentation tool's layout.
**Rejected.** Guessing unsupported address syntax before testing the pinned implementation.
**Acceptance.** M0 ID round-trip; revision crosswalk check.
**Status.** provisional formatting.

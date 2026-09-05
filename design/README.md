# Design documents — revision 1

**Current state:** revised research design; no Lean implementation or proof is included.
**Main change:** M-F, a foundation feasibility milestone between M0 and M1, now gates
root and interface freezing. See `11-foundation-feasibility.md` first for the tests,
and `12-revision-notes.md` for changes, supersession, and unresolved risks.

The design still aims at a common augmented virtual double ∞-category interface, with
categories and enriched categories obtained through matrices and `Mod`. It now separates
relative and categorical mapping spaces, removes the unsupported generic `hP`, uses
reduced object values, corrects collection universes, fixes whole structure labels in
walking constructions, and places symmetry on the profunctor ambient.

## Contents

- `00-charter.md`: goals, corrected principles, and the specification seal.
- `01-kernel.md`: explicit arity hypotheses, augmented shapes, and homotopy machinery.
- `02-root.md`: the candidate root, equivalences, maps, relative Mod, and the interface.
- `03-universal-properties.md`: categorical diagrams, slices, witnesses, and extensions.
- `04-formal-theory.md`: coherent cell-space theory with optional scoped truncations.
- `05-spaces-enrichment.md`: classifier, matrices, spans, and corrected symmetry track.
- `06-tooling.md`: scoped automation, real swap tests, and the axiom allowlist.
- `07-forest-workflow.md`: registry, versioned acceptance evidence, and staged retrieval.
- `08-roadmap.md`: revised milestone order and risks.
- `09-bibliography.md`: primary-source routes and limits of their applicability.
- `10-adversarial-review.md`: disposition of the twelve review findings.
- `11-foundation-feasibility.md`: M-F tests, dependencies, evidence, and failure responses.
- `12-revision-notes.md`: change record and decision-ID crosswalk.
- `decision-supersession.json`: machine-readable decision lineage and original-file hashes.
- `history/v0/`: the twelve original files, preserved verbatim and excluded from active indexing.

## Conventions

Current decisions have fresh IDs when their prior text changed; the crosswalk records
which old IDs they supersede. Frozen *process policies* do not mean provisional
mathematical candidates are validated. Tests retain their subject IDs where useful,
but changed informal scopes are recorded and all current proof statuses are reset to
proposed. Retired tests are not counted as passed. A future changed Lean statement
gets a new statement version and cannot inherit proof status.

A mathematical acceptance test needs a Lean statement and checked proof with approved
axioms. Tooling gates need reproducible build/check records. No gate has passed merely
because this archive contains its specification. M-F failure can trigger a model change;
it cannot be bypassed with an unapproved axiom or an undisclosed weaker test.

Revision 1 is ported into the active forest. The forest is primary for agent work; this
Markdown remains the checked-in source and audit trail for that port. Preserve the
immutable history, do not index it as active work, and do not check build artifacts into
the source repository.

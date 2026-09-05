# 12 · Revision notes — revision 1

**Revision date:** 2026-09-05. **Authorization:** add the foundation feasibility milestone
and revise the design in response to the twelve-finding review. **Validation level:**
document consistency and archive integrity only; no mathematical claim became a proved
Lean theorem in this revision.

## Are the findings fatal?

There is no demonstrated obstruction to the broad goal of a common, sealed categorical
library. Several old formulations are unusable as written. The revision repairs or
removes those formulations rather than treating them as proof tasks.

| Kind | Findings and response | Consequence |
|---|---|---|
| Direct specification repairs | Collection universes, reduced object values, whole-structure fibres, bundled data/laws, proper symmetry ambient | Plausible concrete replacements; still require compiled statements and comparisons |
| Architectural changes | Separate relative/categorical maps and raw/categorical vertical parts; remove mandatory generic hP; scope rectification and pasting | Preserves the common ambient goal but changes the API and proof strategy |
| Material research risks | Augmented arities and their diagram model; coherent Mod and its equivalence/categorical comparisons | May require a different root presentation or a smaller first release if M-F fails |

The current ∞-equivalence clauses remain a candidate, not a fully solved new definition.
The generic hP requirement is deliberately removed; this revision does not claim a
replacement truncation theorem. The augmented row format remains a proposal pending
its arity/normalization proof. Those limits are visible in the active decisions and gates.

## What changed

M-F now comes between M0 and M1. It includes eleven acceptance gates with evidence,
dependencies, counterexamples, and failure responses. The large shape catalogue,
geometric substrate, and full retrieval/generator stack follow foundational evidence.
Both kernel-backed and stub builds, together with an axiom allowlist, are required
before a merge can certify a theorem. Mathematical status is separate from prose status.

The root is a reduced homotopy-Segal candidate; ordinary strict-limit formulas need a
comparison theorem. `MapRel` and `MapCat` have separate clients. `VertRaw`, `Vert₂`,
and `VertCore` retain their different meanings. Monads/modules and slices fix their
entire selected structures through relative fibres. Formal theory works in coherent
cell spaces, using scoped homotopy-equipment comparisons only when proved.

The symmetry track now uses the profunctor ambient for symmetric/braided monoidal
category monads, with a discrete action test before the ∞-construction. Spaces-classifier
paths and arbitrary maps are distinguished. The universe, unit, weighted/conical-limit,
skeleton/coskeleton, and double-nerve wording is corrected. The bibliography now records
what a source supplies and what still needs proof in this model.

## Acceptance-test statement changes

All current tests are **proposed**: the supplied design had no linked checked Lean
statements. No old validation is inherited. In a future repository, each listed change
also requires a new statement version and a fresh checked proof.

| Test | Revision 1 treatment |
|---|---|
| AT-RT-4 | Retired: the unconditional arbitrary-root hP construction is removed; discrete recovery remains AT-RT-1 |
| AT-FT-8 | Retired: no unconditional hP-equipment theorem; specific later comparisons need new tests |
| AT-RT-5 | Revised equivalence clauses; discrete exact comparison, endpoint transport, and ∞-laws explicitly gated |
| AT-RT-6 | Relative mapping spaces only; categorical mapping semantics are separately tested by AT-FD-4 |
| AT-RT-7 | Whole-monad relative fibres and coherent walking-diagram functoriality required |
| AT-KR-2/3/5/6/8/11 | Exact arity, pattern, cofibrancy, and reduced-replacement hypotheses; no universal augmented active-chain claim |
| AT-KR-12/13/14 | Deferred geometric comparisons, with exact categories/morphisms required before stating proofs |
| AT-UP-1/3/6 | Existence, reduced whole-cone fibres, categorical invariance, and parameterized coherence explicit |
| AT-UP-7 | Corrected adjunction direction: sk_n is left adjoint to cosk_n |
| AT-UP-8 | Categorical core ambient, and now a mandatory M4 exit test |
| AT-FT-1/3/4/6/7 | Separate units/restrictions; scoped Mod preservation, constructed double nerve, typed conical weight, and named comparison ambient |
| AT-SP-1/2/3/4 | Classifier semantics, bootstrap bridge, coherent matrix construction, and relative span boundaries explicit |
| AT-SP-5 | Split categorical object comparison from the stronger augmented-VDC/module comparison |
| AT-SP-8 | Rigidification to an equivalent strict model; no universal fixed-target surjectivity inferred |
| AT-SP-9/10/11/13 | Corrected profunctor ambient and explicit equivariance/preservation hypotheses |
| AT-SP-12 | Index-size bounds explicit; does not by itself supply colimits in Cat_∞ |
| AT-FD-1 through AT-FD-11 | New foundational gates; none is marked passed by the document revision |

Other existing test IDs retain their subjects but use the repaired current definitions;
this is not permission to reuse a proof of a different statement. The exact proposed
scopes are in the active documents. Tooling acceptance includes reproducible checks as
well as any mathematical statements required by that gate.

## Decision supersession

Every historical decision whose active text was revised receives a new ID below.
The original decision/rationale/rejected text is preserved byte-for-byte in the listed
file under `history/v0/`. Those old IDs are historical, and the new IDs govern the
current candidate or policy. D-FD-01 is newly introduced. A machine-readable crosswalk
and original-file hashes are in `decision-supersession.json`.

| Historical ID (superseded) | Current ID | Document |
|---|---|---|
| `D-CH-01` | `D-CH-14` | `00-charter.md` |
| `D-CH-02` | `D-CH-15` | `00-charter.md` |
| `D-CH-03` | `D-CH-16` | `00-charter.md` |
| `D-CH-04` | `D-CH-17` | `00-charter.md` |
| `D-CH-05` | `D-CH-18` | `00-charter.md` |
| `D-CH-06` | `D-CH-19` | `00-charter.md` |
| `D-CH-07` | `D-CH-20` | `00-charter.md` |
| `D-CH-08` | `D-CH-21` | `00-charter.md` |
| `D-CH-09` | `D-CH-22` | `00-charter.md` |
| `D-CH-10` | `D-CH-23` | `00-charter.md` |
| `D-CH-11` | `D-CH-24` | `00-charter.md` |
| `D-CH-12` | `D-CH-25` | `00-charter.md` |
| `D-CH-13` | `D-CH-26` | `00-charter.md` |
| `D-KR-01` | `D-KR-13` | `01-kernel.md` |
| `D-KR-02` | `D-KR-14` | `01-kernel.md` |
| `D-KR-03` | `D-KR-15` | `01-kernel.md` |
| `D-KR-04` | `D-KR-16` | `01-kernel.md` |
| `D-KR-05` | `D-KR-17` | `01-kernel.md` |
| `D-KR-06` | `D-KR-18` | `01-kernel.md` |
| `D-KR-07` | `D-KR-19` | `01-kernel.md` |
| `D-KR-08` | `D-KR-20` | `01-kernel.md` |
| `D-KR-09` | `D-KR-21` | `01-kernel.md` |
| `D-KR-10` | `D-KR-22` | `01-kernel.md` |
| `D-KR-11` | `D-KR-23` | `01-kernel.md` |
| `D-KR-12` | `D-KR-24` | `01-kernel.md` |
| `D-RT-01` | `D-RT-16` | `02-root.md` |
| `D-RT-02` | `D-RT-17` | `02-root.md` |
| `D-RT-03` | `D-RT-18` | `02-root.md` |
| `D-RT-04` | `D-RT-19` | `02-root.md` |
| `D-RT-05` | `D-RT-20` | `02-root.md` |
| `D-RT-06` | `D-RT-21` | `02-root.md` |
| `D-RT-07` | `D-RT-22` | `02-root.md` |
| `D-RT-08` | `D-RT-23` | `02-root.md` |
| `D-RT-09` | `D-RT-24` | `02-root.md` |
| `D-RT-10` | `D-RT-25` | `02-root.md` |
| `D-RT-11` | `D-RT-26` | `02-root.md` |
| `D-RT-12` | `D-RT-27` | `02-root.md` |
| `D-RT-13` | `D-RT-28` | `02-root.md` |
| `D-RT-14` | `D-RT-29` | `02-root.md` |
| `D-RT-15` | `D-RT-30` | `02-root.md` |
| `D-UP-01` | `D-UP-10` | `03-universal-properties.md` |
| `D-UP-02` | `D-UP-11` | `03-universal-properties.md` |
| `D-UP-03` | `D-UP-12` | `03-universal-properties.md` |
| `D-UP-04` | `D-UP-13` | `03-universal-properties.md` |
| `D-UP-05` | `D-UP-14` | `03-universal-properties.md` |
| `D-UP-06` | `D-UP-15` | `03-universal-properties.md` |
| `D-UP-07` | `D-UP-16` | `03-universal-properties.md` |
| `D-UP-08` | `D-UP-17` | `03-universal-properties.md` |
| `D-UP-09` | `D-UP-18` | `03-universal-properties.md` |
| `D-FT-01` | `D-FT-06` | `04-formal-theory.md` |
| `D-FT-02` | `D-FT-07` | `04-formal-theory.md` |
| `D-FT-03` | `D-FT-08` | `04-formal-theory.md` |
| `D-FT-04` | `D-FT-09` | `04-formal-theory.md` |
| `D-FT-05` | `D-FT-10` | `04-formal-theory.md` |
| `D-SP-01` | `D-SP-10` | `05-spaces-enrichment.md` |
| `D-SP-02` | `D-SP-11` | `05-spaces-enrichment.md` |
| `D-SP-03` | `D-SP-12` | `05-spaces-enrichment.md` |
| `D-SP-04` | `D-SP-13` | `05-spaces-enrichment.md` |
| `D-SP-05` | `D-SP-14` | `05-spaces-enrichment.md` |
| `D-SP-06` | `D-SP-15` | `05-spaces-enrichment.md` |
| `D-SP-07` | `D-SP-16` | `05-spaces-enrichment.md` |
| `D-SP-08` | `D-SP-17` | `05-spaces-enrichment.md` |
| `D-SP-09` | `D-SP-18` | `05-spaces-enrichment.md` |
| `D-TL-01` | `D-TL-12` | `06-tooling.md` |
| `D-TL-02` | `D-TL-13` | `06-tooling.md` |
| `D-TL-03` | `D-TL-14` | `06-tooling.md` |
| `D-TL-04` | `D-TL-15` | `06-tooling.md` |
| `D-TL-05` | `D-TL-16` | `06-tooling.md` |
| `D-TL-06` | `D-TL-17` | `06-tooling.md` |
| `D-TL-07` | `D-TL-18` | `06-tooling.md` |
| `D-TL-08` | `D-TL-19` | `06-tooling.md` |
| `D-TL-09` | `D-TL-20` | `06-tooling.md` |
| `D-TL-10` | `D-TL-21` | `06-tooling.md` |
| `D-TL-11` | `D-TL-22` | `06-tooling.md` |
| `D-WF-01` | `D-WF-08` | `07-forest-workflow.md` |
| `D-WF-02` | `D-WF-09` | `07-forest-workflow.md` |
| `D-WF-03` | `D-WF-10` | `07-forest-workflow.md` |
| `D-WF-04` | `D-WF-11` | `07-forest-workflow.md` |
| `D-WF-05` | `D-WF-12` | `07-forest-workflow.md` |
| `D-WF-06` | `D-WF-13` | `07-forest-workflow.md` |
| `D-WF-07` | `D-WF-14` | `07-forest-workflow.md` |

## Checks performed on the document revision

The archive verification record is generated during delivery. It checks that the
original snapshot matches the supplied archive, current decision references resolve,
all changed decisions have a supersession entry, decision records contain their required
fields, retired acceptance targets are explicit, and the packaged archive round-trips
without changes. These checks establish document integrity and traceability. They do
not discharge the proposed Lean acceptance tests or prove that the candidate root works.

# Augmented incidence, algebra equations and checked models

This implements the early set-level part of AT-FD-7, the second item in the M-F
work order: generating incidence, primitive operation types, the equation
families, and a nontrivial lawful model. The full acceptance gate remains open
at statement version 1.

Cites: D-KR-18, D-RT-30, D-TL-21, D-WF-08, D-WF-10, AT-FD-7.

The source definition is Koudenburg, *Augmented virtual double categories*,
[arXiv:1910.11189v4](https://arxiv.org/abs/1910.11189v4), 3 March 2025,
Definition 1.2 and Example 1.5. Version 4 matters: its associativity condition
requires both composites to be defined. The pinned Lean dependency is still
Mathlib v4.33.1, commit 0df444a360eaa60ab8c11dca51a86af692955474.

## Implemented structure

`CellGraph` starts with a vertical quiver and a separate horizontal graph.
`Boundary` carries a horizontal input path and an output path of length at most
one. An empty path retains its endpoint incidence. `Side` includes the vertical
arrow itself, so successive cells in a `Row` must share that arrow.

`NonemptyRow` requires a positive cell count. Empty horizontal input and an empty
row are different: a row of two vertical cells has two cells and zero horizontal
edges on either boundary. `Row.input` and `Row.output` concatenate the actual
paths; their concatenation laws and the output-length bound are proved.

`Operations` adds horizontal and vertical identity cells and substitution into a
lower cell. That cell's input must be the entire concatenated output of the row.
The result concatenates the row's inputs, retains the lower output, and composes
the outside vertical arrows. Both compositions of `(0,0)` cells are derived from
these operations. `Algebra` combines this data with the proposition-valued
`Laws` record described below.

| Obligation | Checked declaration or example | Scope |
|---|---|---|
| Incident zero/one outputs | `ShortPath.cases_on`, `ShortPath.endpoints_eq` | Full incident paths, rather than a count alone. |
| Vertical boundaries | `Boundary.vertical_parallel`, `empty_horizontal_arity` | `(0,0)` cells have parallel sides; the empty horizontal graph permits only this arity. |
| Shared sides and mixed rows | `Examples.mixed_counts`, `mixed_horizontal_boundary`, shared-side negative example | Includes `cOneEmpty` followed by a one-output cell; equal objects with different intermediate arrows are rejected. |
| Nullary input and substitution | `Examples.nullaryInput_arity`, `mixedComposite`, `stacked_right_side` | Includes `(0,1)` input and a mixed substitution with nonidentity outside arrows. |
| Both vertical-cell operations | `Operations.verticalStack`, `Operations.verticalAlongRow` | Derived definitions; the general 2-category comparison from `Laws` remains pending. |
| Ordinary active-map obstruction | `Simplex.active_from_zero_target_zero`, `no_active_zero_to_one`, `no_active_encoding` | A positive-input, zero-output row cannot have the proposed ordinary active map from its output length to its input length. `active_to_zero` checks the opposite direction. |
| Supplied 2-category's cells | `FromTwoCategory.cellEquiv` | Empty-path elimination identifies cells with the supplied 2-morphisms. |
| Binary 2-cell laws | `alongRow_assoc`, `stack_assoc`, `identity_stack`, `stack_identity_object`, `stack_identity`, `interchange` in `FromTwoCategory` | Stacking associativity and object units use strictness and endpoint transport (`HEq`); the other laws hold in a bicategory. |
| Categories, functors, natural transformations | `FromCat.cellNatTransEquiv`, `identity`, `alongRow`, `stack` | Instantiates the cell model in Mathlib's strict bicategory `Cat`, preserving identities and both binary compositions. |

In the augmented drawing, along-row composition of vertical cells is vertical
composition of 2-morphisms, and stacking is horizontal composition of
2-morphisms. These names follow the two pictures, so their directions differ.

The `Examples.operations` inhabitant uses one cell at each boundary to check
typing; it is not evidence for a general algebra law. The binary model proofs
quantify over arbitrary supplied bicategories, with explicit strictness where
needed. The additive algebra below supplies a separate nontrivial model of the
full equation record. Object, vertical, horizontal and cell universes remain independent in
the incidence and operation declarations.

## Algebra equations and their domains

`EquationRows.lean`, `NestedRows.lean` and `Algebra.lean` encode Definition 1.2's
equation families. Their correspondence is explicit:

| Source obligation | Lean field | Domain construction |
|---|---|---|
| Preservation of vertical identities under stacking | `Laws.verticalIdentity_stack` | The two identity cells have composable vertical arrows. |
| Left unit for zero or one output | `Laws.leftUnit` | `shortIdentity` uses dependent elimination on the entire incident output path. |
| Right unit for empty or nonempty input | `Laws.rightUnit` | `identityRow` supplies a singleton vertical identity at empty input, otherwise one horizontal identity per input edge. |
| Identity insertion/removal at any shared side | `Laws.insertion` | Either neighbouring row may be empty; the original row must be nonempty. This includes both endpoints. |
| Nested associativity | `Laws.assoc` | `Nested.NonemptyRow` shares the complete arrows of both bands, with a nonempty inner row for each outer cell. |

`Nested.Row.inner_output` proves the boundary match needed to substitute the
flattened inner row into the composite outer cell. `composite_input` and
`composite_output` identify the other evaluation order's paths. Both constructions
preserve nonemptiness. Consequently both sides of `Laws.assoc` are actual cells,
with no assumed incidence equality or hidden existence hypothesis.

The equation fields use `HEq` to retain the explicit path and vertical-arrow
transports. The separate `Operations.leftUnit_boundary`, `rightUnit_boundary`,
`inserted_boundary` and `assoc_boundary` theorems prove equality of the complete
boundaries, including their sides. These proofs use only the operation types and
row constructions, before assuming `Laws`.

The nested-row construction is the domain of this displayed equation. It does
not assert that arbitrary augmented pastings have a unique encoding or that
incident rows already form a canonical arity presentation.

## A nontrivial lawful model

`AdditiveModel.algebra` works over any supplied vertical category, horizontal
graph and additive commutative monoid of labels. Every incident boundary has
that label type as its cells. Identity cells have label zero; substitution adds
the row's labels and the outer cell's label. All five equation families are
proved. In particular, `nested_composite_sum` proves the two-level summation law
used for associativity; no `Laws` instance is assumed to construct this model.

`AlgebraExamples` uses natural-number labels and the existing three-object
category with nonidentity arrows. Its nested example combines a `(1,0)` cell,
a `(1,1)` cell, two empty-output outer cells, and a final `(0,1)` cell. Both
evaluation orders have label 36, with outside arrow labels 9 and 14. Cells with
labels 2 and 3 at the same boundary remain distinct. Endpoint identity insertion
preserves label 9.

A further example has different intermediate factorizations with the same
composed vertical arrow. The invalid nested row is rejected: equality only
after composition does not supply the shared arrows needed by both bands.
An empty inner substitution row is also rejected, alongside positive controls.

## Remaining AT-FD-7 work

The full gate statement is unchanged. Next, extend the supplied no-horizontal
binary model to an augmented algebra and prove the general comparison
with strict 2-categories, including the discrete nerve comparison. The current
`FromTwoCategory` and `FromCat` results establish the cell and binary-operation
part of this comparison, not an equivalence with `Algebra`.

The free construction, arity category and nerve hypotheses remain to be proved.
`Row` is incident syntax, not a
canonical arity presentation; no normalization, monadicity, generic/free
factorization or Reedy/elegance theorem is asserted by its definition.

The required labelled diagram model must still supply the actual cofibrant
sources, relative restriction and replacement lemmas. The
[pinned inventory](../foundations/README.md) records the relevant upstream gaps.
Neither a generic category-of-elements construction nor Mathlib's generic Reedy
definitions discharge these project obligations. Later root, walking and Mod
work continues to depend on this gate.

## Verification

Follow [CONTAINER_SETUP.md](../CONTAINER_SETUP.md), then run:

    lake build
    python3 scripts/check_foundations.py
    bash scripts/swap_test.sh
    python3 scripts/forest_check.py
    python3 scripts/check_revision.py
    python3 scripts/check_imports.py
    python3 scripts/check_unfolding.py
    python3 scripts/check_statement_hygiene.py
    python3 mcp/server.py --selftest

`Augmented` is a default build target. The existing foundation exporter now
includes every `Kernel.Augmented` declaration in
[inventory.json](../foundations/inventory.json), with exact types, independent
universe parameters, source hashes and transitive axiom closures. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. The separate unfinished
fixture must still round-trip as `stated`, with `sorryAx` rejected.
The checker also requires every augmented implementation module to contribute
declarations, so an omitted import or stale aggregate cannot silently skip one.

After intentional audited-source changes, regenerate this evidence with
`python3 scripts/check_foundations.py --write`, then run
`python3 scripts/build_registry.py`. The seal is checked independently; this
slice adds no public sealed constants.

# Augmented incidence and binary cell models

This is the first implementation slice of AT-FD-7, the second item in the M-F
work order. It implements the generating incidence and primitive operation
types. The full acceptance gate remains open at statement version 1.

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
these operations. This record deliberately has no algebra equations yet.

| Obligation | Checked declaration or example | Scope |
|---|---|---|
| Incident zero/one outputs | `ShortPath.cases_on`, `ShortPath.endpoints_eq` | Full incident paths, rather than a count alone. |
| Vertical boundaries | `Boundary.vertical_parallel`, `empty_horizontal_arity` | `(0,0)` cells have parallel sides; the empty horizontal graph permits only this arity. |
| Shared sides and mixed rows | `Examples.mixed_counts`, `mixed_horizontal_boundary`, shared-side negative example | Includes `cOneEmpty` followed by a one-output cell; equal objects with different intermediate arrows are rejected. |
| Nullary input and substitution | `Examples.nullaryInput_arity`, `mixedComposite`, `stacked_right_side` | Includes `(0,1)` input and a mixed substitution with nonidentity outside arrows. |
| Both vertical-cell operations | `Operations.verticalStack`, `Operations.verticalAlongRow` | Operation types and derived definitions; their general algebra laws remain pending. |
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
needed. Object, vertical, horizontal and cell universes remain independent in
the incidence and operation declarations.

## Remaining AT-FD-7 work

The full gate statement is unchanged. The next step is to formalize the complete
algebra equations with their dependent incidence transports. Write
`ψ ∘ (φ₁, …, φₙ)` for substitution, and `id_A` for the vertical identity on the
identity arrow of an object. Definition 1.2 requires:

- preservation of vertical identities under stacking;
- nested-row associativity, only when both expressions are defined;
- the left unit for either zero or one output;
- the right unit for empty input, or the row of horizontal identities for
  nonempty input;
- insertion/removal of a vertical identity at any shared side, including the
  endpoints, whenever both nonempty-row expressions are defined.

Then construct the no-horizontal augmented algebra and prove its comparison
with strict 2-categories, including the discrete nerve comparison. The current
`FromTwoCategory` and `FromCat` results establish the cell and binary-operation
part of this comparison, not an equivalence with a completed augmented algebra.

Only after the equations are in place should the free construction, arity
category and nerve hypotheses be proved. `Row` is incident syntax, not a
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

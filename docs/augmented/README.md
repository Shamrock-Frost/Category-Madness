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
| Both vertical-cell operations | `Operations.verticalStack`, `Operations.verticalAlongRow` | Derived definitions; `Vertical.bicategory` and `Vertical.bicategory_strict` prove the extraction from a lawful algebra. |
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

The equation fields are ordinary equalities after `CellGraph.transport` along
`Operations.leftUnit_boundary`, `rightUnit_boundary`, `inserted_boundary` or
`assoc_boundary`. Each proof compares the complete boundaries, including their
sides, and uses only the operation types and row constructions, before assuming
`Laws`. The vertical-identity field already has one common boundary.
`transport_eq_iff_heq` proves equivalence with the previous equation form **given
that boundary equality**. Internal Mathlib comparison adapters use this lemma;
`Laws` no longer asks clients to supply bare heterogeneous equalities.

The nested-row construction is the domain of this displayed equation. It does
not assert that arbitrary augmented pastings have a unique encoding or that
incident rows already form a canonical arity presentation.

## Shapes, labels and transport

`RowShape` contains the ordered boundaries and shared vertical arrows.
`RowShape.Labels G s` supplies a cell at each boundary. `rowEquiv` proves both
round trips between a labelled row and its shape/labels pair. Cell count, input
and output are preserved. The implementation of `Row.input` and `Row.output`
now computes through the erased shape, without inspecting the labels.
This equivalence presents existing incident rows; it is not a canonical arity
or arbitrary-pasting theorem.

`SubstitutionShape` packages a nonempty row shape, lower sides and output.
Its `outer` and `result` boundaries do not depend on the cell graph or labels.
`Operations.apply` accepts that shape and `SubstitutionShape.Inputs G s`.
`apply_row` proves agreement with the existing incident-row substitution API.
The latter remains available for row constructors and comparison adapters.

`CellGraph.transport` takes an equality of full boundary frames. It has checked
identity, composition, inverse and injectivity laws. `castInput` is a restricted
wrapper around the same transport. `Operations.substitute_transport` handles
row reindexing including the outer cell; `apply_transport` handles equality of
complete substitution shapes. Thus a client can move a whole substitution
through its incidence equality instead of rewriting dependent arguments one by
one.

`SubstitutionExamples.shape_independent` and `labels_matter` check that changing
labels preserves the shape but can change the answer. `cannot_transport_label`
rejects transport between distinct boundaries even when the underlying label
values happen to be heterogeneously equal. This checks the explicit boundary
requirement; it does not claim that the previous checked algebra laws were
unsound.

## Vertical 2-category extraction

`Vertical` derives both unit laws, stacking associativity, along-row
associativity, and interchange from the augmented algebra equations. Its
`substitute_eq_stack_compose` identifies vertical substitution with row
composition followed by stacking. `homCategory`, `bicategory`, and
`bicategory_strict` construct Mathlib's actual categories and strict bicategory,
including coherence. These are derived structures, not additional algebra
axioms. Client associativity and interchange statements use ordinary equality.

Some internal dependent equality remains in `Vertical`, `ComparisonTransport`
and the Mathlib bridge: strict associativity of the underlying arrows is
propositional. The refactor centralizes transport and gives the shape-facing
API explicit equality laws; it does not claim to eliminate every heterogeneous
comparison in the implementation.

`NoHorizontal.rowView` eliminates empty horizontal paths to an ordinary chain
of parallel vertical cells. `rowView_embed` and `rowView_length` prove its
round trip on embedded chains and preservation of length.
`FromTwoCategory.operations` now defines all substitutions of a supplied strict
2-category, and `substitute_vertical` proves their row-fold/stack computation.
`FromTwoCategory.algebra` in `FromTwoCategoryLaws.lean` now proves the
reverse construction satisfies all five algebra law families. `TwoBand` and
`nestedViewFrom` reduce its general associativity domain to two rows; the proof
uses row folding, interchange and stacking associativity.

`FromTwoCategory.homEquivalence` gives inverse functors recovering each supplied
hom category. In the other direction, `NoHorizontal.cellEquiv` gives inverse
maps at every complete boundary, and `substitute_roundtrip` proves preservation
of arbitrary incident substitution with explicit transport. Both binary
compositions and vertical identities are also recovered. `homNerveIso` identifies
the discrete hom nerves in every simplicial degree, with their strict Segal
structure. The nerve on augmented arities remains part of the arity construction.

## Free cells over fixed incidence

`CellOperation` indexes each identity or substitution by its complete incident
shape. Its `Position` type is finite, with each position carrying a full cell
boundary. `CellInterpretation.interpret_operations` checks that this signature
recovers the incident operation API. `Operations.Map` preserves that signature;
its `substitute` theorem gives ordinary equality after explicit input transport.

`CellTerm` freely adjoins these operations to the supplied cell generators.
`CellTerm.Related` is the congruence generated by exactly the five algebra
equation families. `evaluate_related` proves soundness in every lawful algebra.
The quotient construction uses this generated congruence, not an assumed law
record or equality in all models.

`CellTerm.quotient_laws` proves all five laws on quotient terms, using sections
to lift arbitrary rows and nested rows to representatives. `freeAlgebra` bundles
these proofs. `freeLiftEquiv` identifies cell-generator assignments with
operation-preserving maps out of the free algebra. Evaluation is unique.
`CellTerm.Leaf` has a checked finite
instance, and `evaluate_eq_of_leaves` shows that evaluation depends only on those
generator occurrences.

This is a **relative** free construction: the vertical category and horizontal
graph are fixed parameters. It does not freely generate vertical paths, vary the
objects or horizontal graph, or establish a global arity category. Finite inputs
and finite term support do not prove density or nerve recognition. Those are
separate obligations under D-KR-15 and D-KR-18.

## Global generating incidence and free mapping property

`Generating.Shape` is the small category of elementary generator boundaries:
objects, vertical edges, horizontal edges and cells of each arity, with the
endpoint incidence relations. `Generating.Graph.presheafEquiv` proves round
trips between explicit generating data and presheaves on that category. This
object equivalence extends to `presheafEquivalence`, with graph maps defined
as incidence-natural families. `elementaryDensity` expresses each generating
presheaf as the canonical colimit of its elementary representables. This base
density alone does not establish the monad arity condition.

`Generating.Graph.boundary` retains every object, edge and outside side of a
cell generator. `freeAlgebra` adjoins vertical paths and then the free cell
quotient. `BaseMap.pullbackAlgebra` proves all five laws survive change of the
vertical category and horizontal graph. These public law statements remain
ordinary equalities after complete-boundary transport; internal comparison
adapters use heterogeneous equality.

`SkeletonAssignment.baseMap_unique` proves uniqueness of the vertical path
extension. `cellAssignmentEquiv` and `freeMapEquiv` prove that assignments of
cell generators extend uniquely to operation-preserving maps into any target
algebra over the induced base map. Thus the construction now allows objects
and both kinds of edges to vary.

## Global adjunction and monadicity comparison

`BundledAlgebra` forms the category of small augmented algebras in a chosen
universe. A global map includes a vertical functor, a horizontal edge map and
a map of cells with their complete boundaries attached. Both identity-cell
and substitution preservation are ordinary equalities of these attached cells.
Internal typed comparison adapters still use heterogeneous equality.

`BundledAlgebra.forget` is the functor to generating incidence graphs.
`Generating.Graph.lift` and restriction along the generator unit are inverse,
with naturality proved. `BundledAlgebra.freeForgetAdjunction` packages the actual
free/forgetful adjunction, and `generatingMonad` is its induced monad. The unit
and counit have checked formulas. Ordered path positions and reconstruction
lemmas ensure the mapping property retains every vertex and edge, including
empty input/output boundaries.

The forgetful functor and `generatingComparison` are faithful.
`comparisonHomEquiv` characterizes comparison morphisms as graph maps that
commute with evaluation of all free expressions. This condition yields the
vertical functor, complete-boundary cell map, graph-map round trip, evaluation
factorization and preservation of both identity cells. `generatorCell`,
`generatorRow` and `generatorOuter` choose free representatives of whole
substitution inputs, preserving shared sides. Their evaluation laws prove
`comparisonCells_substitute`, so `comparisonMap` preserves arbitrary
substitution as well. The concrete comparison is fully faithful, and the
generating forgetful functor reflects isomorphisms.

The reconstruction below proves essential surjectivity and monadicity. The
separate arity density and exactness hypotheses remain to be proved.

## Vertical reconstruction from arbitrary monad algebras

`GeneratingMonadAlgebra` begins the object reconstruction needed for monadicity.
It takes an arbitrary algebra for `BundledAlgebra.generatingMonad`, with only
its unit and associativity laws. `action_object` proves that the action fixes
objects, and `evalPath` evaluates vertical paths at their original endpoints.
`evalPath_single` and `evalPath_flatten` derive the singleton and two-path
flattening laws from the monad laws, including empty paths.

`PathEvaluation.category` recovers identities and associative composition from
those two laws, with the object and arrow universes independent. Its evaluation
functor agrees with ordinary path composition. `GeneratingMonadAlgebra.Vertical`
applies this construction to the actual generating monad. `map_evalPath` proves
that monad-algebra morphisms commute with all path evaluations; `verticalFunctor`
therefore gives an actual functor from the Eilenberg–Moore category to `Cat`.
The horizontal graph is retained, `action_horizontal` checks its generator
retraction, and `evaluationBase` packages vertical/horizontal base evaluation.

For any existing augmented algebra, `BundledAlgebra.verticalHomEquiv` recovers
its original arrows from their full incidence fibres. `verticalToOriginal` and
`verticalFromOriginal` preserve identities and composition, and
`verticalComparisonEquivalence` proves both round trips. The recovery commutes
with every augmented-algebra map by `verticalToOriginal_naturality`.

## Cells and operations from arbitrary monad algebras

`GeneratingMonadAlgebra.cells` recovers the generating cells at their exact
boundaries over the reconstructed category. `action_boundary` proves that the
monad action preserves both vertical sides and every ordered horizontal edge,
including the endpoints of empty paths. `evaluationCells` packages this as a
cell map over `evaluationBase`.

`generatorCell` and `generatorRow` choose free representatives. Their evaluation
theorems recover the original incident cells and whole rows, with shared sides
and both input and output paths intact. `evaluationCells_surjective` proves
surjectivity on cells together with their full boundaries. `generatorOuter`
also represents each outer cell at the chosen row's output.

`operations` reconstructs both identity cells and arbitrary nonempty-row
substitution by evaluating free operations and transporting along proved
full-boundary equalities. `evaluationCells_multiplication` derives the cell
flattening equation from the monad associativity law. The free action commutes
with the chosen cell and row representatives, yielding
`evaluationCells_horizontalIdentity`, `evaluationCells_verticalIdentity` and
`evaluationCells_substitute`. Thus `evaluationOperations` preserves every
primitive operation, including substitution with nullary cells, empty outputs
and mixed rows. None of these proofs assumes a lawful augmented algebra on the
reconstructed cells.

## Reconstructed laws and monadicity

`leftUnit_law`, `rightUnit_law`, `verticalIdentity_stack_law`, `insertion_law`
and `assoc_law` prove all five equation families for `operations`. Free
representatives of identity rows, inserted rows and nested rows retain the
shared sides at both levels. The proofs evaluate the corresponding free laws
and transport along complete-boundary equalities. Either neighboring row in
identity insertion may be empty; mixed rows and empty-output cells remain
within the universally quantified domains.

`algebra` bundles these laws, and `reconstructed` is the resulting augmented
algebra. `reconstructionUnit` is an isomorphism on all generating graph sorts,
including the cell arity and boundary fibres. `reconstruction_action` identifies
its evaluation with the supplied action, and `reconstructionIso` gives an
isomorphism of monad algebras. Thus `generatingComparison` is essentially
surjective as well as fully faithful. `generatingMonadicEquivalence` proves the
comparison equivalence, and `BundledAlgebra.forget` is a `MonadicRightAdjoint`.

## Reusable nerve recognition step

`Nerve.MonadMap` gives a comparison between monads over a functor between base
categories, with unit and multiplication compatibility. `lift` constructs the
induced algebra functor. It is faithful when the base functor is faithful, and
full when the base is fully faithful and the comparison maps are epimorphisms.
With invertible comparison, `essImage_iff` proves that an algebra descends
exactly when its underlying object lies in the base functor's essential image.

`NerveSquare` transfers these conclusions through supplied category
equivalences and a compatible comparison square. `restriction_essImage_iff`
expresses recognition in terms of the original restriction functor. These are
checked proofs of the algebra-recognition step in
[Berger–Melliès–Weber](https://arxiv.org/pdf/1101.3064), Proposition 1.3 and the
exact-square argument. They assume the monad comparisons and their stated
properties, not the desired full-faithfulness or recognition conclusion.

## Actual free-arity nerve square

For any supplied small arity functor `i` into generating graphs, `Nerve.Theory i`
is the full category of free augmented algebras on those arities. `baseNerve`,
`algebraNerve` and `restriction` give the actual presheaf square, with the
adjunction supplying `restrictionIso`. Restriction is monadic: its left adjoint
is left Kan extension, it preserves reflexive coequalizers, and its identity on
objects lets it reflect isomorphisms. `restrictionMonadicEquivalence` supplies
the second concrete equivalence required by the recognition argument.

`arityMonadMap` constructs the canonical comparison, including its unit and
multiplication laws. `arityComparisonIso` proves compatibility with both monadic
comparisons. `algebraNerve_full` and `algebraNerve_essImage_iff` then prove the
conditional augmented nerve theorem: if `i` is dense and that canonical
comparison is pointwise invertible, the augmented nerve is fully faithful,
and a presheaf is in its image exactly when its restriction is a base nerve.
The monadic equivalences and comparison square are constructed, not assumed.

`freeNerveComparison` expresses the canonical monad comparison as the restriction
of the mate of the free/forgetful unit. `freeNerveComparison_eq` identifies this
mate with the representable Kan-extension isomorphism on each object of a fully
faithful arity family. Thus the canonical comparison is invertible on the arities
themselves. Extending this conclusion to every generating graph requires a
separate argument, supplied below under filtered-colimit preservation.

## Finite incidence supports and candidate family

`Generating.Face` enumerates every face of an elementary generating boundary,
including its own generator, all vertices, both vertical sides and all horizontal
edges. `faceArrow_surjective` proves that this finite list covers every incidence
arrow. Empty inputs and outputs still retain their endpoint vertices and sides.

`finiteSupport` closes a finite collection of generators under all incidence
maps. The total support is finite across all object, edge and cell sorts combined.
`presheafIsFinite_iff_finite_elements` proves that finite generation is equivalent
to finite total incidence in this base; `finite_range_elements` proves maps from
finite incidence data have finite images.

`finiteSupportIsColimit` proves that every generating presheaf is the filtered
colimit of these finite incidence closures. Single-generator supports cover every
element, and finite unions identify overlaps. `finitelyPresentable_iff_finite_elements`
characterizes the finitely presentable presheaves exactly as those with finite
total incidence. One direction uses the finite category-of-elements presentation
by representables; the other factors the identity through a finite support.

`FiniteIncidence` is a small model of the full category of finite incidence
presheaves. `finiteIncidenceGraphs` is its fully faithful dense inclusion into
explicit generating graphs. Applied to this candidate, `finiteIncidenceNerve_full`
and `finiteIncidenceNerve_essImage_iff` require only pointwise invertibility of
the specific canonical comparison. Density is now proved for this family.

`GeneratingFiniteNerve` proves that this base nerve preserves filtered colimits.
Maps out of finite arities factor through finite supports, and equality of two
such maps is witnessed at a common finite stage. `isIso_of_finiteIncidence`
proves that transformations between filtered-colimit-preserving functors are
invertible if they are invertible on the small finite family.

`finiteIncidence_exactness_iff_finitary` proves that the canonical comparison is
invertible on all generating graphs **if and only if** the actual generating
monad preserves filtered colimits. The forward direction uses the fully faithful
base nerve to reflect preservation; the reverse combines finite-support detection
with the proved representable comparison. `finiteIncidenceNerve_full_of_finitary`
and `finiteIncidenceNerve_essImage_iff_of_finitary` give the augmented nerve theorem
under this single remaining hypothesis.

The remaining arity obligation is filtered-colimit preservation by the augmented
monad. This still needs proof, including the incidence and equation-witness arguments that
finite raw cell-term leaves do not supply. This family uses all finite incidence
diagrams and every incidence-preserving map. It supplies no canonical minimal
pasting syntax, normalization, generic/free factorization or Reedy structure.

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

The full gate statement is unchanged. The strict 2-category reconstruction,
cell/hom round trips, arbitrary substitution compatibility and discrete hom
nerves are checked. The global free augmented algebra, adjunction, monadicity
and conditional free-arity nerve theorem are now proved.

A small dense candidate category of finite incidence diagrams is now constructed.
Its canonical-comparison invertibility is now equivalent to the remaining
finitarity obligation. Still open is any canonical
geometric arity presentation required by a later model construction. `Row` alone
proves neither normalization nor generic/free factorization.

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

The generated inventory and seal evidence record the checked declaration counts,
source hashes and signatures for the current checkpoint.

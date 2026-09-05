# 02 · Root — revision 1

This is the current candidate specification. New decision IDs and the immutable original
are tracked in `12-revision-notes.md`. No theorem marked as a target below is claimed
proved by this document. M-F selects a workable root and its comparisons before M3
freezes the full interface.

## Presentation, cells, and equivalences

### D-RT-16 · Reduced augmented Segal presentation
**Decision.** For `X : Type ℓ`, use the labelled augmented arity category
`Θ^aug_{fc,X}` once its arity and Segal-core theorems have been established. A candidate
`VDC∞.{ℓ,s}` is a presheaf into `sSet.{s}` with:
1. a specified reduced presentation: every `P(pt x)` is the terminal simplicial set;
2. Kan values;
3. Kan fibrations from elementary cell values to their full boundary limits;
4. Segal comparison equivalences from `P(θ)` to the homotopy limit of its elementary
   inert subshape diagram.
The edge-to-object endpoint maps also occur in boundary diagrams; reduced object
values make their targets terminal. Strict Segal-core limits may implement (4) only
after the comparison with the homotopy limits is proved. No strict-limit assertion is
inferred from contractibility of object values.
**Rationale.** This supplies genuinely discrete object data and preserves the intended
cell fibres. It leaves room to correct the shape or fibrancy hypotheses at M-F.
**Rejected.** The earlier contractible-object axiom and its strict-gluing justification.
**Acceptance.** AT-FD-3, AT-FD-7, AT-RT-1, AT-RT-3; AT-FD-8 for a nondiscrete example.
**Status.** provisional; freeze only after M-F and the full M3 comparisons.

### D-RT-17 · Presentation versus homotopy theory
**Decision.** A raw root presentation, a Reedy-fibrant presentation, and a categorical
localization are distinct objects. Neither horizontal composites nor symmetry are
primitive. Their existence or encoding is supplied by additional constructions.
**Rationale.** Reedy fibrancy controls mapping and restriction fibrations; it does not
identify all diagrams that should be categorically equivalent.
**Rejected.** Using one unnamed notion of fibrancy or equivalence for all three roles.
**Acceptance.** AT-FD-4, AT-FD-5.
**Status.** provisional until the comparisons are formalized.

### D-RT-18 · Strict maps
**Decision.** A strict map has a function on object labels and a presheaf map into the
corresponding reindexing of its target, respecting reduction. These form a category of
presentations. Reindexing's preservation of the required fibrancy is a theorem.
**Rationale.** Strict maps are convenient input syntax; their interpretation in a
localization needs a comparison theorem.
**Rejected.** The claim that ordinary presheaf enrichment already gives all categorical maps.
**Acceptance.** AT-FD-4, AT-FD-8.
**Status.** provisional.

### D-RT-19 · Raw paths and categorical parts
**Decision.** `VertRaw(P)` restricts to vertical path shapes. `HorizontalObjects(P,a,b)`
is `P(h(a,b))`. `Hor(P,a,b)` is the Segal-category presentation whose objects are
horizontal arrows and whose morphisms are unary cells with identity vertical sides;
it is not the same object as `HorizontalObjects`.
`Vert₂(P)` uses vertical arrows and the augmented `(0,0)` cells, retaining noninvertible
2-cells. `VertCore(P)` denotes the (∞,1)-category obtained by retaining equivalences in
its hom ∞-categories, after the requisite coherent construction is proved. In particular,
`VertRaw(Cat)` is the ordinary category of categories and strict functors, while
`VertCore(Cat)` has groupoids of functors and natural isomorphisms as mapping spaces.
Neither an equality nor a general equivalence `VertRaw(P) ≃ VertCore(P)` is asserted.
**Rationale.** The distinction already matters for two isomorphic target objects.
**Rejected.** Calling raw vertical mapping spaces the spaces of functors and natural equivalences.
**Acceptance.** AT-FD-4, AT-RT-11, AT-RT-12, AT-UP-8.
**Status.** raw restriction provisional implementation; categorical extraction research-gated at M-F.

### D-RT-20 · Truncation is an optional comparison
**Decision.** There is no unconditional public `hP`. For a discrete root the nerve
comparison recovers its ordinary augmented VDC. For a nondiscrete root, any homotopy
2-category or equipment comparison must specify retained objects/arrows, cell
truncation, transport, and composition, with proofs of compatibility. A general
comparison may be bicategorical. D-FT-09 governs when it may be used.
**Rationale.** Taking components of boundary spaces forgets monodromy. Fibres of a Kan
fibration have transport along paths, not path-independent canonical bijections.
**Rejected.** Selecting representatives of `π₀ P(v)` and `π₀ P(h)` and declaring the
resulting fibre components a canonical VDC.
**Acceptance.** AT-FD-6; AT-RT-4 is retired in its original general form. Discrete
recovery is part of AT-RT-1. Any later truncation receives a new acceptance ID.
**Status.** frozen removal of the unsupported requirement; general truncation later.

### D-RT-21 · Two equivalence predicates
**Decision.** Keep the following separate.
- `LevelEq` compares fixed-label presentations by levelwise weak equivalences. It is
  the relation used for Reedy replacement and relative presheaf mapping invariance.
- `VDCEq` is the candidate categorical equivalence of augmented VDC presentations.
  Its provisional local specification requires equivalences on raw vertical hom
  spaces and on cell spaces over every fixed source boundary, and *simultaneous*
  essential surjectivity: choose object representatives with vertical equivalences,
  and for each target horizontal choose a source horizontal and an invertible unary
  cell over those chosen endpoint equivalences. Invertibility and compatibility are
  formulated through coherent unary-cell diagrams, not through the deleted `hP`.
There is no requirement that `P(h) → Q(h)` be a weak equivalence. In the discrete
case the comparison target is Koudenburg's equivalence in `AugVirtDblCat` (with vertical
isomorphisms). For Segal categories themselves use their standard DK-equivalence.
The complete ∞-clause list and its relation to other VDC models remain M-F research
obligations; the provisional predicate is not exported as a settled definition.
**Rationale.** Equivalent presentations may have different sets of isomorphic horizontals.
Different endpoint representatives must work together for all cells.
**Rejected.** The original horizontal-object bijection condition; checking horizontals
only at literal image endpoints; deriving the ∞-comparison from the discrete case alone.
**Acceptance.** AT-FD-5: duplicate horizontals, endpoint transport, and 2-out-of-3;
AT-RT-5 in its revised scope. AT-RT-9 remains the full external comparison.
**Status.** provisional. M-F may change these local clauses if their tests fail.

### D-RT-22 · Reedy replacement
**Decision.** `ReedyFibrant P` is an explicit property for the proved shape model.
A chosen functorial `R_rd` must preserve reduced object labels and yield a `LevelEq`
`P → R_rd P`, with the corresponding boundary and Segal conditions. Its existence
is AT-KR-11. If the chosen shapes do not make all sources cofibrant, relative mapping
constructions also specify a cofibrant source replacement. Any categorical replacement
is named separately. Standard objects have only the fibrancy certificates actually proved.
**Rationale.** Relative mapping invariance uses a specified weak equivalence class.
**Rejected.** Claiming Reedy replacement alone implements categorical localization.
**Acceptance.** AT-KR-11, AT-FD-3, AT-FD-8.
**Status.** provisional until the chosen diagram model is validated.

### D-RT-23 · Relative maps and categorical maps
**Decision.** `MapRel(A,P; f)` is the simplicial presheaf mapping space over the fixed
label function `f`, using a coherent Reedy-fibrant target and any required cofibrant
source. A relative version fixes a prescribed subdiagram `B → A` by taking a fibre of
the restriction map. Strict fibres are used when that restriction is a proved Kan
fibration; otherwise choose a functorial homotopy-fibre construction for the whole diagram.
For Segal categories, `MapCat(C,D)` denotes the mapping space of their localization at
standard DK-equivalences, implemented by a proved categorical framing or complete-Segal-space
comparison. It models the core of `Fun(C,D)`. `MapCat` has no fixed label function.
General mapping spaces of localized VDCs, if needed later, receive a separate definition.
**Rationale.** Relative diagram choices and equivalences between functors have different roles.
**Rejected.** A disjoint union of fixed-label `MapRel` spaces as the definition of `MapCat`.
**Acceptance.** AT-RT-6 now concerns only `MapRel`: independence up to weak equivalence
and strict maps for discrete targets. AT-FD-4 requires `MapCat(1,I)` contractible and
`MapCat(1,BG) ≃ BG`. No acceptance test identifies these two APIs.
**Status.** provisional until M-F establishes both constructions and their bridge.

## Walking structures and examples

### D-RT-24 · `Mod` by relative walking diagrams
**Decision.** Work with one coherent choice of `R_rd P`. A monad over a label is a
vertex of `MapRel(N Mnd,P)`. For a walking diagram `W_θ`, let `B_θ → N W_θ` be the
subdiagram containing the copies of the walking monad at all object positions.
For selected monads `m_x`, define the proposed value by the relative fibre

`Mod(P)(θ; (m_x)) = Fib_(m_x)( MapRel(N W_θ,P) → MapRel(B_θ,P) )`.

The notation includes fixed underlying base labels and their structure restrictions.
At a point shape, `B_pt = N W_pt = N Mnd`, and the fibre over its selected monad is a
point. The family `B_θ → N W_θ` must be functorial in θ. Prove its restriction maps
are fibrations before using strict fibres. Replacement chosen independently at each
shape is prohibited. Prove the Segal condition, functoriality on maps, and construction-specific
invariance; neither `LevelEq` nor `VDCEq` invariance is inferred solely from the formula.
**Rationale.** Fixing an object label of `Mod` fixes its whole monad structure.
**Rejected.** The full space of all monads as the value at one chosen monad.
**Acceptance.** AT-FD-8 and AT-RT-7, including point, vertical edge, bimodule, binary
cell, units, and composition. AT-FT-3 is the separate equipment-preservation theorem.
**Status.** provisional research construction; full proof required before export.

### D-RT-25 · `Mat(Set)` and `Category`
**Decision.** For object types `A B : Type u` and entries in `Type v`, horizontals are
families `A → B → Type v`. Vertical arrows are functions. Multicells are families of
functions from input products to the target family. Empty-target cells have target
`f a₀ = g a_n`, corresponding to cells into the equality matrix. This augmentation
is checked against the unital-to-augmented construction, including all unit laws.
`Category.{u,v} A := Monad (Mat(Set.{v};u)) A`. Export its classical hom, identity,
composition, and laws by the discrete comparison. `Cat := Mod(Mat Set)` includes
functors, profunctors, and augmented transformation cells. Its different vertical
extractions are those of D-RT-19.
**Rationale.** The matrix example provides a small exact test of the entire discrete path.
**Rejected.** Identifying natural transformations with paths of strict functor maps.
**Acceptance.** AT-FD-1, AT-RT-2, AT-RT-10, AT-RT-11, AT-RT-12.
**Status.** provisional until M-F's discrete prototype and the complete M3 comparison.

### D-RT-26 · Discrete nerve comparison
**Decision.** Prove that the nerve of the kernel's set-level augmented VDC is reduced
and satisfies the root conditions; conversely recover a set-level augmented VDC from
a discrete root using the nerve theorem, without an arbitrary-root truncation.
The equivalence identifies root monads in `Mat Set` with classical category structures.
**Rationale.** Discrete self-hosting is independent of the invalid general `hP` formula.
**Rejected.** Using a promised general truncation to justify the discrete inverse.
**Acceptance.** AT-RT-1, AT-RT-3, AT-RT-10.
**Status.** provisional; required by M3.

### D-RT-27 · Universe policy
**Decision.** In `VDC∞.{ℓ,s}`, `ℓ` measures the type of labels and `s` the simplex
sets of presheaf values. A matrix ambient for `A : Type u` and entries in `Type v`
uses labels `Type u : Type (u+1)` and matrix values in `Type (max u (v+1))`:

`Mat(Set.{v};u) : VDC∞.{u+1, max u (v+1)}`.

This is an intended elaboratable signature, to be tested in Lean. Its category
projection still has `A : Type u` and `Hom : A → A → Type v`. The analogous spaces
ambient has a classifier of small spaces in `sSet.{v+1}` and family collections at
least `max u (v+1)`. Constructions involving all objects, monads, or diagrams explicitly
compute any additional maxima or successors. No ban on necessary `max` expressions;
`ULift` only raises universes. Yoneda's presheaf target and the allowable diagram sizes
are stated explicitly and are not solved by augmentation.
**Rationale.** Entry size and collection size are different.
**Rejected.** The former `Mat.{u,v} : VDC∞.{u,v}` signature with labels `Type u`.
**Acceptance.** AT-FD-1, including `u<v`, `u=v`, `u>v`, and category-size examples.
**Status.** minimal universe signatures compiled under AT-FD-1; semantic constructions remain provisional.

## Seal and API

### D-RT-28 · Bundled specification and a proved interface
**Decision.** Use a specification structure containing carriers, operations, and their
laws, with universe parameters and internal dependencies made explicit. Seal an
inhabitant of that structure, not unrelated operations whose laws were proved about a
different implementation. Transparent projections may expose opaque specification
fields; the specification structure itself contains no kernel vocabulary.
An irreducible implementation with an equivalent audited API is an alternative if the
bundle causes practical problems; AT-FD-2 decides the mechanism.

The initial exported vocabulary is limited to:
- finite shape syntax and proved operations, transparently, only for validated shapes;
- sealed spaces, maps, homotopy, fibres, and proved mapping/fibrancy operations;
- the validated root, strict maps, `VertRaw`, `Hor`, and the proved parts of `Vert₂` and
  `VertCore`, with names distinguishing the two;
- `MapRel` and the separately justified Segal-category `MapCat`/`Fun` interface;
- discrete embedding, walking structures, `Mod`, `Mat Set`, and their proved comparisons;
- closure lemmas with explicit hypotheses and the precise equivalence relation used.
No arbitrary `hP`, universal rectification theorem, unvalidated shape, or future slice
construction is included merely because a later milestone needs it. Slices and limits
are added at M4 with their proofs. Kernel primitives needed there are tested at M-F.

New sealed data or changes to a frozen signature require a superseding decision.
Lemmas in interface vocabulary may be added without changing the signature, provided
both builds, dependency checks, and the axiom audit pass. The stub preserves transparent
specification infrastructure and replaces its implementation package with an axiom of
the same specification type. The kernel-backed build contains no such stub axiom.
**Rationale.** The consistency witness must inhabit the same dependent specification
against which client theorems are proved.
**Rejected.** Grep alone for statement hygiene; a vacuous swap test; nightly-only
validation of code already merged using stub axioms.
**Acceptance.** AT-FD-2, AT-FD-11; complete M3 swap test.
**Status.** provisional mechanism; interface contents freeze after their proofs.

### D-RT-30 · Vertical 2-cells and pasting
**Decision.** The augmented `(0,0)` cells define the vertical 2-dimensional part.
Horizontal units, when present, give the equivalent presentation by cells into a unit;
they are not required for vertical cells to exist. Prove the discrete 2-category laws
and the classical `Vert₂(Cat)` comparison. The ∞-version retains coherent composition
and is compared with the chosen (∞,2)-model at M-F. `paste` initially handles discrete
composites and restrictions from one coherent diagram.
**Rationale.** Augmentation already carries transformations, including for nonunital objects.
**Rejected.** Delaying all vertical 2-cells until unit factorization is available.
**Acceptance.** AT-RT-12, AT-FD-4, AT-FD-7, AT-FD-10.
**Status.** discrete implementation provisional; ∞-comparison research-gated.

### D-RT-29 · Thin API
**Decision.** Generate convenient hom, identity, binary and unbiased composition,
functor, profunctor, and transformation APIs from proved interface laws. Human notation
is a separate generated view. Do not generate mathematical laws from unproved signatures.
**Rationale.** Presentation convenience should not reintroduce implementation dependencies.
**Rejected.** A generator that closes client proofs by unfolding root implementations.
**Acceptance.** AT-RT-10, AT-RT-12 and the M3 swap build with a nontrivial client.
**Status.** provisional; implement after the semantic prototype.

## Acceptance-test status

All tests in this revision are proposed until a Lean statement and checked proof are
recorded. AT-RT-1/2/3/7/8/10/11/12 retain their comparison goals with the repaired
constructions. AT-RT-4 is retired. AT-RT-5 uses the revised equivalence specification;
AT-RT-6 is explicitly relative. AT-RT-9 is the full external ∞-comparison. The small
M-F comparisons are mandatory even if that full theorem is scheduled later.

## Open questions

- OQ-RT-1: can strict-core limits implement the homotopy-core specification under the
  corrected augmented shape hypotheses? Keep homotopy limits if the proof fails.
- OQ-RT-2: which coherent walking-diagram construction proves all of `Mod`'s structure
  and invariance laws? Its relative-fibre semantics is fixed, but the proof route is open.
- OQ-RT-3: establish the full augmentation/unit correspondence for the matrix example.
- OQ-RT-4: does the proposed local `VDCEq` predicate admit the intended ∞-comparison?
  A counterexample requires a revised predicate or root; it is not an approved axiom.
- OQ-RT-5: choose and implement the categorical framing for `MapCat` and `VertCore`.

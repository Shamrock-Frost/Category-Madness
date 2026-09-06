# 01 · Kernel — revision 1

Kernel/ may use Mathlib and definitional equality. Prototype/ pulls forward only the
prerequisites needed for M-F; the general machinery follows after the foundation gates.

### D-KR-13 · Allowed scaffolding
**Decision.** Set-level augmented VDCs and their free constructions may be defined in
Kernel/ to build arities and state comparison theorems. They are not a second public
notion. Their discrete nerve is compared with the root before the seal.
**Rationale.** Explicit algebraic scaffolding makes the intended nerve testable.
**Rejected.** An ad hoc shape category with no discrete recognition theorem.
**Acceptance.** AT-KR-8, AT-RT-1.
**Status.** frozen policy.

### D-KR-14 · Mathlib inventory
**Decision.** Pin Lean and Mathlib at M0. Record exact available declarations and gaps
for category theory, simplicial sets, Kan fibrations, weak equivalences, mapping spaces,
model structures, and Reedy machinery. Every proof route names the required inventory
entries or explicit new lemmas. Refresh the inventory on version changes.
**Rationale.** Existence in the literature is not availability in a pinned Lean dependency.
**Rejected.** Scheduling a construction on the assumption that a vaguely named Mathlib
module contains the needed theorem.
**Acceptance.** AT-KR-0: verified names, signatures, gaps, and dependency versions.
**Status.** frozen policy.

### D-KR-15 · Arity recipe with separate hypotheses
**Decision.** Formalize the general BMW nerve theorem for a monad equipped with a proved
arity presentation. Separately establish the hypotheses providing canonical arities and
generic/free factorization when used, such as the relevant strongly cartesian conditions.
A free-algebra construction alone supplies neither. For each chosen monad record:
base presheaf category, arity family, density/recognition result, factorization theorem,
elementary core presentation, and any Reedy/EZ structure.
The first examples are free categories (Δ) and the free augmented-VDC construction.
The general reusable theorem may initially be preceded by a specialized proof if that
is the shortest way to validate the root. Ω_p, Ω, and Θ_n follow only when needed.
**Rationale.** The general nerve theorem, the pattern, and Reedy properties are distinct results.
**Rejected.** Automatic active–inert factorization for every monad with arities;
requiring five shape families before validating the central one.
**Acceptance.** AT-KR-1, AT-KR-2, AT-KR-8, AT-FD-7; AT-KR-3/4 for later presentations.
**Status.** provisional implementation strategy; hypotheses must be proved before use.

### D-KR-16 · Patterns and homotopy Segal cores
**Decision.** Give each adopted shape category its own proved active–inert structure and
elementary objects. In the discrete case the core is a colimit presentation of an arity
and the nerve condition is an ordinary limit condition. In the homotopy case use the
homotopy limit over the actual elementary inert diagram, including its incidences.
Using a strict limit is a theorem under a specified fibrancy condition.
**Rationale.** Limits over overlapping cells involve boundaries, not just independent products.
**Rejected.** Identifying general BMW recognition with a particular elementary pattern
without checking the arity decomposition.
**Acceptance.** AT-KR-5 for Δ; AT-FD-3 and AT-FD-7 for the root.
**Status.** provisional until each shape's proof.

### D-KR-17 · Diagram model and cofibrancy
**Decision.** Prove the Reedy structure required for the adopted augmented shapes.
Elegance, if proved, provides the desired monomorphism/cofibrancy results. Until then,
any relative mapping-space theorem carries its actual cofibrancy hypotheses.
Generalized Reedy and normal presheaves are used for Ω only with their own proved
hypotheses. Failure of elegance elsewhere does not imply that this fallback applies.
Alternative diagram model structures or explicit cofibrant sources may be proposed at
M-F, together with the new mapping, restriction, and replacement proofs they require.
**Rationale.** Absence of automorphisms does not prove elegance or a model-category theorem.
**Rejected.** Generalized Reedy as an automatic remedy for every failed elegance test.
**Acceptance.** AT-KR-6 for the adopted planar shapes; AT-KR-7 for Ω when scheduled;
AT-FD-7 and AT-FD-8 for the actual root mapping machinery.
**Status.** provisional and research-gated.

### D-KR-18 · Augmented arities
**Decision.** Begin from the precise set-level augmented-VDC operations and equations.
The generating graph signature has objects, vertical and horizontal edges, and cells
with ordered input paths and either one or zero horizontal outputs, including `(0,0)`
cells. Write all incidence maps, both vertical-cell compositions, identities, and
substitution equations before constructing the free monad. Prove monadicity/arity
hypotheses if the BMW route is used.

Unaugmented substitution has a useful row description with shared vertical sides;
where proved, a row corresponds to an active map `[k] → [n]`. This does not extend to
all augmented shapes as an ordinary active chain: an input path of length one and
empty output has no associated active `[0] → [1]`.
Candidate augmented data therefore records the full input/output paths, cells including
empty-output cells, vertical boundaries, and their incidence/substitution structure.
Rows with output flags are a proposed serialization only. Their valid composites,
normalization, morphisms, and arity theorem must be proved before they become the
canonical format. A specialized algebraic presentation remains acceptable if rows fail.

The early examples include `c₁^∅`, `(0,0)` cells and both compositions, nullary inputs,
shared-side compositions, and mixed rows. The no-horizontal fragment must recover
2-categories by the discrete nerve comparison.
**Rationale.** Augmentation changes the combinatorics; serialization cannot establish it.
The current presentation separates incident row shapes from cell labels and
centralizes transport along equality of complete boundaries. Algebra equations use
ordinary equality after that transport. This provisional refinement keeps substitution
incidence independent of labels and avoids reconstructing dependent reindexing in
clients. Checked round trips preserve the existing rows; they do not establish
canonical arities.
**Rejected.** The previous assertion that all augmented arities are chains of active
maps in ordinary Δ; inferring a general pasting theorem from a row picture.
**Acceptance.** AT-FD-7, AT-KR-8; AT-KR-3 only after the explicit presentation exists.
**Status.** provisional algebra presentation; arity and diagram-model results remain open.
The equation families and their dependent incidence proofs are encoded in
`Kernel/Augmented/Algebra.lean`; `AdditiveModel.algebra` supplies a nontrivial lawful
model. `forest/augmented-algebra.tree` and `forest/augmented-transport.tree` index
the revised API, renewed model evidence, strict 2-category extraction and reverse
operation data. `forest/augmented-comparison.tree` adds the reverse algebra laws,
cell/hom round trips, arbitrary substitution compatibility and discrete hom nerves.
`forest/augmented-free-cells.tree` records the relative free cell algebra, its
proved quotient laws and universal property over fixed vertical/horizontal incidence.
`forest/augmented-generating.tree` adds the generating presheaf base, free vertical
paths, change of base for lawful algebras and a global free mapping property.
`forest/augmented-monadicity.tree` records the categorical adjunction, all five
reconstructed law families, action identification and comparison equivalence.
`forest/augmented-arity-nerve.tree` constructs both monadic comparisons and the
canonical comparison for the actual free-arity nerve square. Its conditional
recognition theorem requires density and comparison invertibility for the
selected arities. Provisional status is retained because the actual arity
presentation and its exactness proof, and the labelled diagram model required
by AT-FD-7, remain open.

### D-KR-19 · Labels and reduction
**Decision.** Once object positions are defined functorially, labelled shapes are the
category of elements of `θ ↦ (ob θ → X)`. Label reindexing and inherited structural
properties are proved. A reduced presheaf has terminal values at labelled object
positions; the category-of-elements construction alone imposes no such condition.
**Rationale.** External labels do not force a presheaf's object values to be discrete.
**Rejected.** Contractibility as sufficient justification for strict object gluing.
**Acceptance.** AT-KR-9 for Δ_X, AT-FD-3 for root boundaries and label reindexing.
**Status.** provisional until the underlying arity category and reduction are checked.

### D-KR-20 · Additional shapes on demand
**Decision.** Δ and the join/comma shapes needed for M-F/M4 come first. The join API for
Segal categories includes the necessary derived construction; a category-level join
alone is insufficient. Δ₊ and its truncation inclusions support the Čech example.
Double nerves use a constructed bisimplicial indexing diagram, not an assumed inclusion
`Δ×Δ → Θ^aug_fc`. `Tw(θ)` for spans is introduced with its variance and pullback-square
conditions at M5/M6. Ω_p, Ω, Θ_n, cubes, and sequence groupoids are scheduled only by
actual downstream use. In particular symmetric sequence groupoids are indexing
categories, not sets of matrix labels pretending to retain bijections.
**Rationale.** Shape operations need functorial definitions and specific clients.
**Rejected.** Defining all possible shapes at M1 because they may eventually be useful.
**Acceptance.** AT-UP-2/3/6, AT-SP-4; AT-KR-4 and AT-KR-7 when their clients are scheduled.
**Status.** provisional schedule.

### D-KR-21 · Cubes
**Decision.** Cubical shapes and comparison models are optional later work. Their
presentation, equations, decidable equality, and connection conventions are stated
before any cubical construction is exported. No claim about all possible cubical
Segal formalisms is needed for the current root choice.
**Rationale.** Cubes do not resolve the identified root feasibility questions.
**Rejected.** Putting a cubical theory on the immediate critical path.
**Acceptance.** A new client-specific acceptance test is required before implementation.
**Status.** later (M7+).

### D-KR-24 · Geometric substrate
**Decision.** Oriented graded posets, molecules, joins, Gray products, and geometric
pasting are optional presentations and tools after the algebraic root is validated.
Every proposed equivalence between a geometric category and an arity category specifies
morphisms as well as objects. A geometric presentation does not determine the root by
itself. A renderer can begin with the validated elementary syntax.
**Rationale.** A large general substrate should follow evidence that it helps the chosen model.
**Rejected.** Making the general pasting theorem and all geometric shape comparisons
prerequisites for the first nondiscrete root example.
**Acceptance.** AT-KR-12/13/14 are deferred geometric comparisons, with exact statements
required before promotion from proposed to stated.
**Status.** later (after M3, specific clients determine priority).

### D-KR-22 · Kan machinery and relative maps
**Decision.** Reuse or prove Kan complexes and fibrations, anodyne maps, weak equivalences,
mapping complexes, path-space homotopy fibres, and the pushout-product lemmas needed
by the selected diagram model. A Kan fibration with contractible fibres over all
vertices is a trivial fibration; coherent sections use a proved lifting theorem.
Relative mapping restrictions are Kan fibrations only with the specified source
cofibration and fibrant target hypotheses. Homotopy invariance is first proved for
levelwise weak equivalences in that model. Categorical invariance is a separate theorem.
Keep boundary representatives when forming fibres; there is no path-independent
transport theorem for arbitrary Kan fibrations.
**Rationale.** These are the exact tools used by the repaired `MapRel` and `Mod`.
**Rejected.** Generic claims of cartesian closure or replacement for an unspecified model.
**Acceptance.** AT-KR-10, AT-FD-3, AT-FD-6, AT-FD-8.
**Status.** provisional inventory-dependent implementation; needed fragments at M-F.

### D-KR-23 · Reduced Reedy replacement
**Decision.** Construct a functorial replacement in the selected diagram model,
relative to reduced object values. Prove levelwise equivalence, the appropriate
fibrancy, preservation of the homotopy Segal conditions, and compatibility with label
reindexing used by the root. This is distinct from categorical completion of Segal
categories. If a replacement is needed for a whole diagram of walking structures,
perform it coherently on that diagram.
**Rationale.** A collection of pointwise replacements does not define a functor.
**Rejected.** Treating Bergner's Segal-category results as a proof for arbitrary
augmented shapes; calling every replacement a DK-equivalence without comparison.
**Acceptance.** AT-KR-11, AT-FD-3, AT-FD-8.
**Status.** provisional; the root instance is an M-F gate, general packaging M2.

## Acceptance catalogue and open questions

AT-KR-0 is the inventory; 1 is Δ comparison; 2 is the general nerve theorem with its
hypotheses; 3 is explicit presentations; 4 is Θ_n; 5 is Δ's pattern; 6 is elegance for
named adopted shapes; 7 is Ω's generalized-Reedy structure; 8 is the augmented discrete
nerve theorem; 9 is labelled Δ; 10 is the exact Kan closure list; 11 is reduced Reedy
replacement; 12/13/14 are deferred geometric comparisons. All are proposed until
linked to Lean statements and proofs. M-F gates specify the subset needed early.

OQ-KR-1: choose the symmetric-operad arity proof when Ω is needed.
OQ-KR-2: establish an augmented arity presentation that handles empty outputs and
vertical 2-cells; do not freeze the row encoding in advance.
OQ-KR-3: choose the Ω equivariant model separately from the root diagram model.
OQ-KR-4: if root elegance fails, identify an actual alternative with sufficient
cofibrancy/replacement theorems, or revise the root model at M-F.

# 00 · Charter

## Purpose

A Lean 4 library of category theory whose only primitive is the virtual double
∞-category, built so that ordinary categories, ∞-categories, enriched and internal
categories, and equipments are instances of one definition rather than parallel
developments, and so that every theorem is proved once against an interface and never
against an implementation.

The library is built by agents against definitions frozen by a human. The definitions,
their acceptance tests, and the interface are the product. Proofs are the cost of goods.

## Non-goals

- Not a general-purpose mathematics library. Algebra, analysis, and topology are out of
  scope; "spaces" are Kan complexes and geometric realization is never needed.
- Not a contribution to Mathlib. Mathlib is scaffolding (→ D-CH-08) and is hidden after the seal.
- Not constructive. Universal properties are propositions and witnesses are chosen classically (→ D-CH-02).
- Not a home for defeq-based ergonomics. If a proof closes by `rfl` against an implementation, it is wrong for this library (→ D-CH-01).
- Not a library of strict higher category theory. Strict ω-categories, computads, orientals,
  and rewriting exist in the kernel only, to build shape categories; nothing strict survives the seal.

## Principles

### D-CH-01 · Interface over implementation
**Decision.** Theory files see only sealed interfaces. No theorem in the theory layer
may depend on how any sealed object unfolds. Definitional equalities are permitted only
inside the kernel and root stages, which are hidden.
**Rationale.** A proof that goes through by unfolding is a proof about a model. It
cannot be instantiated in an enriched, internal, or ∞ setting where the composite
unfolds to nothing. Mathlib's category theory is saturated with such proofs, which is
why its 1-categorical results are re-proved rather than instantiated in its own
enriched and quasi-category developments.
**Rejected.** Soft discipline (docs and code review). Rejected because agents will
find and exploit every unfolding that typechecks; the seal must be mechanical (→ D-RT-13, D-TL-06).
**Status.** frozen.

### D-CH-02 · "A, not the"
**Decision.** Every universal object is *a* witness of a Prop-valued universal
property. No global choice functions (`limit F`, `X ⨯ Y`) exist. `lift`-style operations
are `Classical.choose` on unique existence or contractibility. Theorems quantify over
witnesses. Witnesses of a given universal property form a contractible space (1-level:
a contractible groupoid), and transport between witnesses is functoriality in the witness.
**Rationale.** Definitional uniqueness is a lie about mathematics; contractibility of the
witness space is the truth, and it is the statement that survives the passage to ∞.
**Rejected.** Data-valued universal properties with `Subsingleton` instances (keeps a
constructive door open, but reintroduces the temptation to unfold `lift`). Chosen-limit
typeclasses (instance diamonds).
**Status.** frozen.

### D-CH-03 · Unbiased and shape-indexed
**Decision.** Limits are indexed by shapes, never iterated binary operations. Products are
limits over finite sets; towers are diagrams over Δ. Where classical treatments have
coherence (associators, pentagons), this library has functoriality in a shape category
and Kan extension along shape inclusions. The paradigm operation is "extend to the
Amitsur/Čech diagram": `cosk₀` in augmented simplicial objects over a base.
Monoidal structure, when it arrives, is representability of multimaps, not a tensor with axioms.
**Rationale.** Coherence problems are artifacts of biased presentations. The unbiased
presentation makes them theorems proved once (Mac Lane, Hermida) rather than normal forms maintained forever.
**Consequence.** No coherence tactic on the critical path. "Extend along a shape
inclusion" tooling is on it (→ D-TL-05).
**Status.** frozen.

### D-CH-04 · Nothing special-cased
**Decision.** There is one root definition (→ D-RT-01). `Category` is a monad in
`Mat(Set)` (→ D-RT-10). ∞-categories are monads in `Mat(Kan)` (→ D-SP-04). Functors,
profunctors, natural transformations are the vertical morphisms, horizontal morphisms,
and cells of `Mod(-)`. The 2-category `Cat` is never defined; it is the vertical
2-category of `Mod(Mat Set)`. Universal properties in `Cat` are those of the vertical
∞-category of the corresponding VDC∞, hence 2-dimensional automatically.
**Rationale.** Every special case is a place where a theorem gets proved twice and the
two copies drift. The formal theory (→ 04) is stated once for augmented virtual ∞-equipments.
**Status.** frozen.

### D-CH-05 · ∞ first, Segal style, labelled, E1, augmented
**Decision.** The root is defined at the ∞ level from the start, as a Segal presheaf
on a shape category ("style B"): a Kan-complex-valued presheaf on the labelled,
augmented shape category `Θ^aug_{fc,X}` satisfying a Segal condition (→ D-RT-01).
Objects form a *set* (labels); vertical morphisms, horizontal morphisms, and cells form
spaces. Cells have ordered inputs (E1/planar); there is no symmetric variant at the root.
Cells may have empty target (augmented, after Koudenburg).
**Rationale.** Style B has honest shapes (leveled grids: chains of active maps in Δ, once
the shared-sides rule of virtual composition is taken seriously, → D-KR-06), strict maps
as the right maps, and levelwise-combinatorial equivalences; it plugs directly into the Reedy/EZ machinery of the kernel. Labels make
Segal conditions over objects into products and remove the need for a completeness
condition (Segal-category style, Hirschowitz–Simpson/Bergner). Augmentation makes
Yoneda for large objects a structural fact rather than a universe hack (→ D-RT-12).
**Rejected.** Style A (fibrations over `N(Δᵒᵖ)`, Gepner–Haugseng generalized
non-symmetric ∞-operads): correct, equivalent, but simplicial encoding of tree-shaped
data and needs Lurie's fibration toolkit; retained as a comparison target only.
Rezk-style unlabelled objects (space of objects, completeness condition). Cubical shapes
(no spines, so no Segal conditions; retained for fibrant-object models, → D-KR-09).
**Note on E1.** E1-only at the root does not exclude symmetric structures: symmetry
enters as a monad `T` on the ambient equipment, and `T`-monoids are monads in the
horizontal Kleisli VDC∞ `H-Kl(T, X)` (Cruttwell–Shulman, → D-SP-09), which is again an
E1 object of the root. Symmetric sequences under the composition product are the
one-object case. What E1-only excludes is presenting `E_n` (`n ≥ 2`) as *non-symmetric*
operads; the braiding is the equivariance. Symmetry is never put into the shapes: cell
inputs are paths ordered by composability, and automorphisms in the root shape category
would cost elegance everywhere.
**Status.** frozen.

### D-CH-13 · Closure and invariance
**Decision.** The interface is closed under the constructions it offers, in the sense
quasi-category theory is: fibrancy is an exported property, standard objects are exported
fibrant, and every exported construction (`Mod`, slices, functor objects, limits, `Span`)
comes with (a) a fibrancy-preservation theorem, (b) a DK-invariance theorem, and
(c) where it produces mapping spaces, a rectification theorem saying strict maps into
strict models hit every component. Definitions in 02–05 are chosen so that (a)–(c) are provable.
**Rationale.** In a strict-model design nothing is invariant or fibrant by construction.
Quasi-category theory is usable because its toolkit (horn filling, `Fun`, joins, mapping
spaces) is closed and rectification populates it; the same list, transposed, is what makes
this library usable rather than merely correct.
**Status.** frozen.

### D-CH-06 · Definitions are the product
**Decision.** Every definition-level decision ships with acceptance tests: Lean
statements whose proofs are the evidence that the definition is the intended one.
Where the literature has the notion (discrete case, non-virtual case), the acceptance
test is a comparison theorem. Where it does not, the acceptance test is the truncation or
restriction to a case where it does.
**Rationale.** The FLT formalization shows that once definitions and a blueprint exist,
the coherence grind scales to millions of lines. It does not show that definitional
judgment in unexplored territory scales. FLT had Wiles as an oracle; here the oracle
must be built in.
**Status.** frozen.

### D-CH-07 · Layering
**Decision.** Agent-native artifacts (Lean sources, generated forest nodes, acceptance
tests, decision registry) are primary. Human-facing documentation and human-facing APIs
(notation, `abbrev` wrappers, prose) are generated layers over them and are never
hand-maintained against the primary. What "agent-native" means is deliberately left
undefined (→ D-TL-01).
**Status.** frozen.

## The bootstrap

### D-CH-08 · Three stages
**Decision.**
- **Kernel** (stage 0, directory `Kernel/`): shape categories, presheaves, simplicial sets,
  Kan machinery, set-level virtual double categories used only to construct shapes. Built
  on Mathlib's `CategoryTheory` and `AlgebraicTopology`. Defeq allowed. Nothing exported.
- **Root** (stage 1, `Root/`): the VDC∞ definition and its immediate constructions, built
  on the kernel; the discrete embedding and the self-hosting theorem (→ AT-RT-1). Also
  hidden. Its public face is `Interface/`.
- **Theory** (stage 2, `Theory/`): everything else, in interface terms only.
**Rationale.** Compiler bootstrap pattern. The kernel is never rewritten in place, only
hidden; a self-hosted replacement is a separate kernel that must pass the same swap test (→ D-CH-12).
**Status.** frozen.

### D-CH-09 · Hard seal
**Decision.** CI rejects any file under `Theory/` importing `Mathlib.CategoryTheory.*`,
`Mathlib.AlgebraicTopology.*`, `Kernel.*`, or `Root.*`. Anything needed is copied or
ported into `Interface/` through the seal mechanism (→ D-RT-13). Mathlib *tactics*
(`Mathlib.Tactic.*`, `Aesop`, `omega`, `decide`, `positivity`, etc.) are allowed everywhere.
**Rationale.** Tactics are not definitions; they cannot leak defeq about our objects
except through unfolding, which the linter forbids independently.
**Status.** frozen.

### D-CH-10 · Full universe polymorphism
**Decision.** Everything is universe-polymorphic from the start; no fixed hierarchy.
Detailed policy → D-RT-12.
**Status.** frozen (policy details provisional).

### D-CH-11 · Dependencies
**Decision.** Mathlib only. No Infinity-Cosmos, no other Lean libraries. Their
constructions may be ported into the kernel with attribution.
**Status.** frozen.

### D-CH-12 · Self-hosting and axiom-wlog
**Decision.** After the seal, the interface is a set of `opaque` constants with an
inhabitation witness from the kernel. A self-hosted kernel (no Mathlib) is on the
roadmap (M7). A build variant may replace the kernel by axioms for speed; the
kernel-backed build remains the consistency witness and runs in CI.
**Rationale.** `opaque` is Lean's native "axiom without loss of consistency": the body
is invisible to the elaborator and the kernel alike, so the theory literally cannot
depend on it.
**Status.** frozen.

## Success criteria

1. The swap test (→ D-TL-06) is green: `Theory/` builds against a stub interface whose
   constants are bodiless axioms.
2. The self-hosting theorem (→ AT-RT-1) is proved: discrete VDC∞s are exactly set-level
   augmented virtual double categories, and the discrete `Category` is exactly the classical one.
3. Yoneda, weighted limits, Kan extensions, adjunctions, and monads are each stated once
   for augmented virtual ∞-equipments (→ 04) and their discrete specializations coincide
   with Cruttwell–Shulman and Koudenburg (→ AT-FT-1).
4. Segal categories, i.e. monads in `Mat(Kan)`, are the ∞-categories of the library,
   with no separate definition (→ AT-SP-2).

## Glossary

- **VDC∞** — virtual double ∞-category, the root object (→ D-RT-01).
- **Labelled** — objects are a set `X`; shapes carry labels in `X` at object positions.
- **Augmented** — cells may have empty horizontal target (Koudenburg).
- **E1** — inputs of cells are ordered; no symmetries at the root.
- **Segal condition** — the value at a shape is the (homotopy) limit of values at its elementary sub-shapes.
- **DK-equivalence** — Dwyer–Kan equivalence: essentially surjective and fully faithful, spelled out in → D-RT-06.
- **Sealed** — visible only through `Interface/`; unfolding forbidden by mechanism.
- **Witness** — an inhabitant of `{x // universalProperty x}`.
- **Acceptance test** — a Lean statement whose proof is evidence a definition is right.
- **Shape** — an object of one of the kernel's shape categories (Δ, Ω_p, Θ_fc, …). For
  `Θ_fc`, a pasting scheme: a leveled grid of cells, i.e. a chain of active maps in Δ.

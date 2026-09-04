# 01 · Kernel (stage 0)

The kernel builds the combinatorial raw material — shape categories, presheaves,
simplicial sets, Kan machinery — on top of Mathlib. It is scaffolding: defeq is
allowed, Mathlib's `CategoryTheory` is used freely, and nothing here is visible past the
seal. The kernel is judged only by whether `Root/` can be built on it and whether the
acceptance tests below are proved.

## Rules

### D-KR-01 · What the kernel may contain
**Decision.** Anything convenient, including a set-level definition of (augmented)
virtual double categories and of free ones. These exist *only* to construct shape
categories and to state the self-hosting theorem; they are not the library's notion of
VDC, which is the discrete case of the root (→ D-RT-11). Kernel files are marked
`-- KERNEL` and live under `Kernel/`.
**Rationale.** Weber's construction of shape categories needs the algebras whose free
objects the shapes are (→ D-KR-03). Refusing to write set-level VDCs in the kernel would
force an ad hoc tree combinatorics as the *definition* of `Θ_fc` and make the nerve
theorem a correctness gamble instead of an instance of a general theorem.
**Status.** frozen.

### D-KR-02 · Mathlib inventory (M0 task, AT-KR-0)
**Decision.** Before M1, produce a verified inventory of what Mathlib (pinned version)
provides, with exact names. Expected candidates, none assumed:
`CategoryTheory.{Category, Functor, NatTrans, Limits, Comma, Grothendieck, MorphismProperty}`,
lifting properties and the small object argument (Riou), `SimplexCategory`,
`SimplicialObject`, `SSet` with `boundary`/`horn`, `SSet.KanComplex`, `Nerve`,
truncations and skeleta, `Quasicategory`, joins/slices if present, any Kan–Quillen
model structure material, `Fin` combinatorics and `omega`. Record for each: name,
statement as we need it, gaps. The inventory is a forest node and is updated at each Mathlib bump.
**Rationale.** Every earlier plan in this design assumed Mathlib content that had to be
hedged. The inventory converts hedges into tasks.
**Status.** frozen.

## Shapes

### D-KR-03 · One recipe: monads with arities
**Decision.** Shape categories are defined uniformly as Weber's `Θ_T`: for a monad `T`
with arities (Berger–Melliès–Weber) on a presheaf category `PSh(G)`, `Θ_T` is the full
subcategory of `T`-algebras on the free algebras `T(E_t)` over the arities `E_t`
(equivalently, the full subcategory of the Kleisli category on the arities). Weber's
generic/free factorization on `Θ_T` is the active/inert factorization; the elementary
objects are the free algebras on the representables of `G`. The nerve theorem (BMW) is
formalized **once**: the nerve `T-Alg → PSh(Θ_T)` is fully faithful, with essential
image the presheaves satisfying the Segal condition (→ D-KR-04). Each shape's nerve
theorem is an instance.

| Shape | `G` (generating shapes) | `T` | Expected `Θ_T` |
|---|---|---|---|
| Δ | graphs (vertex, edge) | free category | Δ (identified with `SimplexCategory`, AT-KR-1) |
| Ω_p | planar multigraphs | free planar (non-symmetric) coloured operad | planar dendroidal category (Moerdijk–Weiss `Ω_p`) |
| Ω | symmetric multigraphs | free symmetric coloured operad | dendroidal category `Ω` **(verify BMW applies; fallback: Moerdijk–Weiss's definition directly)** |
| Θ^aug_fc | double graphs `G_fc` | free augmented VDC | trees with vertical sides (D-KR-06) |
| Θ_n | — | — | defined by Berger's wreath product `Δ ≀ Θ_{n−1}` (→ D-KR-08); identification with `Θ_T` for the free strict `n`-category monad is optional |

**Rationale.** One theorem, five shapes. The recipe also fixes *what the shapes are*
without any tree combinatorics being taken on faith: the explicit tree descriptions are
theorems (AT-KR-3), needed for Reedy structures but not for correctness.
**Rejected.** Ad hoc inductive tree categories as definitions. Rejected as definitions,
retained as presentations.
**Acceptance.** AT-KR-1 (Δ ≅ `SimplexCategory`), AT-KR-2 (BMW nerve theorem, general),
AT-KR-3 (explicit presentations), AT-KR-4 (`Θ_1 ≅ Δ`, `Θ_2 ≅ Δ ≀ Δ`).
**Status.** frozen for Δ, Ω_p, Θ^aug_fc; provisional for Ω (pending the BMW check).

### D-KR-04 · Patterns and Segal cores
**Decision.** Every shape category carries an *algebraic pattern* structure in the
sense of Chu–Haugseng: an inert/active factorization system (`Θ⁻` degeneracies are
separate, see D-KR-05) and a class of elementary objects. For a shape `θ`, the Segal
core `Sc(θ)` is the diagram of elementary inert sub-shapes of `θ`. A presheaf `P` (in
sets or in `sSet`) satisfies the **Segal condition** at `θ` when the canonical map
`P(θ) → lim_{Sc(θ)} P` is an isomorphism (sets) or a homotopy equivalence (spaces,
→ D-RT-01 for the precise form). For `Θ_T` the inert maps are Weber's free maps and the
Segal core is the canonical presentation of the arity `E_t` as a colimit of representables.
**Rationale.** This is exactly the hypothesis of the BMW nerve theorem in the discrete
case and of Chu–Haugseng's Segal-space machinery in the homotopical case; using their
vocabulary keeps our comparisons honest.
**Acceptance.** AT-KR-5: for Δ, inert = interval inclusions, active = endpoint-preserving,
elementary = `[0],[1]`, and the Segal condition is the usual one.
**Status.** frozen.

### D-KR-05 · Reedy, elegant, generalized Reedy
**Decision.** Each shape category is equipped with a Reedy structure (degree,
`Θ⁺` = monomorphisms/faces including active ones, `Θ⁻` = degeneracies/collapses).
Planar shapes (Δ, Ω_p, Θ_fc, Θ_n, Δ×Δ) are expected to be **elegant** Reedy categories
(Bergner–Rezk: every presheaf's degenerate elements are uniquely degeneracies of
non-degenerate ones; Reedy cofibrations are monomorphisms; every object is cofibrant).
Ω has automorphisms and is a **generalized Reedy** category in the sense of
Berger–Moerdijk (EZ category); there the cofibrant objects are the *normal*
presheaves and Reedy fibrancy involves `Aut`-equivariance.
Labelled shape categories `Θ_{T,X}` (D-KR-07) inherit the Reedy structure along the
discrete fibration to `Θ_T`.
Machinery: latching/matching objects, skeleta/coskeleta, the Reedy lemma for
presheaves valued in `sSet`, Reedy fibrancy (→ D-RT-07).
**Acceptance.** AT-KR-6: elegance of Δ, Ω_p, Θ^aug_fc **(verify for Θ_fc; expected)**;
AT-KR-7: Ω is EZ/dualizable generalized Reedy.
**Status.** frozen (the list of which shapes are elegant is provisional until AT-KR-6).

### D-KR-06 · `G_fc` and `Θ^aug_fc`
**Decision.** The category of double graphs is `PSh(G_fc)` where `G_fc` has objects
`pt`, `v` (vertical edge), `h` (horizontal edge), `c_n` (cell with `n ≥ 0` inputs and one
output), `c_n^∅` (cell with `n ≥ 0` inputs and empty output, the augmented cells), and
generating maps `s,t : pt → v`, `s,t : pt → h`, `in_i : h → c_n` (`1 ≤ i ≤ n`),
`out : h → c_n`, `l, r : v → c_n` (left and right sides), the same for `c_n^∅` without
`out`, subject to the incidence relations (input `i` ends where input `i+1` starts; the
left side runs from the start of input 1 to the start of the output; the right side from
the end of input `n` to the end of the output; for `n = 0` the single input object is
shared by both sides; for `c_n^∅` both sides end at the same object).
A set-level augmented VDC is a double graph with vertical composition of vertical edges,
multicategorical composition of cells (including Koudenburg's rule for cells with empty
target), unit vertical edges, unit cells, and the associativity/unit laws. The free
augmented VDC on a double graph is constructed explicitly (cells are planar trees of
generating cells with vertical paths along the sides, modulo unit laws).
`Θ^aug_fc := Θ_T` for this `T`. Expected description (AT-KR-3): objects are vertical
paths, horizontal paths, and planar trees of cells with vertical sides; faces are
sub-shape inclusions and composite-selecting maps; degeneracies collapse a cell to a
unit cell of its input/output or a vertical edge to an identity.
**Rationale.** Cells have ordered inputs and one (or no) output, so the shapes are
planar trees; vertical composition is grafting along the root. This is the honest shape
category behind "virtual double"; the simplicial encoding of style A is avoided.
**Acceptance.** AT-KR-8: the nerve theorem for augmented VDCs is an instance of AT-KR-2
and its essential image is characterized by the Segal condition of D-KR-04.
**Status.** frozen (the exact list of incidence relations is provisional until formalized).

### D-KR-07 · Labelled shapes `Θ_{T,X}`
**Decision.** For `X : Type u`, `Θ_{T,X} := ∫_{Θ_T} X^{ob(−)}`, the category of elements
of the presheaf `θ ↦ (ob θ → X)` where `ob : Θ_T → Set` gives the object positions of a
shape. Objects are labelled shapes, morphisms are shape maps preserving labels.
A function `X → Y` induces `Θ_{T,X} → Θ_{T,Y}`.
**Rationale.** Gepner–Haugseng's `Δ_X` generalized. Labels discretize objects: Segal
conditions over object positions become products.
**Acceptance.** AT-KR-9: `Δ_X` agrees with the labelled simplex construction; the
Segal condition on `Δ_X` characterizes categories with object set `X` (unbiased form).
**Status.** frozen.

### D-KR-08 · Other shapes
**Decision.**
- Δ₊ (augmented simplices) with its join monoidal structure; joins and slices of
  simplicial sets (needed for → D-UP-03).
- Δ×Δ for double (non-virtual) structures; used when composites exist (→ D-FT-02).
- Θ_n by Berger's wreath product, defined in M1 and unused until (∞,n) work.
- Twisted-arrow-type shapes `Tw(θ)` for each `θ ∈ Θ_fc` (Barwick, Haugseng), in which
  the pullbacks of composable spans are objects; needed for `Span(S)` (→ D-SP-05).
  Defined at M1 with the others; their Segal theory is M6.
- The groupoids `Σ_A`, `𝔹_A`, `ℕ_A` of finite `A`-coloured sets with bijections, braids,
  and identities, as the indexing categories of symmetric, braided, and non-symmetric
  sequences (→ D-SP-09).
**Status.** frozen.

### D-KR-09 · Cubes
**Decision.** The cube category with connections is defined by its PRO presentation
(Grandis–Mauri: free strict monoidal category on an interval object with connections),
included in the kernel as a *shape for horn-filling models only* (cubical Kan
complexes, cubical (∞,1)-categories after Doherty–Kapulkin–Lindsey–Sattler, and, via
connections as companion/conjoint squares, equipments with all companions). It carries
no Segal-style structure because it has no spines.
**Rationale.** Segal conditions need shapes that contain their own subdivisions
(`[2] ⊃ [1] ∨ [1]`); cubes only have `I^n`. The library's root is Segal-style, so cubes
are auxiliary.
**Status.** frozen; `later` for any use beyond definition.

## Kan machinery

### D-KR-10 · Spaces are Kan complexes
**Decision.** The kernel provides: Kan complexes; Kan fibrations and trivial fibrations
as lifting properties; anodyne maps; simplicial homotopy (an equivalence relation on
maps into Kan complexes); homotopy equivalences; `π₀`; contractibility; mapping spaces
`L^K` and the exponential law; the pushout-product lemma (needed for `U^{Δ[1]} → U × U`
fibrations, → D-SP-01); homotopy fibre products via path spaces and the lemma that a
strict fibre product along a fibration is a homotopy fibre product; Reedy fibrancy for
`sSet`-valued presheaves on the shapes of D-KR-05; the fact that discrete presheaves are
Reedy fibrant and every map of discrete simplicial sets is a Kan fibration. Sourced from
Mathlib wherever the inventory (D-KR-02) finds it.
The **closure package** (→ D-CH-13), proved here and exported through the interface:
mapping spaces of presheaves `Map(A, P)` for `A ↪ B` a monomorphism and `P` Reedy
fibrant give Kan fibrations `Map(B,P) → Map(A,P)`; exponentials of Reedy fibrant
objects by cofibrant ones are Reedy fibrant; fibre products along Reedy fibrations are
Reedy fibrant; a Kan fibration with contractible fibres over every vertex is a trivial
fibration; homotopy invariance of `Map` in both variables among cofibrant sources and
fibrant targets.
**Rationale.** Every definition in `Root/` is stated with these words and nothing
heavier. Model structures are not needed for definitions and appear only as theorems
(→ D-SP-08). The closure package is what lets `Theory/` prove that its own
constructions preserve fibrancy without seeing the kernel.
**Acceptance.** AT-KR-10: the standard closure properties (composition, pullback,
retract, exponentials) for Kan and trivial fibrations, as a Lean theorem list.
**Status.** frozen.

### D-KR-11 · Fibrant replacement (statement here, proof at M2)
**Decision.** For elegant shapes, there is a functorial Reedy-fibrant replacement of
Segal presheaves that preserves the label set and is a levelwise homotopy equivalence
on elementary values; for `Δ_X` this is Bergner's fibrant replacement for Segal
categories. The kernel proves the version needed by → D-RT-07.
**Rationale.** Natural examples (strict simplicial categories, `Mat(Kan)`) are Segal but
not Reedy fibrant; derived mapping spaces need a fibrant target.
**Acceptance.** AT-KR-11: replacement exists and is a DK-equivalence (→ D-RT-06).
**Status.** provisional (proof strategy to be chosen at M2: Bergner-style small object
argument along the elementary boundary inclusions is the default).

## Acceptance tests (summary)

- AT-KR-0 Mathlib inventory node exists and is verified.
- AT-KR-1 `Θ_T(free category) ≅ SimplexCategory`.
- AT-KR-2 BMW nerve theorem, general form.
- AT-KR-3 Explicit presentations of Δ, Ω_p, Θ^aug_fc as tree/path categories.
- AT-KR-4 `Θ_1 ≅ Δ`, `Θ_2 ≅ Δ ≀ Δ`.
- AT-KR-5 Pattern structure on Δ is the classical one.
- AT-KR-6 Elegance of Δ, Ω_p, Θ^aug_fc.
- AT-KR-7 Ω is EZ generalized Reedy.
- AT-KR-8 Nerve theorem for augmented VDCs with Segal characterization.
- AT-KR-9 Labelled Δ characterizes categories with a given object set.
- AT-KR-10 Closure properties of Kan/trivial fibrations.
- AT-KR-11 Fibrant replacement.

## Open questions

- OQ-KR-1 Does BMW's framework cover the free symmetric operad monad directly, or
  do we define Ω à la Moerdijk–Weiss and prove the nerve theorem separately? (M1)
- OQ-KR-2 Should `G_fc` include a separate `c_n^∅` for each `n`, or is augmentation
  better encoded as an extra object "empty target" with cells targeting it? (Affects the
  explicit tree presentation; decide when formalizing D-KR-06.)
- OQ-KR-3 Which Reedy-fibrancy convention for Ω (Berger–Moerdijk projective on
  `Aut`-objects is the default).

# 05 · Spaces and enrichment (stage 2, M6)

Post-seal homotopy theory: the ∞-category of spaces, `Mat(Kan)`, ∞-categories as
monads in it, Segal spaces via `Span(Kan)`, ∞-operads via `Ω`, and the comparison
milestones. Only the interface `Space` API (→ D-RT-13) and the root are used.

### D-SP-01 · The universe
**Decision.** `U.{v}` is the Kan complex of small Kan fibrations (Kapulkin–Lumsdaine–
Voevodsky; Cisinski's construction): `U_n` is the set of small Kan fibrations over
`Δ[n]` with a set-theoretic normalization making it a set, and the universal small Kan
fibration `Ũ → U`. Theorem: `U` is a Kan complex. Consequence: `U^{Δ[1]} → U × U` and
the higher `U^{Δ[n]} → U^{∂Δ[n]}` are Kan fibrations (exponential/pushout-product,
→ D-KR-10). Univalence is optional and out of scope until needed.
**Rationale.** The universe is the space of objects of `Kan` and the source of the
boundary fibrancy of `Mat(Kan)` (→ D-RT-01 (2)). It replaces the homotopy coherent nerve
on the critical path.
**Acceptance.** AT-SP-1: `U` is a Kan complex (proof strategy chosen at M6: Cisinski's
argument or Sattler's equivalence extension property; minimal fibrations are the
fallback).
**Status.** frozen at M6.

### D-SP-02 · The Segal category `Kan`
**Decision.** `Kan` is exported as a *fibrant* Segal category with object set the small
Kan complexes, with the API: `Kan(K, L) ≃ L^K` (homotopy equivalence), composition
agreeing with composition of maps up to homotopy, and the rectification theorem that
the strict simplicial category (`Kan(K,L) = L^K`, strict composition) maps to it by a
DK-equivalence. How the fibrant object is obtained is a kernel choice (OQ-SP-3): either
the strict simplicial category followed by fibrant replacement, or a fibrant-by-
construction model in the Rezk/Rasekh style (value at `([n]; K₀…K_n)` the Kan complex
whose `m`-simplices are left fibrations over `Δ[n] × Δ[m]` that are Kan fibrations in
the `Δ[m]` direction, with the prescribed vertex fibres), built from the universe
(→ D-SP-01). Past the seal the difference is invisible. `S` (Cisinski's quasi-category
of spaces) is a later comparison target (→ D-SP-08), not a prerequisite.
**Rationale.** No coherent nerve, no necklaces. What Theory needs is fibrancy as a
property plus rectification (→ D-CH-13), not a particular model.
**Acceptance.** AT-SP-2: `Kan` is a monad in `Mat(Kan)` (i.e. an ∞-category in the
library's sense), its homotopy category is the classical homotopy category of Kan
complexes, and the strict simplicial category rectifies it.
**Status.** frozen at M6.

### D-SP-03 · Enrichment over cartesian `V`
**Decision.** Before general monoidal enrichment, only *cartesian* value categories
are supported: `V = Set` (discrete) and `V = Kan`. Cells in `Mat(V)` are families of
maps out of products. General E1-monoidal `V` is → D-SP-07.
**Status.** frozen.

### D-SP-04 · `Mat(Kan)` and ∞-categories
**Decision.** `Mat(Kan.{v})` is the VDC∞ with label set `Type v`, vertical morphisms
functions, horizontal morphisms `A ⇸ B` the space `∏_{A×B} U` of families of small Kan
complexes, and cells `(M₁,…,M_n) ⇒ N` over `(f,g)` the spaces of families of maps
`M₁(a₀,a₁) × ⋯ × M_n(a_{n−1},a_n) → N(f a₀, g a_n)`, built from the universal fibration
so that boundary maps are Kan fibrations; nullary-target cells as in → D-RT-10 (verify).
`Mat(Kan)` is exported *fibrant* (→ D-RT-07, D-CH-13) with the same two options as
D-SP-02 for how (OQ-SP-3), and with its elementary values characterized up to homotopy
equivalence (`Mat(Kan)(h(A,B)) ≃ ∏_{A×B} U`, cell spaces ≃ products of mapping spaces).
`InfCategory A := Monad (Mat Kan) A` for a set `A`; `Cat_∞ := Mod(Mat Kan)`.
**Theorem targets.** `Mat(Kan)` is a VDC∞ and fibrant (AT-RT-8). Monads in `Mat(Kan)`
at `A` are exactly Segal categories with object set `A` (AT-SP-3, the Gepner–Haugseng
categorical algebra statement in Segal-category form); since `Mat(Kan)` is fibrant,
this is an equivalence between strict maps `N Mnd → Mat(Kan)` at `A` and labelled Segal
presheaves on `Δ_A` up to DK-equivalence, and either side may be used as the working
form of "∞-category with object set `A`". Rectification (Dwyer–Kan, Bergner): strict
simplicial categories with object set `A` present every such Segal category
(AT-SP-8). `Vert(Cat_∞)` is the ∞-category of ∞-categories, functors, and natural
equivalences; natural transformations are cells (→ D-UP-09).
**Rationale.** → D-CH-04: ∞-categories are not defined; they are monads in one VDC∞.
The rectification theorem is what lets anyone write one down.
**Status.** frozen at M6.

### D-SP-05 · `Span(S)` and Segal spaces
**Decision.** For a Segal category `S` with finite limits (→ D-UP-04), `Span(S)` is
defined by shapes, not by choices: the kernel provides for each `θ ∈ Θ_fc` the
twisted-arrow-type shape `Tw(θ)` in which every composable configuration of spans has
its pullback squares as *objects*, and `Span(S)(θ)` is the sub-space of `Map(N Tw(θ), S)`
on diagrams whose designated squares are pullbacks (a property, so functoriality in `θ`
is restriction). This is Barwick's and Haugseng's construction of iterated spans; that
`Span(S)` satisfies the Segal condition is their theorem, transposed (AT-SP-4).
Vertical morphisms are `S(a,b)`, horizontal morphisms spans, cells maps out of the
pullbacks recorded in the diagram. `Mod(Span Kan)` has as monads the Segal spaces
(category objects in spaces, Rezk).
**Rejected.** Choosing pullbacks per shape with `Classical.choose`: choices are not
compatible under shape maps, so no presheaf results. (Choosing a *section* per D-UP-06
would work for a single shape but not across the shape category.)
**Theorem target.** AT-SP-4: `Span(S)` is a VDC∞, fibrant when `S` is; AT-SP-5
(comparison, Bergner): `Mod(Mat Kan)` and `Mod(Span Kan)` are DK-equivalent VDC∞s —
families versus spans at the ∞ level.
**Rationale.** Spans return exactly where objects stop being a set. The comparison is
the library's version of "Segal categories ≃ Segal spaces".
**Status.** frozen at M6 (AT-SP-5 is a milestone, not a prerequisite).

### D-SP-06 · ∞-operads via `Ω`
**Decision.** A planar ∞-operad is a Segal presheaf `Ω_pᵒᵖ → sSet` with Kan values and
the Segal condition (the planar version of Cisinski–Moerdijk's dendroidal Segal spaces);
a symmetric ∞-operad is the same on `Ω` with the Segal condition and the generalized
Reedy conventions of → D-KR-05. Labelled variants over a set of colours.
**Theorem targets.** AT-SP-6: the discrete cases are planar/symmetric coloured operads
(nerve theorems, instances of AT-KR-2); AT-SP-7: a planar coloured ∞-operad with colour
set `A` is a monad in the VDC∞ of `Ω_p`-shaped multimatrices over `Kan` **(verify: this
is the multicategory analogue of D-SP-04)**. The symmetric case is first-class through
→ D-SP-09, and the Segal-`Ω` form is its comparison target.
**Status.** frozen at M6.

### D-SP-09 · Symmetry via monads on the ambient: the horizontal Kleisli construction
**Decision.** Symmetry is never baked into the root shapes. It enters, as in
Cruttwell–Shulman, as a *monad on the ambient equipment*. For a strict monad `T` on a
VDC∞ `X` (a map `T : X → X` with unit and multiplication satisfying the laws on the
nose), the **horizontal Kleisli** VDC∞ `H-Kl(T, X)` has the objects and vertical
morphisms of `X`, horizontal morphisms `A ⇸ B` the `X`-horizontals `A ⇸ TB`, and cells
with inputs `(M₁,…,Mₙ)` and target `N` the `X`-cells `(M₁, TM₂, T²M₃, …, Tⁿ⁻¹Mₙ) ⇒ N`
over the vertical boundary obtained by collapsing with the multiplication. `T`-monoids
in `X` are monads in `H-Kl(T, X)`, and `Mod(H-Kl(T, X))` is Cruttwell–Shulman's
`KMod(T, X)`: the equipment of `T`-monoids, their functors, and their bimodules.
The monads used are strict and explicit on `Mat(Kan)`: `T_ℕ` (free monoidal
category: finite sequences), `T_𝔹` (free braided monoidal category), `T_Σ` (free
symmetric monoidal category: finite families with bijections), and more generally
`T_G` for an action operad `G` (Zhang, Gurski). Then, with a set of colours as labels:
- planar coloured ∞-operads are monads in `H-Kl(T_ℕ, Mat Kan)`,
- braided ones are monads in `H-Kl(T_𝔹, Mat Kan)`,
- symmetric ones are monads in `H-Kl(T_Σ, Mat Kan)`,
and Lawvere theories, PROPs, and other generalized multicategories are the same
construction with other `T`. The formal theory of → 04 applies to each `KMod(T, X)`
with no new definitions.
Symmetric sequences are the one-object corollary: `Mat(Kan)(1, T_Σ 1)` is families
over finite sets and bijections, and Kleisli composition is the composition product;
likewise braided and non-symmetric sequences. Construction of the composition product,
and of the Kleisli VDC∞ in general, needs colimits in `Kan` (→ D-SP-08).
`E_1`, `E_2`, `E_∞` are the *contractible* single-coloured monads in the three Kleisli
VDC∞s (Fiedorowicz for the braided case: braided operads with contractible components
and free `Bₙ`-actions present `E_2`; equivalently the symmetric operad in groupoids
with `n`-th groupoid having objects `Σₙ` and morphisms braids, whose realizations are
ordered configuration spaces of the plane). `E_n` for `3 ≤ n < ∞` has no action-operad
model — configuration spaces of `ℝⁿ` are simply connected but not aspherical
(`Conf₂(ℝ³) ≃ S²`) — and is a specific monad in `H-Kl(T_Σ, Mat Kan)` given by a
combinatorial symmetric operad in finite posets: Berger's complete-graph operad `Kₙ`
with `|Kₙ(k)| ≃ Conf_k(ℝⁿ)`, or Smith's filtration of the Barratt–Eccles operad.
Algebras over a symmetric operad `P` in a cartesian `V` with colimits (`Kan`, `Cat_∞`)
are algebras for the monad `A ↦ ⨆ₙ P(n) ×_{hΣₙ} Aⁿ`; symmetric monoidal ∞-categories
are `E_∞`-algebras in `Cat_∞` in this sense.
Shapes with symmetry reappear on the *nerve* side only: Ω is Weber's arity category for
the free `T_Σ`-multicategory monad, so Segal presheaves on Ω (→ D-SP-06) are the nerves
of monads in `H-Kl(T_Σ, Mat Kan)`, and the comparison is the nerve theorem at ∞.
**Rejected.** A "symmetric Θ_fc". The inputs of a cell form a path ordered by
composability, so permuting them does not typecheck except for endomorphisms of one
object; and any automorphisms in the root shape category would make the root
generalized Reedy (normal monomorphisms, `Aut`-equivariant fibrancy, elegance lost), a
permanent tax on `Category` for a benefit only operads want.
**Not viable, and why.** Presenting `E_n` (`n ≥ 2`) as *non-symmetric* operads (monads
in `H-Kl(T_ℕ, −)`). The underlying non-symmetric operad of a symmetric operad `P` has
algebras for the monad `⨆ P(n) × Aⁿ` instead of `⨆ P(n) ×_{hΣₙ} Aⁿ`; for `E_∞` this is
`E_1`, and for `E_2` it is `E_1` together with pure-braid-group actions on iterated
products — the braiding `a ⊗ b → b ⊗ a` is exactly the equivariance that was forgotten.
Braided operads are not non-symmetric operads; they are `T_𝔹`-monoids.
**Acceptance.** AT-SP-9: for `X = Mat(Set)`, `Mod(H-Kl(T_Σ, X))` is the classical
equipment of coloured symmetric operads, functors, and bimodules, and `T`-monoids
agree with the discrete case of D-SP-06; AT-SP-10 (comparison, Haugseng's *∞-operads
via symmetric sequences*, and the nerve theorem at ∞): monads in `H-Kl(T_Σ, Mat Kan)`
present Lurie's ∞-operads / dendroidal Segal spaces; AT-SP-11: the three contractible
monads are `E_1`, `E_2`, `E_∞` (discrete cases: monoids, braided monoidal, symmetric
monoidal categories as algebras in `Cat`); AT-SP-13: `H-Kl(T, X)` is a VDC∞, fibrant
when `X` is, and `Mod(H-Kl(T, X))` is an augmented virtual ∞-equipment when `X` is
(Cruttwell–Shulman's theorem, transposed; the conditions on `T` are part of the task).
**Status.** frozen at M7 (definition), `later` (`E_n` for finite `n ≥ 3`).

### D-SP-07 · General E1 enrichment (later)
**Decision.** An E1-monoidal Segal category is a Segal presheaf on Δ (unlabelled, one
object) valued in Segal categories; `Mat(V)` for such `V` has cells as maps out of
unbiased tensors; Gepner–Haugseng's comparison is the acceptance test.
**Status.** later (M7).

### D-SP-08 · The named mountain, comparisons, model structures
**Decision.** Model structures are theorems, never definitions.
The **named mountain** is `HasColimits Kan` (and limits): an interface one-liner whose
proof is the Segal-category analogue of HTT 4.2.4.1 — homotopy colimits of Kan
complexes (Bousfield–Kan / Hirschhorn) are colimits in the Segal category `Kan` in the
sense of → D-UP-04, established through the identification of derived mapping spaces.
The Segal-native route is Simpson's *Homotopy Theory of Higher Categories* (limits and
colimits in `nCAT` with discrete object sets). Everything downstream depends on it:
cocompleteness of `PSh(C)`, coends, composites of profunctors (→ D-FT-02), Kan
extensions along Yoneda, the Kleisli VDC∞s and composition products of → D-SP-09. It is scheduled by name in → 08.
Other milestones, in the order they unblock things: Kan–Quillen (from the inventory if
present); Reedy/Bergner for Segal categories (needed for AT-KR-11 and rectification);
Segal categories ≃ complete Segal spaces (Bergner) as AT-SP-5; complete Segal spaces ≃
quasi-categories (Joyal–Tierney) and Cisinski's `S` — optional, opens Kerodon/HTT as a
source; dendroidal Segal spaces ≃ Lurie's ∞-operads (Heuts–Hinich–Moerdijk) — optional;
style B ≃ style A for VDC∞ (AT-RT-9) — optional.
**Status.** frozen list; the mountain and the first two are M6, the rest `later`.

## Acceptance tests (summary)

- AT-SP-1 `U` is a Kan complex.
- AT-SP-2 `Kan` is an ∞-category in the library's sense; classical homotopy category; rectified by the strict simplicial category.
- AT-SP-3 Monads in `Mat(Kan)` at `A` are Segal categories with object set `A`.
- AT-SP-4 `Span(S)` is a VDC∞, fibrant when `S` is.
- AT-SP-5 `Mod(Mat Kan) ≃ Mod(Span Kan)`.
- AT-SP-6 Discrete ∞-operads are coloured operads.
- AT-SP-7 Planar ∞-operads as monads in a multimatrix VDC∞.
- AT-SP-8 Rectification: strict simplicial categories present all Segal categories.
- AT-SP-9 `Mod(H-Kl(T_Σ, Mat Set))` is the classical equipment of coloured symmetric operads.
- AT-SP-10 Monads in `H-Kl(T_Σ, Mat Kan)` present Lurie's ∞-operads (Haugseng; nerve theorem at ∞).
- AT-SP-11 Contractible monads in the `T_ℕ`/`T_𝔹`/`T_Σ` Kleisli VDC∞s are `E_1`/`E_2`/`E_∞`.
- AT-SP-13 `H-Kl(T, X)` is a VDC∞ and `Mod(H-Kl(T, X))` is an equipment (Cruttwell–Shulman at ∞).
- AT-SP-12 `HasColimits Kan` (the mountain).

## Open questions

- OQ-SP-1 Universe size bookkeeping: `Mat(Kan.{v})` has values built from
  `U.{v} : sSet.{v+1}` and labels in an independent `Type u` (→ D-RT-12); confirm the
  universe pattern and that nothing forces a third universe.
- OQ-SP-2 Whether to prove AT-SP-1 via Cisinski, Sattler, or minimal fibrations.
- OQ-SP-3 Whether `Kan` and `Mat(Kan)` are made fibrant by replacement or by
  construction from the universe (left fibrations over `Δ[n] × Δ[m]`). Kernel choice;
  invisible past the seal; the by-construction route avoids proving that the
  replacement preserves the elementary values up to equivalence, the by-replacement
  route reuses AT-KR-11.

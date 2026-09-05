# 02 · Root (stage 1)

The root is the single definition everything else instantiates, together with the
constructions that must be made before the seal because they need the kernel: maps,
equivalences, fibrant replacement, derived mapping spaces, walking structures and
`Mod`, `Mat(Set)`, `Category`, the discrete embedding, and the interface itself.

Throughout, `X : Type u` is a label set and `Θ := Θ^aug_{fc,X}` (→ D-KR-06, D-KR-07).
Elementary shapes: `pt(x)`, `v(x,y)`, `h(x,y)`, `c_n(x₀…x_n; y₀,y₁)`, `c_n^∅(x₀…x_n; y)`.

## The definition

### D-RT-01 · Virtual double ∞-category
**Decision.** A VDC∞ with label set `X` is a presheaf `P : Θᵒᵖ → sSet` such that
1. **(Kan)** every `P(θ)` is a Kan complex;
2. **(boundary fibrancy)** for every elementary cell shape `c` (with or without output),
   the restriction map `P(c) → lim_{∂c} P` to the product of the values on its boundary
   edges is a Kan fibration;
3. **(Segal)** for every non-elementary `θ`, the map `P(θ) → lim_{Sc(θ)} P` to the
   strict limit over the Segal core (→ D-KR-04) is a homotopy equivalence;
4. **(unit)** every `P(pt x)` is contractible.
The strict limit in (3) is a homotopy limit because of (2) and because all gluing over
object positions is along discrete sets (labels).
**Rationale.** Conditions (1)–(4) are properties, stated with the kernel's vocabulary
only (→ D-KR-10). Objects are a set, so no completeness condition. Cells are E1.
Augmented cells are in the shape category, so augmentation is not an extra axiom.
**Rejected.** Requiring Reedy fibrancy in the definition. Strict examples (strict
simplicial categories, `Mat(Kan)`, any algebraic model) are never Reedy fibrant: the
matching map at a composite shape is the graph of composition, which is not a fibration.
Fibrancy is a class with a replacement theorem (→ D-RT-07). Stating (3) with homotopy
limits via path spaces instead of (2): equivalent, uglier; (2) holds in every example we
intend and for all discrete presheaves.
**Acceptance.** AT-RT-1 (discrete case, → D-RT-11); AT-RT-2 (`Mat(Set)` is a VDC∞);
AT-RT-3 (nerves of set-level VDCs satisfy (1)–(4)); AT-RT-8 (`Mat(Kan)`, at M6).
**Status.** frozen at M3.

### D-RT-02 · Non-definition: what a VDC∞ is not
A VDC∞ is not Reedy fibrant, not a fibration over `N(Δᵒᵖ)`, not a double ∞-category
(no horizontal composites), not symmetric. Each of those is either a class inside the
definition (fibrant), a comparison target (style A, → AT-RT-9 at M6+), or a derived
structure when extra properties hold (composites, → D-FT-02).

### D-RT-03 · Maps and the 1-category `VDC∞`
**Decision.** A map `P → Q` of VDC∞s with label sets `X, Y` is a function `f : X → Y`
together with a map of presheaves `P → f^* Q` over `Θ_{fc,X}`, where `f^* Q` is
restriction along `Θ_{fc,X} → Θ_{fc,Y}`. Composition is evident. `VDC∞.{u,v}` is a
1-category (a Grothendieck construction over `Type u`). The ∞-category of VDC∞s is not
defined at this stage.
**Rationale.** Strict maps are the right maps for the homotopy theory once the target
is fibrant (→ D-RT-08); before that they are the only maps we can write.
**Status.** frozen at M3.

### D-RT-04 · Vertical and horizontal parts
**Decision.** `Vert P` is the Segal category with object set `X` obtained by restricting
`P` to the vertical-path shapes (the copy of `Δ_X` inside `Θ`); it is an ∞-category in
the sense of → D-SP-04 and is the "underlying ∞-category of objects and functors". For
`x, y : X`, `Hor P (x,y)` is the space `P(h(x,y))` of horizontal morphisms, and unary
cells with identity vertical boundary give the Segal category `Hor P` fibred over `X × X`.
**Status.** frozen at M3.

### D-RT-05 · The homotopy VDC `hP`
**Decision.** `hP` is the set-level augmented VDC with the same objects, vertical
morphisms `π₀ P(v(x,y))`, horizontal morphisms `π₀ P(h(x,y))`, and cells the
path components of the fibres of the boundary maps of (2) over chosen representatives
(well defined up to canonical bijection since those maps are Kan fibrations).
Composition is induced from the Segal maps of (3).
**Rationale.** `hP` is where Riehl–Verity-style arguments live (→ D-FT-04); it is also
the vocabulary in which DK-equivalence is stated.
**Acceptance.** AT-RT-4: `hP` is an augmented VDC; for discrete `P`, `hP ≅ P`.
**Status.** frozen at M3.

### D-RT-06 · DK-equivalence
**Decision.** A map `(f, φ) : P → Q` is a DK-equivalence when
1. it is essentially surjective on objects: every `y : Y` is vertically equivalent in `hQ`
   to some `f x` (vertical equivalence = isomorphism in the vertical category of `hQ`);
2. it is fully faithful on vertical morphisms: `P(v(x,x')) → Q(v(fx,fx'))` is a homotopy equivalence;
3. it is essentially surjective on horizontal morphisms: every `N : fx ⇸ fx'` is
   isomorphic in `Hor Q` (via an invertible unary cell) to `φ(M)` for some `M`;
4. it is fully faithful on horizontal morphisms and cells: `P(h) → Q(h)` and every
   `P(c) → Q(c)` are homotopy equivalences over the boundary (equivalences on fibres of the maps of (2)).
**Rationale.** This is the Segal-category transcription of "equivalence of ∞-categories
over `Δᵒᵖ` fibrewise" in style A. It is combinatorial: homotopy equivalences of Kan
complexes and isomorphisms in a 1-category.
**Acceptance.** AT-RT-5: DK-equivalences satisfy 2-out-of-3 and are closed under
composition; for discrete `P, Q` they are the equivalences of augmented VDCs;
**(verify at M6+)** agreement with style-A equivalences under the comparison of AT-RT-9.
**Status.** frozen at M3 (the clause list is provisional until AT-RT-5 is proved).

### D-RT-07 · Fibrant objects and replacement
**Decision.** `P` is *fibrant* when it is Reedy fibrant for the elegant Reedy structure
on `Θ` (→ D-KR-05). Theorem (from → D-KR-11): every VDC∞ admits a fibrant replacement
`P → RP`, a DK-equivalence that is the identity on labels. A fibrant replacement is a
witness (→ D-CH-02): theorems never depend on which one.
Fibrancy is an *exported property*: standard objects (`Mat Set`, later `Mat Kan`,
`Mod` of fibrant objects, slices, functor objects) are exported together with proofs
that they are fibrant, so that `R` is invoked in `Theory/` only for user-built objects.
Whether a standard object is fibrant by construction or by replacement in the kernel is
invisible past the seal (→ D-CH-13, OQ-SP-3).
**Status.** frozen at M3.

### D-RT-08 · Derived mapping spaces
**Decision.** For VDC∞s `Q, P` with a fixed map on labels, `Map(Q, P)` is the
simplicial mapping space of strict maps `Q → RP` over that label map. It is a Kan
complex (every `Q` is cofibrant by elegance, `RP` is fibrant), and independent of the
choice of `RP` up to homotopy equivalence.
**Rationale.** Strict maps into a fibrant object model homotopy-coherent maps; this is
the whole reason to have fibrant replacement.
**Acceptance.** AT-RT-6: independence of `R`; for discrete `Q, P`, `π₀ Map(Q,P)` is the
set of maps.
**Status.** frozen at M3.

## Constructions

### D-RT-09 · Walking structures and `Mod`
**Decision.** Set-level (kernel) augmented VDCs embed as discrete VDC∞s (→ D-RT-11),
and in particular the *walking* structures do: the walking monad `Mnd` (one object, one
horizontal endomorphism, nullary unit cell, binary multiplication cell, laws), the walking
monad morphism, the walking bimodule, the walking bimodule cell of each arity, and in
general the walking θ-diagram `W_θ` of monads, monad morphisms, bimodules and cells for
each shape `θ` of `Θ_fc` (labelled by the monads at its object positions).
- A **monad** in `P` at `x` is a point of `Map(N Mnd, P)` over `x`.
- `Mod(P)` is the presheaf `θ ↦ Map(N W_θ, P)` on `Θ_{fc, Monads(P)}`, where
  `Monads(P)` is the set of monads of `P`.
**Theorem targets.** `Mod(P)` is a VDC∞ (AT-RT-7); `Mod` preserves augmented virtual
equipments (AT-FT-3, the ∞-analogue of Cruttwell–Shulman).
**Rationale.** The virtual setting means `Mod(P)` needs no coends: bimodules and their
cells are maps out of labelled shapes. Composites of bimodules, when they exist, are a
theorem, not structure.
**Rejected.** Defining monads/bimodules by explicit coherence data. That is what
`Map(N W, RP)` packages, and packaging it by hand is exactly the coherence bookkeeping
the design exists to avoid.
**Status.** frozen at M3.

### D-RT-10 · `Mat(Set)` and `Category`
**Decision.** `Mat(Set.{v})` is the discrete VDC∞ with label set `Type v`, vertical
morphisms functions, horizontal morphisms `A ⇸ B` families `A → B → Type v`, `n`-ary
cells `(M₁,…,M_n) ⇒ N` over `(f,g)` families of functions
`M₁(a₀,a₁) → ⋯ → M_n(a_{n−1},a_n) → N(f a₀, g a_n)`, nullary-target cells
`(M₁,…,M_n) ⇒ ∅` over `(f,g)` families of functions into `f a₀ = g a_n`
**(verify: this is Koudenburg's augmentation of `Mat`; the identity matrix is a unit and
nullary-target cells are cells into it)**.
`Category A := Monad (Mat Set) A` for `A : Type v`. Unwinding: `Hom : A → A → Type v`,
`n`-ary composites `Hom(a₀,a₁) → ⋯ → Hom(a_{n−1},a_n) → Hom(a₀,a_n)` for all `n ≥ 0`,
compatible under all maps of `Δ` — the unbiased families definition, associativity
being functoriality (→ D-CH-03).
`Cat := Mod(Mat Set)`: functors are vertical morphisms, profunctors horizontal
morphisms, natural transformations vertical 2-cells, cells of profunctors the cells.
**Rationale.** Families rather than spans: composability by typing. `Mat` rather than
`Span` at the discrete level because `Span(Set)` needs pullbacks and yields the
component-wise presentation (→ D-SP-05 for where spans return).
**Acceptance.** AT-RT-2; AT-RT-10: `Category A` is equivalent (as a type, over `A`) to
the classical `{Hom, id, comp, laws}` structure and to Segal presheaves on `Δ_A`
(→ AT-KR-9); AT-RT-11: the vertical 2-category of `Cat` is the classical one.
**Status.** frozen at M3.

### D-RT-11 · Discrete embedding and the self-hosting theorem
**Decision.** A set-level augmented VDC `V` (kernel) has a nerve `N V : Θᵒᵖ → Set ⊂ sSet`
(→ AT-KR-8); `N V` is a discrete VDC∞ (AT-RT-3). Conversely a VDC∞ whose values are
discrete is `N` of its `hP`. **Self-hosting theorem (AT-RT-1):** this is an equivalence
between the kernel's category of augmented VDCs and the full subcategory of discrete
VDC∞s, under which `Category A` (D-RT-10) corresponds to Mathlib's `Category A` up to
the evident equivalence. After the seal, "set-level VDC" *means* "discrete VDC∞", and
the kernel's definition is invisible.
**Rationale.** This is the theorem that licenses hiding the kernel: everything the
kernel knew about set-level structures is recoverable from the root.
**Status.** frozen at M3.

### D-RT-12 · Universe policy
**Decision.** Full polymorphism, with the label universe and the value universe
independent everywhere. `VDC∞.{u,v}` has labels in `Type u` and values in `sSet.{v}`;
`Θ_{fc,X}` for `X : Type u` lives in `Type u`. `Mat(Set.{v})` is polymorphic in its
label universe: `Mat.{u,v}(Set.{v}) : VDC∞.{u,v}` has labels the sets `A : Type u` (any
`u`) and horizontal morphisms `A → B → Type v`. Hence `Category.{u,v} A` for `A : Type u`
with homs in `Type v` — exactly Mathlib's split, which is forced: `Set`, `Kan`, and `Cat`
have large object sets and small homs and must be objects of `Mat(Kan.{v})`. Rules: no
`max` in structure fields where a single universe suffices; `ULift`-transport lemmas are
part of the interface; Yoneda-size questions in the formal theory are handled by
augmentation (→ D-FT-01), which addresses the presheaf object not existing at the same
size and nothing else.
**Rationale.** The earlier draft offered a single universe and claimed augmentation
would absorb size; it does not absorb "large objects, small homs," which is the common case.
**Rejected.** A Grothendieck-universe parameter `U` in the root. Reconsider at M6 if
`Kan` and `U` (→ D-SP-01) make it attractive.
**Status.** frozen (rules provisional).

## The seal

### D-RT-13 · Interface and mechanism
**Decision.** `Interface/` exports, and `Theory/` may use, exactly:
- **Shapes, transparently**: the objects and morphisms of Δ, Δ₊, Ω_p, Ω, Θ^aug_fc, Θ_n,
  Δ×Δ, □, `Tw(θ)` are exported as *transparent* inductive types with `DecidableEq` and
  computable composition (→ D-TL-10): rows of block sizes for `Θ^aug_fc`, monotone `Fin`
  maps for Δ, nested lists for Ω_p and Θ_n, and so on. What is sealed is their
  `Category` structure in the sense of D-RT-10 (with generating morphisms, inert/active
  factorization, degrees, Segal cores, labelled variants as API) and the bridge lemma
  identifying the transparent hom-types with the sealed ones. This is the one deliberate
  exposure of computation past the seal: a pasting proof is a tree-map equality decided
  on finite data (→ D-TL-09), not a fact about how a categorical notion unfolds, so
  D-CH-01 is not violated; the linter's `decide` ban (→ D-TL-06) exempts these types.
- **Spaces**: `Space` (Kan complexes), maps, homotopy, homotopy equivalence, `π₀`,
  contractibility, fibrations and fibre products, mapping spaces — sealed.
- **Root**: `VDC∞`, maps, `Vert`, `Hor`, `hP`, DK-equivalence, fibrant, fibrant
  replacement (existence), `Map`.
- **Constructions**: `N` (discrete embedding), walking structures, `Monad`, `Bimodule`,
  `Mod`, `Mat Set`, `Category`, `Cat`, the self-hosting theorem.
- **Closure and rectification** (→ D-CH-13), as theorems: `Mat Set` is fibrant (trivially);
  `Mod` preserves fibrancy; slices, functor objects (mapping Segal categories), and
  fibre products along fibrations preserve fibrancy; exponentials of fibrant objects by
  cofibrant ones are fibrant; the pushout-product and Reedy lemmas needed to prove such
  statements in `Theory/`; DK-invariance of `Mod`, `Vert`, `Hor`, `hP`; rectification:
  for a strict (Segal, not necessarily fibrant) `P`, strict maps `N W → P` composed with
  `P → RP` hit every component of `Map(N W, P)` (Dwyer–Kan/Bergner rigidification in
  the case `P = Mat Kan`, → D-SP-04). Later interface versions add the same package for
  `Mat Kan`, `Span`, and limits.
- **Nothing else.** No `SSet`, no `SimplexCategory`, no Mathlib `Functor`.

Extension policy, two tiers:
- **Constants** (new sealed data or new shapes) are frozen-tier: a superseding decision.
- **Lemmas** statable in interface vocabulary and provable in `Root/` are
  provisional-tier: an agent may add them by PR without a decision, subject to the
  statement-hygiene check (3). This is expected to be the dominant kind of change after
  M3, and making it cheap is what keeps the seal from making the human the bottleneck.

Mechanism:
1. Data whose definitional equations are never needed in `Theory/` are `opaque`
   constants with their kernel implementation as the inhabitation witness.
2. Data whose equations *are* needed as API are `@[irreducible]` definitions with
   equation lemmas `foo_def` that are `private` to `Root/`; the exported API consists of
   theorems proved in `Root/` using those lemmas.
3. Every exported theorem is stated purely in interface vocabulary. A CI grep enforces
   that `Interface/` mentions no kernel or Mathlib category-theory names in statements.
4. The **swap test** (→ D-TL-06): a second `Interface-Stub/` in which every constant is a
   bodiless `axiom` with the same statement; `Theory/` must build against it.
5. A build variant that uses the stub instead of the kernel for speed; the kernel build is
   the consistency witness and runs nightly.
**Rationale.** `opaque` is the hard seal; `@[irreducible]` + private equations is the
soft seal that still allows API lemmas to be proved once; the swap test is the proof that
no leak exists, and it is what "axiom wlog" (→ D-CH-12) means operationally.
**Status.** frozen; the interface *list* is frozen at M3 ("Interface v1") and extended
only by superseding decisions.

### D-RT-15 · `Vert₂`, unit factorization, and 2-categorical pasting (M3)
**Decision.** For a VDC∞ `P` with units (every `Mod(P)` has them), `Vert₂(P)` is the
(∞,2)-categorical structure with objects, vertical morphisms, and 2-cells the nullary
cells `() ⇒ U_b` over `(f, g)`; horizontal composition of 2-cells goes through the
opcartesian unit cell (a nullary cell with a gap at `b` factors uniquely through it).
The 2-categorical pasting theorem for `Vert₂(P)` is a corollary of the nerve theorem
(AT-KR-8) plus unit factorization; mates and whiskering are instances. This is built at
M3 for `Cat = Mod(Mat Set)` rather than waiting for the formal theory at M5.
**Rationale.** Natural transformations exist at M3 as cells, but pasting them needs the
unit's universal property; without `Vert₂` at M3, `Cat` is usable only as a 1-category.
**Acceptance.** AT-RT-12: `Vert₂(Cat)` is the classical 2-category of categories,
functors, and natural transformations, and its pasting theorem is Power's.
**Status.** frozen at M3.

### D-RT-14 · Generated thin API for `Category`
**Decision.** From the monad structure, a metaprogram generates for `Category A`:
`Hom`, `id`, `comp` (binary, as an `abbrev` of the 2-ary composite), `compN` (unbiased),
the `simp` set (`compN` flattening, unit laws, functoriality), `ext`-style lemmas, and the
corresponding API for `Functor`, `Profunctor`, `NatTrans` from `Mod`. The human notation
layer (`⟶`, `≫`, `⥤`, `⇸`) is generated separately (→ D-TL-02).
**Rationale.** Every basic fact about categories arrives through three layers of
instance; the thin API is what makes that invisible, and generating it is what keeps it
in sync with the root.
**Status.** frozen at M3 (contents provisional).

## Acceptance tests (summary)

- AT-RT-1 Self-hosting theorem.
- AT-RT-2 `Mat(Set)` is a VDC∞.
- AT-RT-3 Nerves of set-level augmented VDCs are VDC∞s.
- AT-RT-4 `hP` is an augmented VDC; discrete case.
- AT-RT-5 DK-equivalences: 2-out-of-3, composition, discrete case.
- AT-RT-6 `Map` independent of the replacement; discrete case.
- AT-RT-7 `Mod(P)` is a VDC∞.
- AT-RT-8 `Mat(Kan)` is a VDC∞ (M6).
- AT-RT-9 Comparison with style A (M6+, optional).
- AT-RT-10 `Category A` ≃ classical structure ≃ Segal presheaves on `Δ_A`.
- AT-RT-11 Vertical 2-category of `Cat` is the classical one.
- AT-RT-12 `Vert₂(Cat)` with its pasting theorem is the classical 2-category.

## Open questions

- OQ-RT-1 Is boundary fibrancy (2) the right fibrancy to bake in, or should (2) be
  dropped and (3) stated with path-space homotopy limits? Default: keep (2).
- OQ-RT-2 Should `Monads(P)` (the label set of `Mod(P)`) be the set of *points* of
  `Map(N Mnd, RP)` (depends on `R`) or the set of strict maps `N Mnd → P` (may be too
  small for non-fibrant `P`)? Default: points of `Map(N Mnd, RP)` for a chosen `R`, with
  the theorem that different choices give DK-equivalent `Mod(P)`.
- OQ-RT-3 Exact augmentation structure on `Mat(Set)` (D-RT-10, verify).

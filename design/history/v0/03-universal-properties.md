# 03 · Universal properties (stage 2, M4)

Everything here is stated for a Segal category `C` with object set `X` — i.e. a monad
in `Mat(Kan)` once that exists (→ D-SP-04), and before that for `Vert P` of any VDC∞ and
for discrete `C : Category A`. Only interface vocabulary is used: mapping spaces,
homotopy equivalence, contractibility, derived maps, joins.

## The root notion

### D-UP-01 · Terminal objects
**Decision.** `IsTerminal t : Prop := ∀ x, Contractible (C(x, t))`, with the
theorem, proved immediately after, that this is equivalent to the *global* form: for
every Segal category `K`, restriction `Map(K ⋆ Δ[0], C)_{t} → Map(K, C)` (cones with
vertex `t`) is a trivial fibration. The global form is the one used downstream: it is
what makes lifts along a diagram of problems coherent, and `Classical.choose` is applied
to a *section* of it, never to the fibres one at a time (→ D-UP-06). The equivalence
of the two forms uses boundary fibrancy (→ D-RT-01 (2)): a Kan fibration with
contractible fibres over every vertex is a trivial fibration.
`Terminal C := { t // IsTerminal t }`. Theorem: the full sub-Segal-category of `C` on
terminal objects is a contractible ∞-groupoid (any two terminal objects are connected
by a contractible space of equivalences). Initial objects are dual (→ D-UP-05).
**Rationale.** This is the one universal property. It is a proposition, it survives every
level (1-categories: singleton hom-sets; ∞: contractible mapping spaces), and it needs no
data beyond the mapping spaces. The trivial-fibration form is the same statement with
the coherence of lifts built in.
**Acceptance.** AT-UP-1: for discrete `C`, `IsTerminal` is the classical definition and
the uniqueness theorem is unique-up-to-unique-iso.
**Status.** frozen.

### D-UP-02 · Diagrams
**Decision.** For a category `J` (discrete, i.e. `J : Category`) and a Segal category
`C`, a `J`-diagram in `C` is a point of `Map(N J, C)` (→ D-RT-08 applied to the Segal
categories `N J` and `C` viewed inside `Mat(Kan)`; before M6, inside `Vert` of the
ambient VDC∞). Diagrams of shape a Segal category `K` are points of `Map(K, C)`.
**Status.** frozen.

### D-UP-03 · Joins and slices
**Decision.** For a diagram `F : N J → C`, the slice `C_{/F}` is the Segal category with
object set `{(x, cone) | cone : N([0] ⋆ J) → C restricting to F}` and value at
`([n]; x₀…x_n)` the fibre over `F` of the restriction map
`Map(N([n] ⋆ J), C) → Map(N J, C)` with the given labels — a Kan complex, since the
restriction is a Kan fibration (inclusion of a sub-presheaf into a cofibrant object,
fibrant target). Joins come from the kernel through the interface (→ D-KR-08).
`F ↓ y` and comma constructions are the same recipe with `[n] ⋆ J` replaced by the
appropriate join/comma shape.
**Rationale.** Lurie's definition of slices transposed to Segal categories; it uses
only joins, derived mapping spaces and fibres along fibrations.
**Acceptance.** AT-UP-2: for discrete `C` and `J`, `C_{/F}` is the classical slice/cone
category; AT-UP-3: `C_{/F}` is a Segal category (Segal condition holds).
**Status.** frozen (the exact join used for commas is provisional).

### D-UP-04 · Limits, and everything else, as terminal objects
**Decision.**
- `Limit F := Terminal (C_{/F})`; `HasLimit F : Prop := Nonempty (Limit F)`.
- `Product (x_i)_{i ∈ I}` for a set `I` is `Limit` of the discrete diagram; there is no
  binary-product API at this layer (binary is an `abbrev` in the human layer, → D-TL-02).
- `Representation P := Terminal (El P)` for a presheaf `P` (a profunctor `C ⇸ 1`; the
  profunctor form is → D-FT-03).
- `RightAdjointAt F y := Terminal (F ↓ y)`; an adjunction is a family of these together
  with the induced functor, and in the formal theory it is `companion ≃ conjoint` (→ D-FT-03).
- Right Kan extension along `i : J → J'` of `F : N J → C` at `j'`: `Limit` of the
  restriction of `F` to the slice `(j' ↓ i)`; pointwise by definition; existence
  propositions as `Nonempty`.
**Rationale.** One universal property, many witness categories. Uniqueness, transport and
the contractibility of witnesses are inherited from D-UP-01 in every case.
**Acceptance.** AT-UP-4: each specializes to the classical notion for discrete `C`.
**Status.** frozen.

### D-UP-05 · Duality
**Decision.** Within Segal categories (this document), colimits, initial objects, left
Kan extensions, left adjoints are obtained by the `to_dual` attribute (→ D-TL-03),
which acts by `op` on shapes and on the ambient Segal category. No dual notion at this
layer is defined by hand. Scope: `to_dual` is total on Segal categories and on the
*horizontal* op of VDC∞s (reversal of inputs); the vertical op is not available for
augmented VDC∞s (nullary-target cells have no nullary-source dual) and transpose is not
available for virtual ones, so in → 04 some dual statements will be proved by hand and
the attribute records that they are duals rather than generating them.
`Cᵒᵖᵒᵖ ≃ C` is an equivalence, never an identity, past the seal; `to_dual`'s
transport lemmas along it are part of the attribute's output.
**Acceptance.** AT-UP-5: `to_dual` of `Limit` is a colimit in the classical sense for discrete `C`.
**Status.** frozen (scope clause provisional).

## Witnesses

### D-UP-06 · Witness discipline
**Decision.** Theorems about universal objects quantify over witnesses: `∀ (L : Limit F), …`.
`Classical.choose` appears only in the bridge lemmas `Nonempty (Limit F) → Limit F`
and in choosing *sections* of the trivial fibrations of D-UP-01 (global lifts,
functorial `cosk_n`, coherent families of limits over a diagram of diagrams); both live
in one file. No `limit F` constant exists. Any construction `Φ` that takes a witness
must come with its functoriality in the witness (a map between the contractible witness
spaces induces a canonical equivalence `Φ L ≃ Φ L'`), and the `witness_transport`
tactic (→ D-TL-04) discharges the routine cases.
**Rationale.** → D-CH-02. The functoriality requirement is the categorical replacement for
definitional uniqueness; choosing sections rather than points is what makes chosen
lifts coherent along diagrams without any coherence bookkeeping.
**Status.** frozen.

### D-UP-07 · Extend along a shape inclusion
**Decision.** The primary *operation* of this layer is Kan extension along inclusions of
shape categories: `sk_n`, `cosk_n`, restriction/extension along `Δ_{≤n} → Δ`,
`Δ₊,≤0 → Δ₊`, `Ω_p → Ω`, and along inert inclusions of sub-shapes. Worked example and
acceptance test: the Čech nerve of `f : x → s` is `cosk₀` in augmented simplicial
objects over `s`; its `n`-th term is a limit over the appropriate shape; it exists when
the relevant limits do; it is unique up to contractible choice; it is functorial in `f`.
This is the "extend to the Amitsur diagram" of → D-CH-03.
**Acceptance.** AT-UP-6 (Čech nerve as above); AT-UP-7: `cosk_n ⊣ sk_n`-style
adjunction statements as terminal-object statements.
**Status.** frozen.

## Specializations

### D-UP-08 · 1-level instances
**Decision.** For discrete `C`, all of the above are proved to coincide with the
classical definitions, as theorems in `Theory/` (not as separate definitions). These
theorems are the acceptance tests AT-UP-1…7.
**Status.** frozen.

### D-UP-09 · 2-level: universal properties in `Cat`
**Decision.** `Vert P` sees vertical morphisms only: `Vert(Cat)` is the 1-category of
categories and functors, and `Vert(Mod(Mat Kan))` has as mapping spaces the
∞-groupoids of functors and natural *equivalences*. Natural transformations are nullary
cells into units and live in the equipment, not in `Vert`. Consequently:
- (∞,1)-universal properties in `Vert(Cat_∞)` are used for products, pullbacks,
  exponentials (functor objects), and cotensors with `[1]`. They suffice for these because
  the core of `Fun(E, −)` for all `E` (including `E × [1]`) detects the full ∞-category
  `Fun(E, −)`; a functor object is "an exponential in `Vert(Cat_∞)`", a localization "a
  functor with the universal property in `Vert(Cat_∞)`", and the concrete `[C, D]`,
  `C[W⁻¹]` are witnesses provided by constructions.
- Anything lax or 2-categorical — comma objects as 2-limits, Kleisli objects, lax
  monoidal structure, mates — is stated in the equipment `Mod(Mat Kan)` using cells (→ 04),
  never in `Vert`.
1-categorical universal properties in a strict `Cat` are never used.
**Rationale.** The earlier draft called `Vert` "2-dimensional"; it is not. The
2-dimensional data is in the cells, and the (∞,1)-part is enough exactly for the
constructions listed.
**Acceptance.** AT-UP-8: for discrete `C, D`, the exponential in `Vert(Cat)` is the
functor category and its universal property is the classical one on cores.
**Status.** frozen.

## Open questions

- OQ-UP-1 Comma shapes: use the simplicial join throughout, or a dedicated comma
  shape in the kernel? Default: join.
- OQ-UP-2 Do we want `HasLimitsOfShape J C` as a Prop-class for instance search, or
  always explicit hypotheses? Default: Prop-classes are allowed (they are propositions),
  never data-classes.

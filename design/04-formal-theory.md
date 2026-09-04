# 04 · Formal category theory (stage 2, M5)

Formal category theory is developed once, for augmented virtual ∞-equipments, using
only the VDC∞ interface. Instances: `Cat = Mod(Mat Set)` (discrete), `Mod(Mat Kan)`
(∞-categories and profunctors, M6), `Mod(Span S)` (internal, M5/M6), and `Mod(P)` for
any equipment `P` (→ AT-FT-3). This is the layer where "not written down" is the point
(→ D-CH-06): definitions follow Koudenburg's augmented framework and Cruttwell–Shulman,
transported to VDC∞s; the acceptance tests are the discrete and non-virtual comparisons.

## Definitions

### D-FT-01 · Augmented virtual ∞-equipment
**Decision.** A VDC∞ `P` is an augmented virtual ∞-equipment when:
1. **Restrictions.** For vertical `f : a → c`, `g : b → d` and horizontal `M : c ⇸ d`,
   there is a horizontal `M(f,g) : a ⇸ b` with a unary *cartesian* cell
   `M(f,g) ⇒ M` over `(f,g)`: cartesian means that for every path `(M₁,…,M_n)` and
   vertical `(h,k)` factoring through `(f,g)`, precomposition with the cartesian cell is a
   homotopy equivalence between the space of cells `(M₁,…,M_n) ⇒ M(f,g)` over `(h,k)`
   and the space of cells `(M₁,…,M_n) ⇒ M` over `(f h, g k)`. Universality is a
   proposition; `M(f,g)` is a witness.
2. **Units.** For every object `a`, a horizontal `U_a : a ⇸ a` with a nullary *opcartesian*
   cell `() ⇒ U_a` (postcomposition with it is a homotopy equivalence on cell spaces with a
   gap at `a`). In the augmented setting units are not required to exist; where they do
   not, the nullary-target cells carry the universal properties Koudenburg assigns to
   them. **(verify: transcribe Koudenburg's axioms for AVDCs exactly; this is a task, not
   a fact.)**
Companions `f_* := U_b(f, 1)` and conjoints `f^* := U_b(1, f)` when units exist;
otherwise as Koudenburg defines them through nullary-target cells.
**Rationale.** Cartesian/opcartesian universality is "terminal in a witness Segal
category" (→ D-UP-01) applied to cells; so the whole formal theory rests on the same
root as → 03.
**Acceptance.** AT-FT-1 (discrete case is Koudenburg's/Cruttwell–Shulman's definition);
AT-FT-2 (`Mat(Set)` and `Cat` are augmented virtual equipments).
**Status.** frozen at M5 (axiom transcription provisional).

### D-FT-02 · When composites exist
**Decision.** `P` *has composites* when for every path `(M₁,…,M_n)` there is a horizontal
`M₁ ⊙ ⋯ ⊙ M_n` with an opcartesian `n`-ary cell. Then `P` restricted to the `Δ×Δ`-shapes
(→ D-KR-08) is a double ∞-category, and if `P` is an equipment it is an ∞-equipment in
Ruit's sense **(verify: this is the statement of AT-FT-4; the precise notion of "Ruit's
sense" transported to Segal-style double ∞-categories is part of the task)**.
Composites are a property with witnesses, never structure (→ D-CH-02).
**Acceptance.** AT-FT-4 as above; AT-FT-5: `Cat` has composites (coends of profunctors)
and the induced double category is the classical one.
**Status.** frozen at M5.

## The formal theory (targets)

### D-FT-03 · Theorem list, stated once
Each item is stated for an augmented virtual ∞-equipment `P` and proved with the VDC∞
API only. Discrete specializations are acceptance tests (AT-FT-1 covers all of them).
1. **Representable horizontals** and the characterization of companions and conjoints
   by their unit/counit cells; `f_* ≃ g_*` implies `f ≃ g` vertically.
2. **Yoneda.** Koudenburg's Yoneda embeddings in augmented VDCs: a vertical `y : a → â`
   with the universal nullary/unary cell structure such that restriction along `y`
   induces equivalences of the relevant cell spaces **(verify exact form)**. Existence of
   Yoneda embeddings is a *property* of `P` ("has Yoneda embeddings"), holding in `Cat`
   with `â` the presheaf category of the next universe (→ D-RT-12).
3. **Right and left extensions and liftings** of horizontals along horizontals (Kan
   extensions inside the equipment), with the pointwise/absolute distinction stated
   through restriction.
4. **Weighted limits and colimits** of a diagram `d : j → a` weighted by `W : j ⇸ k`
   (resp. `k ⇸ j`), as representability of the appropriate restriction; conical limits
   as the unit-weighted case; comparison with → D-UP-04 (AT-FT-6).
5. **Adjunctions.** `f ⊣ g` iff `f_* ≃ g^*`; the space of adjunction data over a given
   `f` is contractible or empty; mates.
6. **Monads** in `P` as in → D-RT-09; Kleisli and Eilenberg–Moore objects by universal
   property; monadicity in the formal sense (Street) where composites exist.
7. **Fully faithful / essentially surjective** vertical morphisms via companions;
   equivalences as vertical morphisms with a companion that is also a conjoint of an inverse.
8. **Absolute liftings** and the formal definition of limits in the vertical
   ∞-category through them (the Riehl–Verity form), compared with 4 (AT-FT-7).
**Status.** frozen list; each item provisional until stated in Lean.

## Tracks and comparisons

### D-FT-04 · The set-level track in `hP`
**Decision.** `hP` (→ D-RT-05) is an augmented virtual equipment when `P` is
(AT-FT-8). Riehl–Verity-style arguments — proofs in the homotopy 2-category and in the
set-level equipment of modules — are carried out in `hP` and lifted to `P` by truncation
lemmas where the ∞-statement is a `π₀`-statement. This is the cheap track: many
(∞,1)-theorems (adjunctions, absolute liftings, limits as absolute liftings) are
set-level statements about `hP`.
**Rationale.** Coherence lives in `P`; the formal layer is set-level. Banking these
results early is low-risk and validates D-FT-03 before the coherent versions are built.
**Status.** frozen at M5.

### D-FT-05 · Cosmoi (later)
**Decision.** An ∞-cosmos is defined as a category enriched in Segal categories (through
the strict simplicial-category model, → D-SP-02) with the Riehl–Verity limits and
isofibrations, adapted to the Segal-category model; its homotopy 2-category and its
virtual equipment of modules are compared with `hP` for `P = Mod(Mat Kan)` (AT-FT-9).
**Status.** later (M7).

## Acceptance tests (summary)

- AT-FT-1 Discrete case of D-FT-01 and D-FT-03 is Koudenburg / Cruttwell–Shulman.
- AT-FT-2 `Mat(Set)` and `Cat` are augmented virtual equipments.
- AT-FT-3 `Mod` preserves augmented virtual (∞-)equipments.
- AT-FT-4 With composites, an equipment is a Ruit ∞-equipment.
- AT-FT-5 `Cat` has composites; classical double category of profunctors.
- AT-FT-6 Weighted limits with unit weight are the limits of → D-UP-04.
- AT-FT-7 Absolute-lifting limits agree with slice-terminal limits.
- AT-FT-8 `hP` is an augmented virtual equipment.
- AT-FT-9 Cosmos comparison (M7).

## Open questions

- OQ-FT-1 Do we transcribe Koudenburg's *augmented* axioms literally, or the
  Cruttwell–Shulman axioms plus his augmentation as a separate structure? Default:
  literal transcription, then a theorem that it restricts to Cruttwell–Shulman on the
  unaugmented part.
- OQ-FT-2 How much of D-FT-03 should be attempted in `hP` first (D-FT-04) versus
  directly in `P`? Default: every item first in `hP`, then coherently.

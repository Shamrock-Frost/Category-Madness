import Kernel.Augmented.NerveMonadMap

/-! Recognition of lifted algebras under an invertible monad comparison.
Berger–Melliès–Weber, arXiv:1101.3064, Proposition 1.3(c).
The augmented arity application must still supply the comparison and monadicity.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category
namespace Kernel.Augmented.Nerve.MonadMap
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : CategoryTheory.Monad C} {S : CategoryTheory.Monad D} {F : C ⥤ D}
  (M : MonadMap T S F) [F.Faithful]

/-- The faithful base functor reflects the unit law of a lifted operation. -/
theorem reflects_unit (X : C) (a : T.obj X ⟶ X)
    (h : S.η.app (F.obj X) ≫ (M.comparison.app X ≫ F.map a) = 𝟙 (F.obj X)) :
    T.η.app X ≫ a = 𝟙 X := by
  apply F.map_injective
  rw [F.map_comp]
  erw [F.map_id]
  rw [← M.unit, assoc]
  exact h

/-- Epimorphic comparison maps reflect associativity; invertibility suffices. -/
theorem reflects_assoc [∀ X, IsIso (M.comparison.app X)] (X : C) (a : T.obj X ⟶ X)
    (h : S.μ.app (F.obj X) ≫ (M.comparison.app X ≫ F.map a) =
      S.map (M.comparison.app X ≫ F.map a) ≫ (M.comparison.app X ≫ F.map a)) :
    T.μ.app X ≫ a = T.map a ≫ a := by
  apply F.map_injective
  simp only [F.map_comp]
  apply (cancel_epi (M.comparison.app (T.obj X))).mp
  apply (cancel_epi (S.map (M.comparison.app X))).mp
  calc
    _ = S.μ.app (F.obj X) ≫ (M.comparison.app X ≫ F.map a) := by
      simpa only [assoc] using congrArg (fun k => k ≫ F.map a) (M.mul X).symm
    _ = S.map (M.comparison.app X ≫ F.map a) ≫ (M.comparison.app X ≫ F.map a) := h
    _ = _ := by
      rw [S.map_comp]
      simpa only [assoc] using congrArg (fun k => S.map (M.comparison.app X) ≫ k ≫ F.map a) (M.naturality a)

variable [F.Full] [∀ X, IsIso (M.comparison.app X)]

/-- Descend an algebra operation whose underlying object is in the strict image of the base. -/
noncomputable def descend (X : C) (a : S.obj (F.obj X) ⟶ F.obj X)
    (unit : S.η.app (F.obj X) ≫ a = 𝟙 (F.obj X))
    (mul : S.μ.app (F.obj X) ≫ a = S.map a ≫ a) : CategoryTheory.Monad.Algebra T where
  A := X
  a := F.preimage (inv (M.comparison.app X) ≫ a)
  unit := by
    apply M.reflects_unit
    simpa only [F.map_preimage, ← assoc, IsIso.hom_inv_id, id_comp] using unit
  assoc := by
    apply M.reflects_assoc
    simpa only [F.map_preimage, ← assoc, IsIso.hom_inv_id, id_comp] using mul

@[simp] theorem lift_descend_a (X : C) (a : S.obj (F.obj X) ⟶ F.obj X)
    (unit : S.η.app (F.obj X) ≫ a = 𝟙 (F.obj X))
    (mul : S.μ.app (F.obj X) ≫ a = S.map a ≫ a) :
    (M.lift.obj (M.descend X a unit mul)).a = a := by
  simp only [lift, descend, F.map_preimage, ← assoc, IsIso.hom_inv_id, id_comp]

/-- Transport an algebra operation to an isomorphic underlying object. -/
def transportAlgebra (A : CategoryTheory.Monad.Algebra S) (X : D) (i : X ≅ A.A) :
    CategoryTheory.Monad.Algebra S where
  A := X
  a := S.map i.hom ≫ A.a ≫ i.inv
  unit := by
    erw [← S.unit_naturality_assoc]
    simp only [A.unit_assoc, i.hom_inv_id]
  assoc := by
    simp only [S.map_comp, assoc]
    rw [← S.mu_naturality_assoc, A.assoc_assoc]
    simp only [← S.map_comp_assoc, i.inv_hom_id, S.map_id, id_comp]

/-- Every algebra on an underlying object in the essential image descends. -/
theorem essImage_iff (A : CategoryTheory.Monad.Algebra S) :
    M.lift.essImage A ↔ F.essImage A.A := by
  constructor
  · rintro ⟨B, ⟨i⟩⟩
    exact ⟨B.A, ⟨S.forget.mapIso i⟩⟩
  · rintro ⟨X, ⟨i⟩⟩
    let B := transportAlgebra A (F.obj X) i
    let E := M.descend X B.a B.unit B.assoc
    refine ⟨E, ⟨CategoryTheory.Monad.Algebra.isoMk i ?_⟩⟩
    change S.map i.hom ≫ A.a = (M.lift.obj (M.descend X B.a B.unit B.assoc)).a ≫ i.hom
    rw [M.lift_descend_a]
    dsimp [B, transportAlgebra]
    simp only [assoc, i.inv_hom_id, comp_id]

end Kernel.Augmented.Nerve.MonadMap

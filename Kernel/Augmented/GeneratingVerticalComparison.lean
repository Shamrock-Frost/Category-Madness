import Kernel.Augmented.GeneratingVerticalFunctor

/-! Vertical reconstruction recovers every augmented algebra's original vertical category.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating GeneratingMonadAlgebra
variable (A : BundledAlgebra.{w})

/-- The original arrow and its generating incidence fibre contain exactly the same data. -/
def verticalHomEquiv (a b : A.Obj) :
    @Quiver.Hom (Vertical (generatingComparison.obj A)) inferInstance a b ≃ (a ⟶ b) where
  toFun e := FinPath.Edge.reindex e.val e.property.1 e.property.2
  invFun f := A.arrowGenerators.map f
  left_inv e := by
    rcases e with ⟨⟨a', b', e⟩, ha, hb⟩
    cases ha; cases hb; rfl
  right_inv f := rfl

/-- Comparison-algebra path evaluation agrees with the original free evaluation. -/
theorem verticalHomEquiv_evalPath {a b : (forget.obj A).Objects} (p : Quiver.Path a b) :
    verticalHomEquiv A a b (evalPath (generatingComparison.obj A) p) =
      (evaluation A).base.vertical.map p := rfl

private theorem evaluation_edge {a b : (forget.obj A).Objects} (e : a ⟶ b) :
    (evaluation A).base.vertical.map e.toPath = verticalHomEquiv A a b e := by
  change (Graph.skeleton (𝟙 (forget.obj A))).baseMap.vertical.map e.toPath = _
  erw [Graph.SkeletonAssignment.baseMap_generator]
  rfl

/-- Recover the original vertical category from its comparison monad algebra. -/
def verticalToOriginal : Vertical (generatingComparison.obj A) ⥤ A.Obj where
  obj a := a
  map {a b} e := verticalHomEquiv A a b e
  map_id a := by
    change verticalHomEquiv A a a (evalPath (generatingComparison.obj A) .nil) = 𝟙 (show A.Obj from a)
    erw [verticalHomEquiv_evalPath]
    exact (evaluation A).base.vertical.map_id a
  map_comp {a b c} f g := by
    change verticalHomEquiv A a c
      (evalPath (generatingComparison.obj A) (f.toPath.comp g.toPath)) = _
    erw [verticalHomEquiv_evalPath, Functor.map_comp, evaluation_edge, evaluation_edge]
    rfl

/-- The inverse sends each original arrow to its full generating incidence fibre. -/
def verticalFromOriginal : A.Obj ⥤ Vertical (generatingComparison.obj A) where
  obj a := a
  map {a b} f := (verticalHomEquiv A a b).symm f
  map_id a := by
    apply (verticalHomEquiv A a a).injective
    exact ((verticalHomEquiv A a a).apply_symm_apply _).trans
      ((verticalToOriginal A).map_id a).symm
  map_comp {a b c} f g := by
    apply (verticalHomEquiv A a c).injective
    change _ = (verticalToOriginal A).map (_ ≫ _)
    erw [Functor.map_comp]
    exact (verticalHomEquiv A a c).apply_symm_apply _

/-- Both vertical comparison round trips, with identity and composition preserved. -/
def verticalComparisonEquivalence : Vertical (generatingComparison.obj A) ≌ A.Obj where
  functor := verticalToOriginal A
  inverse := verticalFromOriginal A
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change f ≫ 𝟙 b = 𝟙 a ≫ (verticalHomEquiv A a b).symm (verticalHomEquiv A a b f)
    rw [Category.comp_id, Category.id_comp, Equiv.symm_apply_apply])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change verticalHomEquiv A a b ((verticalHomEquiv A a b).symm f) ≫ 𝟙 b = 𝟙 a ≫ f
    rw [Category.comp_id, Category.id_comp, Equiv.apply_symm_apply])
  functor_unitIso_comp a := by
    change (verticalToOriginal A).map (𝟙 a) ≫ 𝟙 (show A.Obj from a) =
      𝟙 (show A.Obj from a)
    exact (Category.comp_id _).trans ((verticalToOriginal A).map_id a)

/-- Recovery commutes with every global augmented-algebra map. -/
theorem verticalToOriginal_naturality {A B : BundledAlgebra.{w}} (F : A ⟶ B) :
    GeneratingMonadAlgebra.verticalMap (generatingComparison.map F) ⋙ verticalToOriginal B =
      verticalToOriginal A ⋙ F.base.vertical := by
  apply Functor.hext
  · intro a; rfl
  · intro a b e
    rcases e with ⟨⟨a', b', e⟩, ha, hb⟩
    cases ha; cases hb; rfl

end Kernel.Augmented.BundledAlgebra

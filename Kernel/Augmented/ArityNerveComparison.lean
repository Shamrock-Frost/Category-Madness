import Kernel.Augmented.ArityRestrictionMonadicity
import Kernel.Augmented.NerveAdjunctionComparison

/-! The canonical comparison for the augmented free-arity nerve square.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.

No invertibility is asserted here: that is the exactness obligation on the chosen arities.
-/

open CategoryTheory CategoryTheory.Category Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Nerve
universe w
variable {C : Type w} [Category.{w} C] (i : C ⥤ Generating.Graph.{w})

private def nerveImageAlgebra (A : BundledAlgebra.{w}) : (restrictionMonad i).Algebra :=
  MonadMap.transportAlgebra
    ((Monad.comparison (restrictionAdjunction i)).obj ((algebraNerve i).obj A))
    ((baseNerve i).obj (BundledAlgebra.forget.obj A)) ((restrictionIso i).app A).symm

private def nerveAlgebraImage :
    AdjunctionAlgebraImage BundledAlgebra.freeForgetAdjunction (restrictionMonad i) (baseNerve i) where
  action A := (nerveImageAlgebra i A).a
  unit A := (nerveImageAlgebra i A).unit
  assoc A := (nerveImageAlgebra i A).assoc
  naturality {A B} f := by
    let S := restrictionMonad i
    let K := Monad.comparison (restrictionAdjunction i)
    change S.map ((baseNerve i).map (BundledAlgebra.forget.map f)) ≫
      (S.map ((restrictionIso i).inv.app B) ≫ (K.obj ((algebraNerve i).obj B)).a ≫
        (restrictionIso i).hom.app B) =
      (S.map ((restrictionIso i).inv.app A) ≫ (K.obj ((algebraNerve i).obj A)).a ≫
        (restrictionIso i).hom.app A) ≫ (baseNerve i).map (BundledAlgebra.forget.map f)
    rw [← S.map_comp_assoc]
    erw [(restrictionIso i).inv.naturality f]
    rw [S.map_comp, assoc]
    erw [(K.map ((algebraNerve i).map f)).h_assoc]
    simp only [assoc]
    erw [(restrictionIso i).hom.naturality f]
    rfl

/-- The canonical comparison whose invertibility is required by the arity theorem. -/
def arityMonadMap :
    MonadMap BundledAlgebra.generatingMonad (restrictionMonad i) (baseNerve i) :=
  (nerveAlgebraImage i).monadMap

private def arityComparisonIsoAt (A : BundledAlgebra.{w}) :
    (BundledAlgebra.generatingComparison ⋙ (arityMonadMap i).lift).obj A ≅
      (algebraNerve i ⋙ Monad.comparison (restrictionAdjunction i)).obj A :=
  Monad.Algebra.isoMk ((restrictionIso i).app A).symm (by
    change (restrictionMonad i).map ((restrictionIso i).inv.app A) ≫ _ =
      ((nerveAlgebraImage i).comparison.app (BundledAlgebra.forget.obj A) ≫
        (baseNerve i).map (BundledAlgebra.forget.map (BundledAlgebra.freeForgetAdjunction.counit.app A))) ≫
          (restrictionIso i).inv.app A
    rw [(nerveAlgebraImage i).comparison_action]
    dsimp [nerveAlgebraImage, nerveImageAlgebra, MonadMap.transportAlgebra]
    simp only [assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm)

/-- Both actual monadic comparisons are compatible with the augmented nerve. -/
def arityComparisonIso :
    BundledAlgebra.generatingComparison ⋙ (arityMonadMap i).lift ≅
      algebraNerve i ⋙ Monad.comparison (restrictionAdjunction i) :=
  NatIso.ofComponents (arityComparisonIsoAt i) (by
    intro A B f
    apply Monad.Algebra.Hom.ext
    exact (restrictionIso i).inv.naturality f)

/-- Dense arities with invertible canonical comparison give a full augmented nerve. -/
theorem algebraNerve_full [i.IsDense]
    [∀ X, IsIso ((arityMonadMap i).comparison.app X)] : (algebraNerve i).Full :=
  square_full (arityMonadMap i) BundledAlgebra.generatingMonadicEquivalence
    (restrictionMonadicEquivalence i) (algebraNerve i) (arityComparisonIso i)

/-- The augmented nerve recognition condition, under the explicit arity exactness hypothesis. -/
theorem algebraNerve_essImage_iff [i.IsDense]
    [∀ X, IsIso ((arityMonadMap i).comparison.app X)] (X : (Theory i)ᵒᵖ ⥤ Type w) :
    (algebraNerve i).essImage X ↔ (baseNerve i).essImage ((restriction i).obj X) :=
  restriction_essImage_iff (arityMonadMap i) BundledAlgebra.generatingMonadicEquivalence
    (restrictionMonadicEquivalence i) (algebraNerve i) (arityComparisonIso i)
    (restriction i) (Monad.comparisonForget (restrictionAdjunction i)) X

end Kernel.Augmented.Nerve

import Kernel.Augmented.ArityNerveComparison

/-! The canonical free-arity comparison on representable arities.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Presheaf Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Nerve
universe w
variable {C : Type w} [Category.{w} C] (i : C ⥤ Generating.Graph.{w})

/-- The mate of the free/forgetful unit under the presheaf restriction adjunction. -/
def freeNerveComparison (X : Generating.Graph.{w}) :
    (arityToTheory i).op.lan.obj ((baseNerve i).obj X) ⟶
      (algebraNerve i).obj (BundledAlgebra.free.obj X) :=
  ((restrictionAdjunction i).homEquiv _ _).symm
    ((baseNerve i).map (BundledAlgebra.freeForgetAdjunction.unit.app X) ≫
      (restrictionIso i).inv.app (BundledAlgebra.free.obj X))

/-- The monad comparison is the restriction of the free comparison, under the nerve square. -/
theorem arityMonadMap_comparison (X : Generating.Graph.{w}) :
    (arityMonadMap i).comparison.app X =
      (restriction i).map (freeNerveComparison i X) ≫
        (restrictionIso i).hom.app (BundledAlgebra.free.obj X) := by
  change (restrictionMonad i).map
      ((baseNerve i).map (BundledAlgebra.freeForgetAdjunction.unit.app X)) ≫
    ((restrictionMonad i).map ((restrictionIso i).inv.app (BundledAlgebra.free.obj X)) ≫
      (restriction i).map ((restrictionAdjunction i).counit.app
        ((algebraNerve i).obj (BundledAlgebra.free.obj X))) ≫
      (restrictionIso i).hom.app (BundledAlgebra.free.obj X)) = _
  simp only [freeNerveComparison, Adjunction.homEquiv_counit, Functor.map_comp, assoc]
  rfl

def baseRepresentableIso [i.Full] [i.Faithful] (c : C) :
    (baseNerve i).obj (i.obj c) ≅ uliftYoneda.{w}.obj c :=
  (Functor.FullyFaithful.ofFullyFaithful i).homNatIso c

def theoryRepresentableIso (c : C) :
    (algebraNerve i).obj (BundledAlgebra.free.obj (i.obj c)) ≅
      uliftYoneda.{w}.obj ((arityToTheory i).obj c) :=
  (Functor.FullyFaithful.ofFullyFaithful (theoryInclusion i)).homNatIso c

/-- Kan extension of the base representable is the corresponding free-theory representable. -/
def freeRepresentableIso [i.Full] [i.Faithful] (c : C) :
    (arityToTheory i).op.lan.obj ((baseNerve i).obj (i.obj c)) ≅
      (algebraNerve i).obj (BundledAlgebra.free.obj (i.obj c)) :=
  (arityToTheory i).op.lan.mapIso (baseRepresentableIso i c) ≪≫
    (compULiftYonedaIsoULiftYonedaCompLan.{w} (arityToTheory i)).symm.app c ≪≫
    (theoryRepresentableIso i c).symm

theorem freeNerveComparison_eq [i.Full] [i.Faithful] (c : C) :
    freeNerveComparison i (i.obj c) = (freeRepresentableIso i c).hom := by
  apply (cancel_epi ((arityToTheory i).op.lan.map (baseRepresentableIso i c).inv)).mp
  simp only [freeRepresentableIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [freeNerveComparison, ← Adjunction.homEquiv_naturality_left_symm]
  apply ((restrictionAdjunction i).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply uliftYonedaEquiv.injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp,
    uliftYonedaEquiv_comp]
  change ULift.up ((BundledAlgebra.freeForgetAdjunction.homEquiv _ _).symm
      (i.map (𝟙 c) ≫ BundledAlgebra.freeForgetAdjunction.unit.app (i.obj c))) =
    ((theoryRepresentableIso i c).inv.app (op ((arityToTheory i).obj c)))
      (((compULiftYonedaIsoULiftYonedaCompLan.{w} (arityToTheory i)).inv.app c).app
        (op ((arityToTheory i).obj c))
        (((arityToTheory i).op.lanUnit.app (uliftYoneda.{w}.obj c)).app (op c)
          (ULift.up (𝟙 c))))
  erw [compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (arityToTheory i) c]
  simp only [CategoryTheory.Functor.map_id, id_comp, Adjunction.homEquiv_symm_unit]
  rfl

instance [i.Full] [i.Faithful] (c : C) : IsIso (freeNerveComparison i (i.obj c)) := by
  rw [freeNerveComparison_eq]
  infer_instance

/-- The canonical monad comparison is invertible on every arity of a fully faithful family. -/
instance [i.Full] [i.Faithful] (c : C) :
    IsIso ((arityMonadMap i).comparison.app (i.obj c)) := by
  rw [arityMonadMap_comparison]
  infer_instance

end Kernel.Augmented.Nerve

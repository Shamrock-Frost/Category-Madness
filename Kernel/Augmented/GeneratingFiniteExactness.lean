import Kernel.Augmented.GeneratingFiniteDetection
import Kernel.Augmented.ArityRepresentableComparison

/-! Finite-incidence arity exactness follows from filtered-colimit preservation.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.

The only remaining hypothesis is preservation by the actual augmented generating
monad. Density, preservation by the base nerve, and exactness on arities are proved.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Nerve
universe w

instance {C : Type w} [Category.{w} C] (i : C ⥤ Generating.Graph.{w}) :
    PreservesColimitsOfSize.{w, w} (restrictionMonad i).toFunctor := by
  have := (restrictionAdjunction i).isLeftAdjoint
  change PreservesColimitsOfSize.{w, w} ((arityToTheory i).op.lan ⋙ restriction i)
  unfold restriction
  infer_instance

end Kernel.Augmented.Nerve

namespace Kernel.Augmented.Generating
universe w
variable [PreservesFilteredColimitsOfSize.{w, w} BundledAlgebra.generatingMonad.{w}.toFunctor]

/-- The concrete finite family satisfies arity exactness if the generating monad is finitary. -/
theorem finiteIncidence_comparison_isIso :
    IsIso (Nerve.arityMonadMap finiteIncidenceGraphs.{w}).comparison := by
  let α := (Nerve.arityMonadMap finiteIncidenceGraphs.{w}).comparison
  have (a : FiniteIncidence.{w}) :
      IsIso ((Functor.whiskerLeft Graph.presheafEquivalence.inverse α).app
        (finiteIncidenceInclusion.obj a)) :=
    inferInstanceAs (IsIso ((Nerve.arityMonadMap finiteIncidenceGraphs).comparison.app
      (finiteIncidenceGraphs.obj a)))
  have : IsIso (Functor.whiskerLeft Graph.presheafEquivalence.inverse α) :=
    isIso_of_finiteIncidence _
  have (X : Graph.{w}) : IsIso (α.app X) := by
    let e := Graph.presheafEquivalence.unitIso.app X
    have : IsIso (α.app (Graph.presheafEquivalence.inverse.obj
        (Graph.presheafEquivalence.functor.obj X))) :=
      inferInstanceAs (IsIso ((Functor.whiskerLeft Graph.presheafEquivalence.inverse α).app
        (Graph.presheafEquivalence.functor.obj X)))
    have : IsIso (α.app X ≫
        (BundledAlgebra.generatingMonad.toFunctor ⋙ Nerve.baseNerve finiteIncidenceGraphs).map
          e.hom) := by
      rw [← α.naturality]
      change IsIso (_ ≫ α.app (Graph.presheafEquivalence.inverse.obj
        (Graph.presheafEquivalence.functor.obj X)))
      infer_instance
    exact IsIso.of_isIso_comp_right (α.app X)
      ((BundledAlgebra.generatingMonad.toFunctor ⋙ Nerve.baseNerve finiteIncidenceGraphs).map e.hom)
  exact NatIso.isIso_of_isIso_app α

/-- Under finitarity, the augmented nerve for the finite-incidence family is full. -/
theorem finiteIncidenceNerve_full_of_finitary :
    (Nerve.algebraNerve finiteIncidenceGraphs.{w}).Full := by
  have := finiteIncidence_comparison_isIso.{w}
  exact finiteIncidenceNerve_full

/-- Under finitarity, restriction to finite incidence exactly recognizes augmented nerves. -/
theorem finiteIncidenceNerve_essImage_iff_of_finitary
    (X : (Nerve.Theory finiteIncidenceGraphs.{w})ᵒᵖ ⥤ Type w) :
    (Nerve.algebraNerve finiteIncidenceGraphs).essImage X ↔
      (Nerve.baseNerve finiteIncidenceGraphs).essImage
        ((Nerve.restriction finiteIncidenceGraphs).obj X) := by
  have := finiteIncidence_comparison_isIso.{w}
  exact finiteIncidenceNerve_essImage_iff X

omit [PreservesFilteredColimitsOfSize.{w, w} BundledAlgebra.generatingMonad.{w}.toFunctor] in
/-- For the finite family, canonical monad exactness is precisely finitarity. -/
theorem finiteIncidence_exactness_iff_finitary :
    (∀ X, IsIso ((Nerve.arityMonadMap finiteIncidenceGraphs.{w}).comparison.app X)) ↔
      PreservesFilteredColimitsOfSize.{w, w} BundledAlgebra.generatingMonad.{w}.toFunctor := by
  constructor
  · intro h
    have := h
    have := NatIso.isIso_of_isIso_app (Nerve.arityMonadMap finiteIncidenceGraphs.{w}).comparison
    have : PreservesFilteredColimitsOfSize.{w, w}
        (BundledAlgebra.generatingMonad.{w}.toFunctor ⋙ Nerve.baseNerve finiteIncidenceGraphs) :=
      ⟨fun J _ _ => preservesColimitsOfShape_of_natIso
        (asIso (Nerve.arityMonadMap finiteIncidenceGraphs).comparison)⟩
    exact ⟨fun J _ _ => preservesColimitsOfShape_of_reflects_of_preserves
      BundledAlgebra.generatingMonad.toFunctor (Nerve.baseNerve finiteIncidenceGraphs)⟩
  · intro h
    have := h
    have := finiteIncidence_comparison_isIso.{w}
    infer_instance

end Kernel.Augmented.Generating

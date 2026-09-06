import Kernel.Augmented.GeneratingFiniteFamily
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-! Filtered-colimit preservation by the finite-incidence base nerve.
Cites: D-KR-15, D-KR-18, AT-FD-7.

This concerns the base nerve. Preservation by the generating monad is a
separate obligation.
-/

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
noncomputable section
namespace Kernel.Augmented.Generating
universe w
attribute [local instance] fact_isRegular_aleph0

instance (a : FiniteIncidence.{w}) :
    IsFinitelyPresentable.{w} (finiteIncidenceInclusion.obj a) :=
  ((equivSmallModel _).inverse.obj a).property

instance (a : FiniteIncidence.{w}) :
    IsFinitelyPresentable.{w} (finiteIncidenceGraphs.obj a) :=
  Graph.presheafEquivalence.symm.toAdjunction.isCardinalPresentable_leftAdjoint_obj
    (ℵ₀ : Cardinal.{w}) (finiteIncidenceInclusion.obj a)

instance : PreservesFilteredColimitsOfSize.{w, w}
    (Nerve.baseNerve finiteIncidenceGraphs.{w}) where
  preserves_filtered_colimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro a
    change PreservesColimitsOfShape J
      (uliftCoyoneda.{w}.obj (op (finiteIncidenceGraphs.obj a.unop)))
    have : (uliftCoyoneda.{w}.obj (op (finiteIncidenceGraphs.obj a.unop))).IsFinitelyAccessible :=
      inferInstance
    have := (Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize).mp this
    infer_instance

/-- A map from a finite incidence diagram factors through a finite support. -/
theorem finiteIncidence_factors_through_support (a : FiniteIncidence.{w})
    {P : Presheaf.{w}} (f : finiteIncidenceInclusion.obj a ⟶ P) :
    ∃ (s : Finset (Element P))
      (g : finiteIncidenceInclusion.obj a ⟶ (finiteSupportDiagram P).obj s),
      g ≫ (finiteSupportCocone P).ι.app s = f :=
  IsFinitelyPresentable.exists_hom_of_isColimit (finiteSupportIsColimit P) f

/-- Equality between finite-stage maps is witnessed after passing to a finite support. -/
theorem finiteIncidence_support_equality (a : FiniteIncidence.{w})
    {P : Presheaf.{w}} {s t : Finset (Element P)}
    (f : finiteIncidenceInclusion.obj a ⟶ (finiteSupportDiagram P).obj s)
    (g : finiteIncidenceInclusion.obj a ⟶ (finiteSupportDiagram P).obj t)
    (h : f ≫ (finiteSupportCocone P).ι.app s = g ≫ (finiteSupportCocone P).ι.app t) :
    ∃ (u : Finset (Element P)) (hs : s ⟶ u) (ht : t ⟶ u),
      f ≫ (finiteSupportDiagram P).map hs = g ≫ (finiteSupportDiagram P).map ht :=
  IsFinitelyPresentable.exists_eq_of_isColimit (finiteSupportIsColimit P) f g h

end Kernel.Augmented.Generating

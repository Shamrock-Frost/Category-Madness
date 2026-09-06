import Kernel.Augmented.GeneratingFiniteNerve

/-! Detecting isomorphisms of filtered-colimit-preserving functors on finite incidence.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace Kernel.Augmented.Generating
universe w u v
variable {D : Type u} [Category.{v} D]

/-- Finite supports detect an isomorphism of two functors preserving their colimits. -/
theorem isIso_app_of_finite_supports {F H : Presheaf.{w} ⥤ D} (α : F ⟶ H)
    (P : Presheaf.{w})
    [PreservesColimit (finiteSupportDiagram P) F]
    [PreservesColimit (finiteSupportDiagram P) H]
    (h : ∀ Q : Presheaf.{w}, Finite (Element Q) → IsIso (α.app Q)) :
    IsIso (α.app P) := by
  have (s : Finset (Element P)) :
      IsIso ((Functor.whiskerLeft (finiteSupportDiagram P) α).app s) :=
    h _ inferInstance
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft (finiteSupportDiagram P) α)
  exact isIso_app_coconePt_of_preservesColimit (finiteSupportDiagram P) α
    (finiteSupportCocone P) (finiteSupportIsColimit P)

/-- Every finite incidence presheaf occurs in the small candidate up to isomorphism. -/
theorem finiteIncidence_essImage (P : Presheaf.{w}) [Finite (Element P)] :
    finiteIncidenceInclusion.essImage P := by
  let X : (ObjectProperty.isFinitelyPresentable.{w} Presheaf.{w}).FullSubcategory :=
    ⟨P, show IsFinitelyPresentable.{w} P from inferInstance⟩
  exact ⟨(equivSmallModel _).functor.obj X,
    ⟨(ObjectProperty.isFinitelyPresentable.{w} Presheaf.{w}).ι.mapIso
      ((equivSmallModel _).unitIso.symm.app X)⟩⟩

/-- A transformation between filtered-colimit-preserving functors is determined on finite arities. -/
theorem isIso_of_finiteIncidence {F H : Presheaf.{w} ⥤ D} (α : F ⟶ H)
    [PreservesFilteredColimitsOfSize.{w, w} F]
    [PreservesFilteredColimitsOfSize.{w, w} H]
    [∀ a : FiniteIncidence.{w}, IsIso (α.app (finiteIncidenceInclusion.obj a))] :
    IsIso α := by
  have (P : Presheaf.{w}) : IsIso (α.app P) := by
    apply isIso_app_of_finite_supports α P
    intro Q hQ
    obtain ⟨a, ⟨e⟩⟩ := finiteIncidence_essImage Q
    have : IsIso (F.map e.hom ≫ α.app Q) := by
      rw [α.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map e.hom) (α.app Q)
  exact NatIso.isIso_of_isIso_app α

end Kernel.Augmented.Generating

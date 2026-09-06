import Kernel.Augmented.GeneratingSupportColimit
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.Limits

/-! Finite incidence characterizes finitely presentable generating presheaves.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Generating
universe w
attribute [local instance] fact_isRegular_aleph0

instance (P : Presheaf.{w}) [Finite (Element P)] : IsFinitelyPresentable.{w} P := by
  have : Finite P.Elements := inferInstanceAs (Finite (Element P))
  have (X Y : P.Elements) : Finite (X ⟶ Y) := by
    change Finite {f : X.1 ⟶ Y.1 // P.map f X.2 = Y.2}
    infer_instance
  have : Finite (Arrow P.Elements) :=
    Finite.of_equiv _ (Arrow.equivSigma P.Elements).symm
  have : Finite (Arrow P.Elementsᵒᵖ) :=
    Finite.of_equiv _ (Arrow.opEquiv P.Elements).symm
  have (x : P.Elementsᵒᵖ) : IsFinitelyPresentable.{w} ((Presheaf.functorToRepresentables P).obj x) := by
    change IsFinitelyPresentable.{w} (uliftYoneda.{w}.obj x.unop.1.unop)
    infer_instance
  exact isCardinalPresentable_of_isColimit.{w} (Presheaf.coconeOfRepresentable P)
    (Presheaf.colimitOfRepresentable P) (ℵ₀ : Cardinal.{w})
    ((hasCardinalLT_aleph0_iff _).mpr inferInstance)

/-- Compactness forces the identity to factor through one finite incidence support. -/
theorem finite_elements_of_finitelyPresentable (P : Presheaf.{w}) [IsFinitelyPresentable.{w} P] :
    Finite (Element P) := by
  obtain ⟨s, f, hf⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (finiteSupportIsColimit P) (𝟙 P)
  let g : Element ((finiteSupportDiagram P).obj s) → Element P := fun x => ⟨x.1, x.2.val⟩
  apply Finite.of_surjective g
  intro x
  refine ⟨⟨x.1, f.app x.1 x.2⟩, ?_⟩
  have hx := ConcreteCategory.congr_hom (congr_app hf x.1) x.2
  change (f.app x.1 x.2).val = x.2 at hx
  exact congrArg (Sigma.mk x.1) hx

theorem finitelyPresentable_iff_finite_elements (P : Presheaf.{w}) :
    IsFinitelyPresentable.{w} P ↔ Finite (Element P) := by
  constructor
  · intro h
    have := h
    exact finite_elements_of_finitelyPresentable P
  · intro h
    have := h
    infer_instance

end Kernel.Augmented.Generating

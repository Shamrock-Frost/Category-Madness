import Kernel.Augmented.NerveRecognition
import Mathlib.CategoryTheory.Equivalence

/-! Transfer the algebra recognition lemma through supplied monadic comparisons.
This is the recognition step of the BMW exact-square argument. It does not
construct the augmented monad, identify its arities, or prove the required mate invertible.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
namespace Kernel.Augmented.Nerve
universe u v u' v' uB vB uP vP
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {B : Type uB} [Category.{vB} B] {P : Type uP} [Category.{vP} P]
  {T : CategoryTheory.Monad C} {S : CategoryTheory.Monad D} {F : C ⥤ D}
  (M : MonadMap T S F) [fullF : F.Full] [faithfulF : F.Faithful] [isoM : ∀ X, IsIso (M.comparison.app X)]
  (E : B ≌ CategoryTheory.Monad.Algebra T) (E' : P ≌ CategoryTheory.Monad.Algebra S)
  (N : B ⥤ P) (square : E.functor ⋙ M.lift ≅ N ⋙ E'.functor)

include M E E' square fullF faithfulF isoM

omit fullF isoM in
/-- Faithfulness transfers through the supplied comparison square. -/
theorem square_faithful : N.Faithful := by
  let : (N ⋙ E'.functor).Faithful := Functor.Faithful.of_iso square
  exact Functor.Faithful.of_comp N E'.functor

theorem square_full : N.Full := by
  let : (N ⋙ E'.functor).Full := Functor.Full.of_iso square
  exact Functor.Full.of_comp_faithful N E'.functor

/-- Recognition after passing through the supplied category equivalences. -/
theorem square_essImage_iff (X : P) :
    N.essImage X ↔ F.essImage (E'.functor.obj X).A := by
  rw [← M.essImage_iff]
  constructor
  · rintro ⟨Y, ⟨i⟩⟩
    exact ⟨E.functor.obj Y, ⟨square.app Y ≪≫ E'.functor.mapIso i⟩⟩
  · rintro ⟨A, ⟨i⟩⟩
    refine ⟨E.inverse.obj A, ⟨E'.functor.preimageIso ?_⟩⟩
    exact (square.app (E.inverse.obj A)).symm ≪≫ M.lift.mapIso (E.counitIso.app A) ≪≫ i

/-- The recognized condition can be expressed using the original restriction functor. -/
theorem restriction_essImage_iff (R : P ⥤ D)
    (underlying : E'.functor ⋙ S.forget ≅ R) (X : P) :
    N.essImage X ↔ F.essImage (R.obj X) := by
  rw [square_essImage_iff M E E' N square X]
  exact ⟨Functor.essImage.ofIso (underlying.app X), Functor.essImage.ofIso (underlying.app X).symm⟩

end Kernel.Augmented.Nerve

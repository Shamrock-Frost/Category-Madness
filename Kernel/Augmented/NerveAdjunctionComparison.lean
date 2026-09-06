import Kernel.Augmented.NerveMonadMap
import Mathlib.CategoryTheory.Monad.Adjunction

/-! Construct the canonical monad comparison from algebra operations over an adjunction.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory CategoryTheory.Category
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Nerve
universe u v uB vB uD vD
variable {C : Type u} [Category.{v} C] {B : Type uB} [Category.{vB} B]
  {D : Type uD} [Category.{vD} D] {L : C ⥤ B} {U : B ⥤ C}
  (adj : L ⊣ U) (S : CategoryTheory.Monad D) (F : C ⥤ D)

/-- Lawful operations on the images of objects and maps of the adjunction's domain. -/
structure AdjunctionAlgebraImage (adj : L ⊣ U) (S : CategoryTheory.Monad D) (F : C ⥤ D) where
  action : ∀ A, S.obj (F.obj (U.obj A)) ⟶ F.obj (U.obj A)
  unit : ∀ A, S.η.app (F.obj (U.obj A)) ≫ action A = 𝟙 _
  assoc : ∀ A, S.μ.app (F.obj (U.obj A)) ≫ action A = S.map (action A) ≫ action A
  naturality : ∀ {A B} (f : A ⟶ B),
    S.map (F.map (U.map f)) ≫ action B = action A ≫ F.map (U.map f)

namespace AdjunctionAlgebraImage
variable {adj S F} (H : AdjunctionAlgebraImage adj S F)

def comparison : F ⋙ S.toFunctor ⟶ adj.toMonad.toFunctor ⋙ F where
  app X := S.map (F.map (adj.unit.app X)) ≫ H.action (L.obj X)
  naturality {X Y} f := by
    dsimp [Adjunction.toMonad]
    rw [← Category.assoc, ← S.map_comp, ← F.map_comp]
    erw [adj.unit.naturality]
    simp only [Functor.comp_map, F.map_comp, S.map_comp, Category.assoc]
    rw [H.naturality]

@[reassoc] theorem comparison_action (A : B) :
    H.comparison.app (U.obj A) ≫ F.map (U.map (adj.counit.app A)) = H.action A := by
  dsimp [comparison, Adjunction.toMonad]
  rw [Category.assoc, ← H.naturality, ← S.map_comp_assoc, ← F.map_comp,
    adj.right_triangle_components, F.map_id, S.map_id, id_comp]

/-- The comparison is determined by the unit and the operation on each free object. -/
def monadMap : MonadMap adj.toMonad S F where
  comparison := H.comparison
  unit X := by
    dsimp [comparison, Adjunction.toMonad]
    rw [← S.unit_naturality_assoc, H.unit]
    simp only [Functor.id_obj, comp_id]
  mul X := by
    have h : S.map (H.comparison.app X) ≫ H.action (L.obj X) =
        S.μ.app (F.obj X) ≫ H.comparison.app X := by
      dsimp [comparison, Adjunction.toMonad]
      rw [S.map_comp, Category.assoc, ← H.assoc, ← S.mu_naturality_assoc]
    change S.μ.app (F.obj X) ≫ H.comparison.app X =
      S.map (H.comparison.app X) ≫ H.comparison.app (U.obj (L.obj X)) ≫
        F.map (U.map (adj.counit.app (L.obj X)))
    rw [H.comparison_action]
    exact h.symm

end AdjunctionAlgebraImage
end Kernel.Augmented.Nerve

import Kernel.Augmented.GeneratingPathAction
import Mathlib.CategoryTheory.Category.Cat

/-! Vertical reconstruction is functorial in arbitrary generating-monad algebras.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable {A B : BundledAlgebra.generatingMonad.{w}.Algebra}

/-- A monad-algebra map commutes with evaluation of every vertical path. -/
theorem map_evalPath (F : A ⟶ B) {a b : A.A.Objects} (p : Quiver.Path a b) :
    (Graph.verticalMap F.f).map (evalPath A p) =
      evalPath B ((Graph.verticalMap F.f).mapPath p) := by
  apply Subtype.ext
  have h := congrArg (fun f : BundledAlgebra.generatingMonad.toFunctor.obj A.A ⟶ B.A =>
    Graph.mapVertical f ⟨a, b, p⟩) F.h
  change Graph.mapVertical B.a
      (⟨Graph.mapObject F.f a, Graph.mapObject F.f b,
        (BundledAlgebra.free.map F.f).base.vertical.map p⟩ : FinPath.Edge (Paths B.A.Objects)) =
    Graph.mapVertical F.f (Graph.mapVertical A.a ⟨a, b, p⟩) at h
  erw [Graph.free_map_path] at h
  exact h.symm

/-- The vertical functor induced by any morphism of generating-monad algebras. -/
def verticalMap (F : A ⟶ B) : Vertical A ⥤ Vertical B :=
  (pathEvaluation A).functorOfCompatible (pathEvaluation B) (Graph.verticalMap F.f)
    (map_evalPath F)

/-- Reconstruct vertical categories and functors from the whole Eilenberg–Moore category. -/
def verticalFunctor : BundledAlgebra.generatingMonad.{w}.Algebra ⥤ Cat.{w,w} where
  obj A := Cat.of (Vertical A)
  map F := Cat.Hom.ofFunctor (verticalMap F)
  map_id A := by
    apply Cat.Hom.ext
    apply Functor.hext
    · intro a; rfl
    · intro a b f; rfl
  map_comp F G := by
    apply Cat.Hom.ext
    apply Functor.hext
    · intro a; rfl
    · intro a b f; rfl

end Kernel.Augmented.GeneratingMonadAlgebra

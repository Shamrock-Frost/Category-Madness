import Kernel.Augmented.FreeGeneratingUnique
import Mathlib.CategoryTheory.Monad.Adjunction

/-! The global free/forgetful adjunction over generating incidence presheaves.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented
universe w

namespace Generating.Graph

/-- The global mapping property, including changes of objects and vertical arrows. -/
def homEquiv (G : Graph.{w}) (A : BundledAlgebra.{w}) :
    (G.freeObject ⟶ A) ≃ (G ⟶ BundledAlgebra.forget.obj A) where
  toFun := restrictMap
  invFun := lift
  left_inv := lift_restrictMap
  right_inv := unit_lift

theorem homEquiv_naturality (G : Graph.{w}) (A B : BundledAlgebra.{w})
    (f : A ⟶ B) (g : G.freeObject ⟶ A) :
    homEquiv G B (g ≫ f) = homEquiv G A g ≫ BundledAlgebra.forget.map f := by
  change G.unit ≫ BundledAlgebra.forget.map (g ≫ f) =
    (G.unit ≫ BundledAlgebra.forget.map g) ≫ BundledAlgebra.forget.map f
  rw [Functor.map_comp, Category.assoc]

end Generating.Graph

namespace BundledAlgebra

/-- Free augmented algebra, functorial in every generating incidence sort. -/
def free : Generating.Graph.{w} ⥤ BundledAlgebra.{w} :=
  Adjunction.leftAdjointOfEquiv Generating.Graph.homEquiv
    Generating.Graph.homEquiv_naturality

/-- The concrete global free/forgetful adjunction. -/
def freeForgetAdjunction : free.{w} ⊣ forget :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The induced monad on generating incidence presheaves. -/
def generatingMonad : Monad Generating.Graph.{w} := freeForgetAdjunction.toMonad

theorem freeForgetAdjunction_homEquiv (G : Generating.Graph.{w}) (A : BundledAlgebra.{w}) :
    freeForgetAdjunction.homEquiv G A = Generating.Graph.homEquiv G A := by
  unfold freeForgetAdjunction Adjunction.adjunctionOfEquivLeft
  erw [Adjunction.mkOfHomEquiv_homEquiv]

theorem freeForgetAdjunction_unit (G : Generating.Graph.{w}) :
    freeForgetAdjunction.unit.app G = G.unit := by
  change G.unit ≫ forget.map (𝟙 G.freeObject) = G.unit
  rw [forget.map_id, Category.comp_id]

theorem freeForgetAdjunction_counit (A : BundledAlgebra.{w}) :
    freeForgetAdjunction.counit.app A = Generating.Graph.lift (𝟙 (forget.obj A)) := rfl

end BundledAlgebra
end Kernel.Augmented

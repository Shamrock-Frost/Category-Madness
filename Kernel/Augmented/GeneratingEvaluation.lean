import Kernel.Augmented.GlobalForgetfulFaithful

/-! Evaluation and the concrete monadicity comparison equation.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w

abbrev evaluation (A : BundledAlgebra.{w}) : free.obj (forget.obj A) ⟶ A :=
  freeForgetAdjunction.counit.app A

theorem lift_eq_free_map_evaluation {G : Generating.Graph.{w}} {A : BundledAlgebra.{w}}
    (F : G ⟶ forget.obj A) : Generating.Graph.lift F = free.map F ≫ evaluation A := by
  have h := freeForgetAdjunction.homEquiv_counit (g := F)
  rw [freeForgetAdjunction_homEquiv] at h
  exact h

theorem unit_evaluation (A : BundledAlgebra.{w}) :
    (forget.obj A).unit ≫ forget.map (evaluation A) = 𝟙 (forget.obj A) := by
  rw [← freeForgetAdjunction_unit]
  exact freeForgetAdjunction.right_triangle_components A

/-- A graph map is compatible when it commutes with evaluation of all free expressions. -/
def EvaluationCompatible {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) : Prop :=
  forget.map (Generating.Graph.lift F) = forget.map (evaluation A) ≫ F

theorem evaluationCompatible_iff {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) : EvaluationCompatible F ↔
      (generatingMonad.toFunctor.map F) ≫ (generatingComparison.obj B).a =
        (generatingComparison.obj A).a ≫ F := by
  unfold EvaluationCompatible
  rw [lift_eq_free_map_evaluation]
  erw [forget.map_comp]
  rfl

/-- Monad-algebra morphisms in the comparison are precisely evaluation-compatible graph maps. -/
def comparisonHomEquiv (A B : BundledAlgebra.{w}) :
    (generatingComparison.obj A ⟶ generatingComparison.obj B) ≃
      {F : forget.obj A ⟶ forget.obj B // EvaluationCompatible F} where
  toFun M := ⟨M.f, (evaluationCompatible_iff M.f).mpr M.h⟩
  invFun F := ⟨F.val, (evaluationCompatible_iff F.val).mp F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_evaluationCompatible {A B : BundledAlgebra.{w}} (F : A ⟶ B) :
    EvaluationCompatible (forget.map F) :=
  (comparisonHomEquiv A B (generatingComparison.map F)).property

end Kernel.Augmented.BundledAlgebra

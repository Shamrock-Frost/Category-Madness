import Kernel.Augmented.GeneratingReconstructionGraph
import Kernel.Augmented.GeneratingComparisonSubstitution

/-! Essential surjectivity of the generating comparison and monadicity of augmented algebras.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented
universe w
open Generating
namespace GeneratingMonadAlgebra
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

/-- The reconstructed evaluation is the supplied monad action under the incidence isomorphism. -/
theorem reconstruction_action :
    BundledAlgebra.forget.map (reconstructionEvaluation A) = A.a ≫ reconstructionUnit A := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s⟩
  cases s with
  | point =>
    ext a
    exact (action_object A a).symm
  | vertical =>
    ext e
    rcases e with ⟨a, b, p⟩
    change (⟨a, b, evalPath A p⟩ : FinPath.Edge (Vertical A)) =
      Graph.mapVertical (reconstructionUnit A) (Graph.mapVertical A.a ⟨a, b, p⟩)
    rw [reconstructionUnit_vertical]
    exact A.A.verticalPack_fiber (evalPath A p)
  | horizontal =>
    ext e
    rcases e with ⟨a, b, j⟩
    change (⟨a, b, j⟩ : FinPath.Edge (Kernel.Augmented.Horizontal (horizontal A))) =
      Graph.mapHorizontal (reconstructionUnit A) (Graph.mapHorizontal A.a ⟨a, b, j⟩)
    rw [reconstructionUnit_horizontal, action_horizontal]
    exact A.A.horizontalPack_fiber j
  | cell n ε =>
    ext x
    apply Subtype.ext
    change ((evaluationCells A).arityCell x).val =
      (Graph.mapCell (reconstructionUnit A) (Graph.mapCell A.a x)).val
    rw [CellGraph.OverMap.arityCell_val, reconstructionUnit_cell]
    exact evaluationCells_arityCell A x

def reconstructionHom : A ⟶ BundledAlgebra.generatingComparison.obj (reconstructed A) where
  f := reconstructionUnit A
  h := by
    have h := congrArg BundledAlgebra.forget.map
      (Graph.lift_restrictMap (reconstructionEvaluation A))
    rw [BundledAlgebra.lift_eq_free_map_evaluation] at h
    erw [Functor.map_comp] at h
    exact h.trans (reconstruction_action A)

/-- Each generating-monad algebra is isomorphic to the comparison of its reconstructed algebra. -/
def reconstructionIso : A ≅ BundledAlgebra.generatingComparison.obj (reconstructed A) :=
  Monad.Algebra.isoMk (reconstructionGraphIso A) (reconstructionHom A).h

end GeneratingMonadAlgebra
namespace BundledAlgebra

instance : generatingComparison.{w}.EssSurj where
  mem_essImage A := ⟨GeneratingMonadAlgebra.reconstructed A,
    ⟨(GeneratingMonadAlgebra.reconstructionIso A).symm⟩⟩

instance : generatingComparison.{w}.IsEquivalence where

/-- Augmented algebras are exactly the Eilenberg–Moore algebras of the generating monad. -/
def generatingMonadicEquivalence : BundledAlgebra.{w} ≌ generatingMonad.Algebra :=
  generatingComparison.asEquivalence

instance : MonadicRightAdjoint forget.{w} where
  L := free
  adj := freeForgetAdjunction
  eqv := inferInstanceAs generatingComparison.IsEquivalence

end BundledAlgebra
end Kernel.Augmented

import Kernel.Augmented.GeneratingCellActionSection

/-! Free-cell evaluation preserves arbitrary nonempty-row substitution.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

private theorem edge_heq {C : Type w} [Quiver.{w} C] {x y : FinPath.Edge C} (h : x = y) :
    HEq x.2.2 y.2.2 := by cases h; rfl

private theorem free_action_generatorOuter {f g : Side A.A.freeObject.Obj}
    (r : A.A.freeObject.cells.NonemptyRow f g) {a b : A.A.Objects}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.A.freeHorizontal a b)
    (ψ : A.A.freeObject.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    CellGraph.pack ((BundledAlgebra.free.map A.a).toOverMap.outerCell
      (A.A.freeObject.generatorNonemptyRow r) (A.A.freeObject.generatorArrow h)
      (A.A.freeObject.generatorArrow k) (A.A.freeObject.generatorShortPath L)
      (A.A.freeObject.generatorOuter r h k L ψ)) =
    CellGraph.pack (generatorOuter A ((evaluationCells A).nonemptyRow r)
      (evalPath A h) (evalPath A k) ((evaluationBase A).shortPath L)
      ((evaluationCells A).outerCell r h k L ψ)) := by
  erw [CellGraph.OverMap.pack_outerCell]
  unfold BundledAlgebra.generatorOuter generatorOuter
  erw [CellGraph.pack_castInput, CellGraph.pack_castInput, free_action_generatorCell]
  apply generatorCell_congr A
  exact ((evaluationCells A).pack_cell ψ).trans ((evaluationCells A).pack_outerCell r h k L ψ).symm

private theorem free_action_substituteImage {f g : Side A.A.freeObject.Obj}
    (r : A.A.freeObject.cells.NonemptyRow f g) {a b : A.A.Objects}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.A.freeHorizontal a b)
    (ψ : A.A.freeObject.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    (BundledAlgebra.free.map A.a).toOverMap.substituteImage A.A.freeAlgebra.toOperations
      (A.A.freeObject.generatorNonemptyRow r) (A.A.freeObject.generatorArrow h)
      (A.A.freeObject.generatorArrow k) (A.A.freeObject.generatorShortPath L)
      (A.A.freeObject.generatorOuter r h k L ψ) =
    CellGraph.pack (A.A.freeAlgebra.substitute
      (generatorNonemptyRow A ((evaluationCells A).nonemptyRow r))
      (evalPath A h).toPath (evalPath A k).toPath ((evaluationBase A).shortPath L)
      (generatorOuter A ((evaluationCells A).nonemptyRow r) (evalPath A h) (evalPath A k)
        ((evaluationBase A).shortPath L) ((evaluationCells A).outerCell r h k L ψ))) := by
  apply Operations.pack_substitute_heq _ (free_action_generatorSide A f) (free_action_generatorSide A g)
    (free_action_generatorRow A r.val) (action_object A a) (action_object A b)
    (edge_heq (free_action_single A h)) (edge_heq (free_action_single A k))
    ((free_action_generatorShortPath A L).trans (heq_of_eq (evaluationBase_shortPath A L)).symm)
  exact CellGraph.Total.cell_heq (free_action_generatorOuter A r h k L ψ)

/-- The action preserves substitution at every free row and every incident outer cell. -/
theorem evaluationCells_substitute {f g : Side A.A.freeObject.Obj}
    (r : A.A.freeObject.cells.NonemptyRow f g) {a b : A.A.Objects}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.A.freeHorizontal a b)
    (ψ : A.A.freeObject.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.substitute r h k L ψ)) =
      (evaluationCells A).substituteImage (operations A) r h k L ψ := by
  have he := A.A.freeObject.generatorInputs_evaluation (CellGraph.OverMap.id A.A.freeObject.cells)
    A.A.freeAlgebra.toOperations r h k L ψ
  erw [CellGraph.OverMap.id_substituteImage, CellGraph.OverMap.id_substituteImage] at he
  have hm := evaluationCells_multiplication A
    (CellGraph.pack ((BundledAlgebra.forget.obj A.A.freeObject).freeAlgebra.substitute
      (A.A.freeObject.generatorNonemptyRow r) (A.A.freeObject.generatorArrow h)
      (A.A.freeObject.generatorArrow k) (A.A.freeObject.generatorShortPath L)
      (A.A.freeObject.generatorOuter r h k L ψ)))
  erw [(BundledAlgebra.evaluation A.A.freeObject).substitute,
    (BundledAlgebra.free.map A.a).substitute] at hm
  have hleft : (BundledAlgebra.evaluation A.A.freeObject).toOverMap.substituteImage A.A.freeAlgebra.toOperations
      (A.A.freeObject.generatorNonemptyRow r) (A.A.freeObject.generatorArrow h)
      (A.A.freeObject.generatorArrow k) (A.A.freeObject.generatorShortPath L)
      (A.A.freeObject.generatorOuter r h k L ψ) =
      CellGraph.pack (A.A.freeAlgebra.substitute r h k L ψ) := he
  erw [hleft, free_action_substituteImage] at hm
  exact hm.trans (operations_substitute A ((evaluationCells A).nonemptyRow r)
    (evalPath A h) (evalPath A k) ((evaluationBase A).shortPath L)
    ((evaluationCells A).outerCell r h k L ψ)).symm

/-- Evaluation respects all three primitive operations over the reconstructed vertical category. -/
def evaluationOperations : A.A.freeAlgebra.toOperations.OverMap (operations A) where
  toOverMap := evaluationCells A
  horizontalIdentity := evaluationCells_horizontalIdentity A
  verticalIdentity := evaluationCells_verticalIdentity A
  substitute := evaluationCells_substitute A

end Kernel.Augmented.GeneratingMonadAlgebra

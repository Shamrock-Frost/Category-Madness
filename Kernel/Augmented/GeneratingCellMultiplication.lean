import Kernel.Augmented.GeneratingCellOperations
import Kernel.Augmented.GeneratingSectionSubstitution

/-! Cell evaluation and the multiplication of the generating monad.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

/-- Evaluating after free flattening agrees with evaluating the inner cells first. -/
theorem evaluationCells_multiplication
    (x : (BundledAlgebra.forget.obj A.A.freeObject).freeObject.cells.Total) :
    (evaluationCells A).total ((BundledAlgebra.evaluation A.A.freeObject).total x) =
      (evaluationCells A).total ((BundledAlgebra.free.map A.a).total x) := by
  have h := congrArg (fun F : BundledAlgebra.generatingMonad.toFunctor.obj
      (BundledAlgebra.generatingMonad.toFunctor.obj A.A) ⟶ A.A => Graph.mapCell F x.arityCell) A.assoc
  change Graph.mapCell A.a ((BundledAlgebra.evaluation A.A.freeObject).toOverMap.arityCell x.arityCell) =
    Graph.mapCell A.a ((BundledAlgebra.free.map A.a).toOverMap.arityCell x.arityCell) at h
  have hm := evaluationCells_arityCell A
    ((BundledAlgebra.evaluation A.A.freeObject).toOverMap.arityCell x.arityCell)
  have hf := evaluationCells_arityCell A ((BundledAlgebra.free.map A.a).toOverMap.arityCell x.arityCell)
  erw [CellGraph.OverMap.arityCell_val] at hm hf
  exact hm.trans ((congrArg (fun x => CellGraph.pack (G := cells A) (A.A.generator x)) h).trans hf.symm)

/-- The free functor maps each incident cell generator by the underlying graph map. -/
theorem free_action_cell {n ε} (x : A.A.freeObject.cells.ArityCell n ε) :
    (BundledAlgebra.free.map A.a).total
      (CellGraph.pack ((BundledAlgebra.forget.obj A.A.freeObject).freeCell x)) =
        CellGraph.pack (A.A.freeCell (Graph.mapCell A.a x)) := by
  have h := BundledAlgebra.freeForgetAdjunction.unit.naturality A.a
  erw [BundledAlgebra.freeForgetAdjunction_unit,
    BundledAlgebra.freeForgetAdjunction_unit] at h
  have he := congrArg (fun F : BundledAlgebra.forget.obj A.A.freeObject ⟶
    BundledAlgebra.forget.obj A.A.freeObject => (Graph.mapCell F x).val) h
  change CellGraph.pack (A.A.freeCell (Graph.mapCell A.a x)) =
    ((BundledAlgebra.free.map A.a).toOverMap.arityCell
      ((BundledAlgebra.forget.obj A.A.freeObject).unitCell x)).val at he
  erw [CellGraph.OverMap.arityCell_val] at he
  exact he.symm

/-- Evaluation preserves the horizontal identity at every free horizontal edge. -/
theorem evaluationCells_horizontalIdentity {a b : A.A.Objects} (j : A.A.freeHorizontal a b) :
    (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.horizontalIdentity j)) =
      CellGraph.pack ((operations A).horizontalIdentity ((evaluationBase A).horizontal j)) :=
  (operations_horizontalIdentity A j).symm

/-- Evaluation preserves the vertical identity at every free vertical path. -/
theorem evaluationCells_verticalIdentity {a b : A.A.Objects} (p : Quiver.Path a b) :
    (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.verticalIdentity p)) =
      CellGraph.pack ((operations A).verticalIdentity (evalPath A p)) := by
  let q := A.A.freeObject.generatorArrow p
  have h := evaluationCells_multiplication A
    (CellGraph.pack ((BundledAlgebra.forget.obj A.A.freeObject).freeAlgebra.verticalIdentity q))
  erw [(BundledAlgebra.evaluation A.A.freeObject).verticalIdentity,
    (BundledAlgebra.free.map A.a).verticalIdentity] at h
  have he : (BundledAlgebra.evaluation A.A.freeObject).base.vertical.map q = p :=
    A.A.freeObject.evaluation_generator p
  erw [he] at h
  have hf := congrArg (fun e : FinPath.Edge (Paths A.A.Objects) =>
    CellGraph.pack (A.A.freeAlgebra.verticalIdentity e.2.2)) (free_action_single A p)
  exact h.trans ((congrArg (evaluationCells A).total hf).trans
    (operations_verticalIdentity A (evalPath A p)).symm)

end Kernel.Augmented.GeneratingMonadAlgebra

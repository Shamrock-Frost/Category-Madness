import Kernel.Augmented.GeneratingComparisonCells

/-! Evaluation-compatible graph maps preserve both augmented identity cells.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating
variable {A B : BundledAlgebra.{w}}
  (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F)

theorem comparisonCells_horizontalIdentity {a b : A.Obj} (j : A.horizontal a b) :
    (comparisonCells F hF).total (CellGraph.pack (A.algebra.horizontalIdentity j)) =
      CellGraph.pack (B.algebra.horizontalIdentity ((comparisonBase F hF).horizontal j)) := by
  let j' : (forget.obj A).freeHorizontal a b := ⟨⟨a, b, j⟩, rfl, rfl⟩
  have he := (evaluation A).horizontalIdentity j'
  have hi := (Graph.lift F).horizontalIdentity j'
  have hp := comparisonCells_evaluation F hF
    (CellGraph.pack ((forget.obj A).freeAlgebra.horizontalIdentity j'))
  erw [he] at hp
  exact hp.trans hi

theorem comparisonCells_verticalIdentity {a b : A.Obj} (f : a ⟶ b) :
    (comparisonCells F hF).total (CellGraph.pack (A.algebra.verticalIdentity f)) =
      CellGraph.pack (B.algebra.verticalIdentity ((comparisonBase F hF).vertical.map f)) := by
  let p := (Paths.of (forget.obj A).Objects).map (A.arrowGenerators.map f)
  have he := (evaluation A).verticalIdentity p
  have hi := (Graph.lift F).verticalIdentity p
  have hp := comparisonCells_evaluation F hF
    (CellGraph.pack ((forget.obj A).freeAlgebra.verticalIdentity p))
  erw [he, evaluation_generator] at hp
  have hf := graphVertical_evaluation F hF p
  erw [evaluation_generator] at hf
  exact hp.trans (hi.trans (congrArg (fun f => CellGraph.pack (B.algebra.verticalIdentity f)) hf.symm))

end Kernel.Augmented.BundledAlgebra

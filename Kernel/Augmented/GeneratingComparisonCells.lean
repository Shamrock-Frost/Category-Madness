import Kernel.Augmented.GeneratingComparisonBase

/-! Recover the complete-boundary cell map from evaluation compatibility.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating

def graphTotal {A B : BundledAlgebra.{w}} (F : forget.obj A ⟶ forget.obj B)
    (x : A.cells.Total) : B.cells.Total := (Graph.mapCell F x.arityCell).val

theorem graphTotal_arityCell {A B : BundledAlgebra.{w}} (F : forget.obj A ⟶ forget.obj B)
    {n ε} (x : A.cells.ArityCell n ε) : graphTotal F x.val = (Graph.mapCell F x).val := by
  have hn : x.val.1.2.2.input.length = n := x.input_length
  have he : x.val.outputFlag = ε := by
    unfold CellGraph.Total.outputFlag
    have h := x.output_length
    change x.val.1.2.2.output.val.length = ε.toNat at h
    cases ε <;> simp_all
  rcases x with ⟨x, hx⟩
  dsimp at hn he
  subst n
  subst ε
  rfl

theorem evaluation_cell_generator (A : BundledAlgebra.{w}) {n ε}
    (x : (forget.obj A).Cell n ε) :
    (evaluation A).total (CellGraph.pack ((forget.obj A).freeCell x)) = x.val :=
  Graph.lift_generator (𝟙 (forget.obj A)) x

def comparisonCells {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) : A.cells.OverMap B.cells where
  base := comparisonBase F hF
  total := graphTotal F
  boundary x := by
    have hi := (Graph.lift F).boundary (CellGraph.pack ((forget.obj A).freeCell x.arityCell))
    have he := (evaluation A).boundary (CellGraph.pack ((forget.obj A).freeCell x.arityCell))
    erw [Graph.lift_generator] at hi
    erw [evaluation_cell_generator] at he
    change (graphTotal F x).1 = _ at hi
    rw [lift_base_factorization F hF] at hi
    erw [BaseMap.comp_frame] at hi
    exact hi.trans (congrArg (comparisonBase F hF).frame he.symm)

theorem comparisonCells_graphMap {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) :
    (comparisonCells F hF).graphMap = F := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s⟩
  cases s with
  | point => rfl
  | vertical =>
    ext x
    rcases x with ⟨a, b, f⟩
    exact graphVertical_pack F f
  | horizontal =>
    ext x
    rcases x with ⟨a, b, j⟩
    exact graphHorizontal_pack F j
  | cell n ε =>
    ext x
    apply Subtype.ext
    exact ((comparisonCells F hF).arityCell_val x).trans (graphTotal_arityCell F x)

theorem comparisonCells_evaluation {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F)
    (x : (forget.obj A).freeObject.cells.Total) :
    (comparisonCells F hF).total ((evaluation A).total x) = (Graph.lift F).total x := by
  have h := congrArg (fun f : forget.obj ((forget.obj A).freeObject) ⟶ forget.obj B =>
    (Graph.mapCell f x.arityCell).val) hF
  change ((Graph.lift F).toOverMap.arityCell x.arityCell).val =
    (Graph.mapCell F ((evaluation A).toOverMap.arityCell x.arityCell)).val at h
  erw [CellGraph.OverMap.arityCell_val] at h
  rw [← graphTotal_arityCell] at h
  erw [CellGraph.OverMap.arityCell_val] at h
  exact h.symm

theorem comparisonCells_factorization {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) :
    (Graph.lift F).toOverMap = (evaluation A).toOverMap.comp (comparisonCells F hF) :=
  CellGraph.OverMap.ext _ _ (lift_base_factorization F hF)
    (funext (fun x => (comparisonCells_evaluation F hF x).symm))

end Kernel.Augmented.BundledAlgebra

import Kernel.Augmented.GeneratingSectionRows
import Kernel.Augmented.SubstitutionCongruence

/-! Lift complete substitution inputs through global free evaluation.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating
variable (A : BundledAlgebra.{w})

def generatorArrow {a b : A.Obj} (f : a ⟶ b) :=
  (Paths.of (forget.obj A).Objects).map (A.arrowGenerators.map f)

def generatorOuter {f g : Side A.Obj} (r : A.cells.NonemptyRow f g) {a b : A.Obj}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.horizontal a b)
    (ψ : A.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    (forget.obj A).freeObject.cells.Cell (CellGraph.Row.outerBoundary (A.generatorNonemptyRow r)
      (A.generatorArrow h) (A.generatorArrow k) (A.generatorShortPath L)) :=
  CellGraph.castInput (A.generatorRow_output r.val).symm (A.generatorCell ψ)

theorem generatorOuter_evaluation {f g : Side A.Obj} (r : A.cells.NonemptyRow f g) {a b : A.Obj}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.horizontal a b)
    (ψ : A.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    (evaluation A).total (CellGraph.pack (A.generatorOuter r h k L ψ)) = CellGraph.pack ψ := by
  unfold generatorOuter
  erw [CellGraph.pack_castInput, generatorCell_evaluation]

private theorem packedRow_heq
    {x y : Σ f : Side A.Obj, Σ g : Side A.Obj, A.cells.Row f g} (e : x = y) : HEq x.2.2 y.2.2 := by
  cases e; rfl

/-- Any target substitution image is recovered from the chosen free representatives. -/
theorem generatorInputs_evaluation {B : BundledAlgebra.{w}} (F : A.cells.OverMap B.cells)
    (O : Operations B.cells) {f g : Side A.Obj} (r : A.cells.NonemptyRow f g) {a b : A.Obj}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.horizontal a b)
    (ψ : A.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    F.substituteImage O ((evaluation A).toOverMap.nonemptyRow (A.generatorNonemptyRow r))
      ((evaluation A).base.vertical.map (A.generatorArrow h))
      ((evaluation A).base.vertical.map (A.generatorArrow k))
      ((evaluation A).base.shortPath (A.generatorShortPath L))
      ((evaluation A).toOverMap.outerCell (A.generatorNonemptyRow r)
        (A.generatorArrow h) (A.generatorArrow k) (A.generatorShortPath L) (A.generatorOuter r h k L ψ)) =
      F.substituteImage O r h k L ψ := by
  apply F.substituteImage_congr O (A.generatorSide_evaluation f) (A.generatorSide_evaluation g)
    (packedRow_heq A (A.generatorRow_evaluation r.val))
    (heq_of_eq (A.evaluation_generator h)) (heq_of_eq (A.evaluation_generator k))
    (A.generatorShortPath_evaluation L)
  apply CellGraph.Total.cell_heq
    (x := CellGraph.pack ((evaluation A).toOverMap.outerCell (A.generatorNonemptyRow r)
      (A.generatorArrow h) (A.generatorArrow k) (A.generatorShortPath L) (A.generatorOuter r h k L ψ)))
    (y := CellGraph.pack ψ)
  erw [CellGraph.OverMap.pack_outerCell, generatorOuter_evaluation]

end Kernel.Augmented.BundledAlgebra

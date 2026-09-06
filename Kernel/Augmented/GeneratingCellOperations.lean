import Kernel.Augmented.GeneratingCellSection

/-! Primitive augmented operations reconstructed from the monad action.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.

This supplies operation data and evaluation formulas. The augmented equation families
must still be transferred before these data can be bundled as an algebra.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

def generatorOuter {f g : Side (Vertical A)} (r : (cells A).NonemptyRow f g)
    {a b : Vertical A} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath (horizontal A) a b)
    (ψ : (cells A).Cell (CellGraph.Row.outerBoundary r h k L)) :
    A.A.freeObject.cells.Cell (CellGraph.Row.outerBoundary (generatorNonemptyRow A r) h.toPath k.toPath L) :=
  CellGraph.castInput (generatorRow_output A r.val).symm (generatorCell A ψ)

theorem generatorOuter_evaluation {f g : Side (Vertical A)} (r : (cells A).NonemptyRow f g)
    {a b : Vertical A} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath (horizontal A) a b)
    (ψ : (cells A).Cell (CellGraph.Row.outerBoundary r h k L)) :
    (evaluationCells A).total (CellGraph.pack (generatorOuter A r h k L ψ)) = CellGraph.pack ψ := by
  unfold generatorOuter
  erw [CellGraph.pack_castInput, generatorCell_evaluation]

theorem generatorPost_evaluation (f : Side (Vertical A)) {a : Vertical A} (h : f.target ⟶ a) :
    (evaluationBase A).side ((generatorSide A f).post h.toPath) = f.post h := rfl

theorem generatorComposite_evaluation {f g : Side (Vertical A)} (r : (cells A).NonemptyRow f g)
    {a b : Vertical A} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath (horizontal A) a b) :
    ((evaluationBase A).boundary
      (CellGraph.Row.compositeBoundary (generatorNonemptyRow A r) h.toPath k.toPath L)).frame =
      (CellGraph.Row.compositeBoundary r h k L).frame :=
  Boundary.frame_eq (generatorPost_evaluation A f h) (generatorPost_evaluation A g k)
    (heq_of_eq ((evaluationBase_path A _).trans (generatorRow_input A r.val)))
    (heq_of_eq (evaluationBase_shortPath A L))

private theorem verticalIdentity_boundary {a b : Vertical A} (f : a ⟶ b) :
    ((evaluationBase A).boundary (Boundary.vertical f.toPath f.toPath)).frame =
      (Boundary.vertical f f).frame :=
  Boundary.frame_eq (generatorSide_evaluation A ⟨a, b, f⟩)
    (generatorSide_evaluation A ⟨a, b, f⟩) (HEq.refl _) (HEq.refl _)

/-- Both identity constructors and arbitrary nonempty-row substitution, with full incidence. -/
def operations : Operations (cells A) where
  horizontalIdentity j := CellGraph.transport ((evaluationBase A).horizontalIdentity_boundary j).symm
    ((evaluationCells A).cell (A.A.freeAlgebra.horizontalIdentity j))
  verticalIdentity f := CellGraph.transport (verticalIdentity_boundary A f)
    ((evaluationCells A).cell (A.A.freeAlgebra.verticalIdentity f.toPath))
  substitute := by
    intro f g r a b h k L ψ
    exact CellGraph.transport (generatorComposite_evaluation A r h k L)
      ((evaluationCells A).cell (A.A.freeAlgebra.substitute (generatorNonemptyRow A r)
        h.toPath k.toPath L (generatorOuter A r h k L ψ)))

theorem operations_horizontalIdentity {a b : Vertical A} (j : horizontal A a b) :
    CellGraph.pack ((operations A).horizontalIdentity j) =
      (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.horizontalIdentity j)) := by
  exact (CellGraph.pack_transport ((evaluationBase A).horizontalIdentity_boundary j).symm
    ((evaluationCells A).cell (A.A.freeAlgebra.horizontalIdentity j))).trans
      ((evaluationCells A).pack_cell _)

theorem operations_verticalIdentity {a b : Vertical A} (f : a ⟶ b) :
    CellGraph.pack ((operations A).verticalIdentity f) =
      (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.verticalIdentity f.toPath)) := by
  exact (CellGraph.pack_transport (verticalIdentity_boundary A f)
    ((evaluationCells A).cell (A.A.freeAlgebra.verticalIdentity f.toPath))).trans
      ((evaluationCells A).pack_cell _)

theorem operations_substitute {f g : Side (Vertical A)} (r : (cells A).NonemptyRow f g)
    {a b : Vertical A} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath (horizontal A) a b)
    (ψ : (cells A).Cell (CellGraph.Row.outerBoundary r h k L)) :
    CellGraph.pack ((operations A).substitute r h k L ψ) =
      (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.substitute (generatorNonemptyRow A r)
        h.toPath k.toPath L (generatorOuter A r h k L ψ))) := by
  exact (CellGraph.pack_transport (generatorComposite_evaluation A r h k L)
    ((evaluationCells A).cell (A.A.freeAlgebra.substitute (generatorNonemptyRow A r)
      h.toPath k.toPath L (generatorOuter A r h k L ψ)))).trans
        ((evaluationCells A).pack_cell _)

end Kernel.Augmented.GeneratingMonadAlgebra

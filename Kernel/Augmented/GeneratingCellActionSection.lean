import Kernel.Augmented.GeneratingCellMultiplication

/-! Compare free images of incident representatives with representatives of evaluated cells.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

theorem free_action_generatorCell {f g : Side A.A.freeObject.Obj}
    {b : Boundary A.A.freeHorizontal f g} (φ : A.A.freeObject.cells.Cell b) :
    (BundledAlgebra.free.map A.a).total (CellGraph.pack (A.A.freeObject.generatorCell φ)) =
      CellGraph.pack (generatorCell A ((evaluationCells A).cell φ)) := by
  unfold BundledAlgebra.generatorCell
  erw [CellGraph.pack_transport, free_action_cell]
  have h := congrArg (fun x : (cells A).Total => CellGraph.pack (generatorCell A x.2))
    ((evaluationCells A).pack_cell φ)
  exact (pack_generatorCell A _).symm.trans h.symm

theorem free_action_generatorSide (f : Side A.A.freeObject.Obj) :
    (BundledAlgebra.free.map A.a).base.side (A.A.freeObject.generatorSide f) =
      generatorSide A ((evaluationBase A).side f) := by
  apply Side.edge_injective
  exact free_action_single A f.arrow

theorem free_action_generatorHorizontal {a b : A.A.Objects} (j : A.A.freeHorizontal a b) :
    (⟨Graph.mapObject A.a a, Graph.mapObject A.a b,
      (BundledAlgebra.free.map A.a).base.horizontal (A.A.freeObject.generatorHorizontal.map j)⟩ :
        FinPath.Edge (Kernel.Augmented.Horizontal A.A.freeHorizontal)) = ⟨a, b, j⟩ := by
  have h := BundledAlgebra.freeForgetAdjunction.unit.naturality A.a
  erw [BundledAlgebra.freeForgetAdjunction_unit,
    BundledAlgebra.freeForgetAdjunction_unit] at h
  have he := congrArg (fun F : BundledAlgebra.forget.obj A.A.freeObject ⟶
    BundledAlgebra.forget.obj A.A.freeObject => Graph.mapHorizontal F ⟨a, b, j⟩) h
  change A.A.unitHorizontal (Graph.mapHorizontal A.a ⟨a, b, j⟩) = _ at he
  erw [action_horizontal] at he
  exact he.symm.trans (A.A.horizontalPack_fiber j).symm

theorem free_action_generatorPath {a b : A.A.Objects} (p : HPath A.A.freeHorizontal a b) :
    HEq ((BundledAlgebra.free.map A.a).base.path (A.A.freeObject.generatorPath p)) p := by
  apply FinPath.path_heq (C := Kernel.Augmented.Horizontal A.A.freeHorizontal) _ _
    (action_object A a) (action_object A b)
    (((BundledAlgebra.free.map A.a).base.path_length _).trans
      (FinPath.map_length A.A.freeObject.generatorHorizontal p))
  intro i hi
  erw [FinPath.edgeAt_map, FinPath.edgeAt_map]
  generalize FinPath.edgeAt p i _ = e
  rcases e with ⟨a, b, j⟩
  exact free_action_generatorHorizontal A j
  all_goals simpa only [BaseMap.path_length, FinPath.map_length] using hi

theorem free_action_generatorShortPath {a b : A.A.Objects} (p : ShortPath A.A.freeHorizontal a b) :
    HEq ((BundledAlgebra.free.map A.a).base.shortPath (A.A.freeObject.generatorShortPath p)) p := by
  have h := free_action_generatorPath A p.val
  have ha := action_object A a
  have hb := action_object A b
  have aux : ∀ {a b a' b' : A.A.Objects} (p : ShortPath A.A.freeHorizontal a b)
      (q : ShortPath A.A.freeHorizontal a' b'), a = a' → b = b' → HEq p.val q.val → HEq p q := by
    intro a b a' b' p q ha hb hp
    cases ha; cases hb
    exact heq_of_eq (Subtype.ext (eq_of_heq hp))
  exact aux _ _ ha hb h

theorem free_action_generatorBoundary {f g : Side A.A.freeObject.Obj}
    (b : Boundary A.A.freeHorizontal f g) :
    ((BundledAlgebra.free.map A.a).base.boundary (A.A.freeObject.generatorBoundary b)).frame =
      (generatorBoundary A ((evaluationBase A).boundary b)).frame := by
  apply Boundary.frame_eq (free_action_generatorSide A f) (free_action_generatorSide A g)
  · exact (free_action_generatorPath A b.input).trans (heq_of_eq (evaluationBase_path A b.input)).symm
  · exact (free_action_generatorShortPath A b.output).trans
      (heq_of_eq (evaluationBase_shortPath A b.output)).symm

/-- Mapping a whole free representative row agrees with representing its evaluation. -/
theorem free_action_generatorRow {f g : Side A.A.freeObject.Obj} (r : A.A.freeObject.cells.Row f g) :
    HEq ((BundledAlgebra.free.map A.a).toOverMap.row (A.A.freeObject.generatorRow r))
      (generatorRow A ((evaluationCells A).row r)) := by
  induction r with
  | nil => exact CellGraph.Row.nil_heq (free_action_generatorSide A f)
  | @cons g k r e ih =>
    apply CellGraph.Row.cons_heq (free_action_generatorSide A f) (free_action_generatorSide A g)
      (free_action_generatorSide A k) ih (Boundary.heq_of_frame_eq (free_action_generatorBoundary A e.1))
    exact CellGraph.Total.cell_heq (((BundledAlgebra.free.map A.a).toOverMap.pack_cell _).trans
      (free_action_generatorCell A e.2))

end Kernel.Augmented.GeneratingMonadAlgebra

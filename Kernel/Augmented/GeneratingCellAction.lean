import Kernel.Augmented.GeneratingPathAction
import Kernel.Augmented.GeneratingComparisonCells

/-! Reconstruct incident cells and evaluate free cells using an arbitrary monad action.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

/-- The generating cells at their exact boundaries over the reconstructed base. -/
def cells : CellGraph (Vertical A) (horizontal A) := A.A.cellGraph

private theorem action_side {n ε} (x : A.A.freeObject.cells.ArityCell n ε) (s : Bool) :
    A.A.side (Graph.mapCell A.a x) s =
      (evaluationBase A).side (if s then x.right else x.left) := by
  apply Side.edge_injective
  have h := A.A.verticalPack_fiber (A.A.side (Graph.mapCell A.a x) s).arrow
  have hn := congrArg A.A.verticalPack (Graph.map_cellVertical A.a s x)
  cases s
  · exact h.trans (hn.trans (A.A.verticalPack_fiber (evalPath A x.left.arrow)).symm)
  · exact h.trans (hn.trans (A.A.verticalPack_fiber (evalPath A x.right.arrow)).symm)

private theorem action_horizontalPack
    (e : FinPath.Edge (Kernel.Augmented.Horizontal A.A.freeHorizontal)) :
    A.A.horizontalPack (Graph.mapHorizontal A.a e) =
      FinPath.mapEdge (evaluationBase A).horizontalPrefunctor e := by
  rcases e with ⟨a, b, j⟩
  erw [action_horizontal]
  exact (A.A.horizontalPack_fiber j).symm

private theorem action_input_edge {n ε} (x : A.A.freeObject.cells.ArityCell n ε) (i : Fin n) :
    FinPath.edgeAt (A.A.boundary (Graph.mapCell A.a x)).input i.val
      (by erw [FinPath.length_ofEdges]; exact i.isLt) =
    FinPath.edgeAt ((evaluationBase A).path x.boundary.input) i.val
      (by erw [BaseMap.path_length, x.input_length]; exact i.isLt) := by
  erw [FinPath.edgeAt_ofEdges]
  erw [A.A.horizontalPack_fiber]
  change A.A.horizontalPack (A.A.cellHorizontal (.inl i) (Graph.mapCell A.a x)) = _
  exact (congrArg A.A.horizontalPack (Graph.map_cellHorizontal A.a (.inl i) x)).trans
    ((action_horizontalPack A (x.horizontal (.inl i))).trans
      (FinPath.edgeAt_map (evaluationBase A).horizontalPrefunctor x.boundary.input i.val _).symm)

private theorem action_output_edge {n ε} (x : A.A.freeObject.cells.ArityCell n ε) (i : Fin ε.toNat) :
    FinPath.edgeAt (A.A.boundary (Graph.mapCell A.a x)).output.val i.val
      (by erw [FinPath.length_ofEdges]; exact i.isLt) =
    FinPath.edgeAt ((evaluationBase A).shortPath x.boundary.output).val i.val
      (by erw [BaseMap.path_length, x.output_length]; exact i.isLt) := by
  erw [FinPath.edgeAt_ofEdges]
  erw [A.A.horizontalPack_fiber]
  change A.A.horizontalPack (A.A.cellHorizontal (.inr i) (Graph.mapCell A.a x)) = _
  exact (congrArg A.A.horizontalPack (Graph.map_cellHorizontal A.a (.inr i) x)).trans
    ((action_horizontalPack A (x.horizontal (.inr i))).trans
      (FinPath.edgeAt_map (evaluationBase A).horizontalPrefunctor x.boundary.output.val i.val _).symm)

private theorem shortPath_heq {C : Type w} {H : C → C → Type w} {a b a' b' : C}
    (p : ShortPath H a b) (q : ShortPath H a' b') (ha : a = a') (hb : b = b')
    (hp : HEq p.val q.val) : HEq p q := by
  cases ha; cases hb
  exact heq_of_eq (Subtype.ext (eq_of_heq hp))

/-- The graph action preserves the complete boundary under reconstructed base evaluation. -/
theorem action_boundary {n ε} (x : A.A.freeObject.cells.ArityCell n ε) :
    (A.A.boundary (Graph.mapCell A.a x)).frame = (evaluationBase A).frame x.boundary.frame := by
  have hf := action_side A x false
  have hg := action_side A x true
  apply Boundary.frame_eq hf hg
  · apply FinPath.path_heq (C := Kernel.Augmented.Horizontal (horizontal A)) _ _
      (congrArg (fun f : Side (Vertical A) => f.source) hf)
      (congrArg (fun f : Side (Vertical A) => f.source) hg)
      ((FinPath.length_ofEdges _ _ _).trans ((evaluationBase A).path_length x.boundary.input |>.trans x.input_length).symm)
    intro i hi
    exact action_input_edge A x ⟨i, by erw [FinPath.length_ofEdges] at hi; exact hi⟩
  · apply shortPath_heq _ _
      (congrArg (fun f : Side (Vertical A) => f.target) hf)
      (congrArg (fun f : Side (Vertical A) => f.target) hg)
    apply FinPath.path_heq (C := Kernel.Augmented.Horizontal (horizontal A)) _ _
      (congrArg (fun f : Side (Vertical A) => f.target) hf)
      (congrArg (fun f : Side (Vertical A) => f.target) hg)
      ((FinPath.length_ofEdges _ _ _).trans ((evaluationBase A).path_length x.boundary.output.val |>.trans x.output_length).symm)
    intro i hi
    exact action_output_edge A x ⟨i, by erw [FinPath.length_ofEdges] at hi; exact hi⟩

/-- Free-cell evaluation as a full-boundary cell map over the recovered base functor. -/
def evaluationCells : A.A.freeObject.cells.OverMap (cells A) where
  base := evaluationBase A
  total x := CellGraph.pack (G := cells A) (A.A.generator (Graph.mapCell A.a x.arityCell))
  boundary x := action_boundary A x.arityCell

theorem evaluationCells_arityCell {n ε} (x : A.A.freeObject.cells.ArityCell n ε) :
    (evaluationCells A).total x.val =
      CellGraph.pack (G := cells A) (A.A.generator (Graph.mapCell A.a x)) := by
  have hn : x.val.1.2.2.input.length = n := x.input_length
  have he : x.val.outputFlag = ε := by
    unfold CellGraph.Total.outputFlag
    have h := x.output_length
    change x.val.1.2.2.output.val.length = ε.toNat at h
    cases ε <;> simp_all
  rcases x with ⟨x, hx⟩
  dsimp at hn he
  subst n; subst ε; rfl

/-- Each original cell generator is recovered exactly, with its boundary still attached. -/
theorem evaluationCells_generator {n ε} (x : A.A.Cell n ε) :
    (evaluationCells A).total (CellGraph.pack (A.A.freeCell x)) =
      CellGraph.pack (G := cells A) (A.A.generator x) := by
  have h := A.unit
  change BundledAlgebra.freeForgetAdjunction.unit.app A.A ≫ A.a = 𝟙 A.A at h
  rw [BundledAlgebra.freeForgetAdjunction_unit] at h
  have hx := congrArg (fun F : A.A ⟶ A.A => Graph.mapCell F x) h
  have he := evaluationCells_arityCell A (A.A.unitCell x)
  exact he.trans (congrArg (fun x => CellGraph.pack (G := cells A) (A.A.generator x)) hx)

end Kernel.Augmented.GeneratingMonadAlgebra

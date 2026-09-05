import Kernel.Augmented.GeneratingBoundaryMaps
import Kernel.Augmented.GlobalMapFromPullback

/-! The free augmented algebra as an object and its generating-graph unit.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

noncomputable section

open CategoryTheory Opposite
namespace Kernel.Augmented.Generating.Graph
universe w
variable (G : Graph.{w})

noncomputable def freeObject : BundledAlgebra.{w} where
  Obj := Paths G.Objects
  vertical := inferInstance
  horizontal := G.freeHorizontal
  cells := CellTerm.quotientGraph G.freeCellGenerators
  algebra := G.freeAlgebra

def verticalPack (e : G.Vertical) : FinPath.Edge G.Objects :=
  ⟨G.verticalEndpoint false e, G.verticalEndpoint true e, ⟨e, rfl, rfl⟩⟩

def horizontalPack (e : G.Horizontal) : FinPath.Edge (Kernel.Augmented.Horizontal G.horizontal) :=
  ⟨G.horizontalEndpoint false e, G.horizontalEndpoint true e, ⟨e, rfl, rfl⟩⟩

theorem verticalPack_fiber {a b : G.Objects} (e : a ⟶ b) :
    (⟨a, b, e⟩ : FinPath.Edge G.Objects) = G.verticalPack e.val := by
  rcases e with ⟨e, ha, hb⟩
  cases ha; cases hb; rfl

theorem horizontalPack_fiber {a b : G.Objects} (e : G.horizontal a b) :
    (⟨a, b, e⟩ : FinPath.Edge (Kernel.Augmented.Horizontal G.horizontal)) = G.horizontalPack e.val := by
  rcases e with ⟨e, ha, hb⟩
  cases ha; cases hb; rfl

def unitVertical (e : G.Vertical) : G.freeObject.cells.underlyingGraph.Vertical :=
  FinPath.mapEdge (Paths.of G.Objects) (G.verticalPack e)

def unitHorizontal (e : G.Horizontal) : G.freeObject.cells.underlyingGraph.Horizontal := G.horizontalPack e

def unitCell {n ε} (x : G.Cell n ε) : G.freeObject.cells.ArityCell n ε :=
  ⟨CellGraph.pack (G.freeCell x), G.freeBoundary_arity x⟩

theorem unitCell_vertex {n ε} (x : G.Cell n ε) (i : Vertex n ε) :
    (G.unitCell x).vertex i = G.cellVertex i x := by
  cases i with
  | inl i => exact FinPath.vertexAt_ofEdges n (G.inputObjects x) (G.inputEdge x) i
  | inr i => exact FinPath.vertexAt_ofEdges ε.toNat (G.outputObjects x) (G.outputEdge x) i

theorem unitCell_vertical {n ε} (x : G.Cell n ε) (s : Bool) :
    (G.unitCell x).vertical s = G.unitVertical (G.cellVertical s x) := by
  have h := congrArg (FinPath.mapEdge (Paths.of G.Objects)) (G.verticalPack_fiber (G.side x s).arrow)
  cases s <;> exact h

theorem unitCell_horizontal {n ε} (x : G.Cell n ε) (i : HorizontalEdge n ε) :
    (G.unitCell x).horizontal i = G.unitHorizontal (G.cellHorizontal i x) := by
  cases i with
  | inl i =>
    exact (FinPath.edgeAt_ofEdges n (G.inputObjects x) (G.inputEdge x) i).trans
      (G.horizontalPack_fiber (G.inputEdge x i))
  | inr i =>
    exact (FinPath.edgeAt_ofEdges ε.toNat (G.outputObjects x) (G.outputEdge x) i).trans
      (G.horizontalPack_fiber (G.outputEdge x i))

def unitComponent : (s : Shape) → G.value s → G.freeObject.cells.underlyingGraph.value s
  | .point => fun a => a
  | .vertical => G.unitVertical
  | .horizontal => G.unitHorizontal
  | .cell _ _ => G.unitCell

def unit : G ⟶ BundledAlgebra.forget.obj G.freeObject where
  app s := ↾G.unitComponent s.unop
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    cases f with
    | id x => cases x <;> rfl
    | verticalEndpoint e => cases e <;> rfl
    | horizontalEndpoint e => cases e <;> rfl
    | cellVertex i => ext x; exact (G.unitCell_vertex x i).symm
    | cellVertical s => ext x; exact (G.unitCell_vertical x s).symm
    | cellHorizontal i => ext x; exact (G.unitCell_horizontal x i).symm

end Kernel.Augmented.Generating.Graph

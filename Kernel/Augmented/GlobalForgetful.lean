import Kernel.Augmented.UnderlyingGeneratingGraph

/-! The global forgetful functor to generating incidence graphs.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Opposite
namespace Kernel.Augmented
universe w
namespace CellGraph.OverMap
variable {C D E : Type w} [Category.{w} C] [Category.{w} D] [Category.{w} E]
  {H : C → C → Type w} {K : D → D → Type w} {L : E → E → Type w}
  {G : CellGraph.{w,w,w,w} C H} {G' : CellGraph.{w,w,w,w} D K} {G'' : CellGraph.{w,w,w,w} E L}

open Generating

def arityCell (F : OverMap G G') {n ε} (x : G.ArityCell n ε) : G'.ArityCell n ε :=
  ⟨pack (F.cell x.val.2), (Prod.ext (F.base.path_length x.val.1.2.2.input)
    (F.base.path_length x.val.1.2.2.output.val)).trans x.property⟩

theorem arityCell_val (F : OverMap G G') {n ε} (x : G.ArityCell n ε) :
    (F.arityCell x).val = F.total x.val := F.pack_cell x.val.2

theorem arityCell_vertex (F : OverMap G G') {n ε} (x : G.ArityCell n ε) (i : Generating.Vertex n ε) :
    (F.arityCell x).vertex i = F.base.vertical.obj (x.vertex i) := by
  cases i with
  | inl i => exact FinPath.vertexAt_map F.base.horizontalPrefunctor x.boundary.input i.val _
  | inr i => exact FinPath.vertexAt_map F.base.horizontalPrefunctor x.boundary.output.val i.val _

theorem arityCell_vertical (F : OverMap G G') {n ε} (x : G.ArityCell n ε) (s : Bool) :
    (F.arityCell x).vertical s = FinPath.mapEdge F.base.vertical.toPrefunctor (x.vertical s) := by
  cases s <;> rfl

theorem arityCell_horizontal (F : OverMap G G') {n ε} (x : G.ArityCell n ε) (i : HorizontalEdge n ε) :
    (F.arityCell x).horizontal i = FinPath.mapEdge F.base.horizontalPrefunctor (x.horizontal i) := by
  cases i with
  | inl i => exact FinPath.edgeAt_map F.base.horizontalPrefunctor x.boundary.input i.val _
  | inr i => exact FinPath.edgeAt_map F.base.horizontalPrefunctor x.boundary.output.val i.val _

def graphComponent (F : OverMap G G') : (s : Shape) → G.underlyingGraph.value s → G'.underlyingGraph.value s
  | .point => F.base.vertical.obj
  | .vertical => FinPath.mapEdge F.base.vertical.toPrefunctor
  | .horizontal => FinPath.mapEdge F.base.horizontalPrefunctor
  | .cell _ _ => F.arityCell

def graphMap (F : OverMap G G') : G.underlyingGraph ⟶ G'.underlyingGraph where
  app s := ↾F.graphComponent s.unop
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    cases f with
    | id x => cases x <;> rfl
    | verticalEndpoint e => cases e <;> rfl
    | horizontalEndpoint e => cases e <;> rfl
    | cellVertex i => ext x; exact (F.arityCell_vertex x i).symm
    | cellVertical s => ext x; exact (F.arityCell_vertical x s).symm
    | cellHorizontal i => ext x; exact (F.arityCell_horizontal x i).symm

theorem graphMap_id : (id G).graphMap = 𝟙 G.underlyingGraph := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s⟩
  cases s with
  | point => rfl
  | vertical => rfl
  | horizontal => rfl
  | cell n ε =>
    ext x
    apply Subtype.ext
    exact (id G).arityCell_val x

theorem graphMap_comp (F : OverMap G G') (I : OverMap G' G'') :
    (F.comp I).graphMap = F.graphMap ≫ I.graphMap := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s⟩
  cases s with
  | point => rfl
  | vertical => rfl
  | horizontal => rfl
  | cell n ε =>
    ext x
    apply Subtype.ext
    change ((F.comp I).arityCell x).val = (I.arityCell (F.arityCell x)).val
    erw [arityCell_val, arityCell_val, arityCell_val]
    rfl

end CellGraph.OverMap

namespace BundledAlgebra

def forget : BundledAlgebra.{w} ⥤ Generating.Graph.{w} where
  obj A := A.cells.underlyingGraph
  map F := F.toOverMap.graphMap
  map_id _A := CellGraph.OverMap.graphMap_id
  map_comp F I := CellGraph.OverMap.graphMap_comp F.toOverMap I.toOverMap

end BundledAlgebra
end Kernel.Augmented

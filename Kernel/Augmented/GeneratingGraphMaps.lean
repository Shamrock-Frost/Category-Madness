import Kernel.Augmented.GlobalForgetful
import Kernel.Augmented.FreeGeneratingUniversal

/-! The object and edge assignment induced by a generating graph morphism.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Opposite
namespace Kernel.Augmented.Generating
universe w
namespace Graph
variable {G G' : Graph.{w}}

def mapObject (F : G ⟶ G') : G.Object → G'.Object := F.app (op Shape.point)
def mapVertical (F : G ⟶ G') : G.Vertical → G'.Vertical := F.app (op Shape.vertical)
def mapHorizontal (F : G ⟶ G') : G.Horizontal → G'.Horizontal := F.app (op Shape.horizontal)
def mapCell (F : G ⟶ G') {n ε} : G.Cell n ε → G'.Cell n ε := F.app (op (Shape.cell n ε))

theorem map_verticalEndpoint (F : G ⟶ G') (e : Bool) (f : G.Vertical) :
    G'.verticalEndpoint e (mapVertical F f) = mapObject F (G.verticalEndpoint e f) :=
  (congrArg (fun k => k f) (F.naturality (Hom.verticalEndpoint e).op)).symm

theorem map_horizontalEndpoint (F : G ⟶ G') (e : Bool) (j : G.Horizontal) :
    G'.horizontalEndpoint e (mapHorizontal F j) = mapObject F (G.horizontalEndpoint e j) :=
  (congrArg (fun k => k j) (F.naturality (Hom.horizontalEndpoint e).op)).symm

theorem map_cellVertex (F : G ⟶ G') {n ε} (i : Vertex n ε) (x : G.Cell n ε) :
    G'.cellVertex i (mapCell F x) = mapObject F (G.cellVertex i x) :=
  (congrArg (fun k => k x) (F.naturality (Hom.cellVertex i).op)).symm

theorem map_cellVertical (F : G ⟶ G') {n ε} (s : Bool) (x : G.Cell n ε) :
    G'.cellVertical s (mapCell F x) = mapVertical F (G.cellVertical s x) :=
  (congrArg (fun k => k x) (F.naturality (Hom.cellVertical s).op)).symm

theorem map_cellHorizontal (F : G ⟶ G') {n ε} (i : HorizontalEdge n ε) (x : G.Cell n ε) :
    G'.cellHorizontal i (mapCell F x) = mapHorizontal F (G.cellHorizontal i x) :=
  (congrArg (fun k => k x) (F.naturality (Hom.cellHorizontal i).op)).symm

end Graph
namespace FinPath.Edge
variable {C : Type w} [Quiver.{w} C]

def reindex (e : FinPath.Edge C) {a b : C} (ha : e.1 = a) (hb : e.2.1 = b) : a ⟶ b :=
  cast (congrArg₂ (fun a b : C => a ⟶ b) ha hb) e.2.2

theorem pack_reindex (e : FinPath.Edge C) {a b : C} (ha : e.1 = a) (hb : e.2.1 = b) :
    (⟨a, b, reindex e ha hb⟩ : FinPath.Edge C) = e := by
  rcases e with ⟨x, y, e⟩
  cases ha; cases hb; rfl

end FinPath.Edge
namespace Graph
variable {G : Graph.{w}} {C : Type w} [Category.{w} C] {H : C → C → Type w}
  {Q : CellGraph.{w,w,w,w} C H}

/-- Read the object and generating-edge assignment from an incidence-natural graph map. -/
def skeleton (F : G ⟶ Q.underlyingGraph) : SkeletonAssignment G H where
  vertical :=
    { obj := mapObject F
      map := fun e => FinPath.Edge.reindex (mapVertical F e.val)
        ((map_verticalEndpoint F false e.val).trans (congrArg (mapObject F) e.property.1))
        ((map_verticalEndpoint F true e.val).trans (congrArg (mapObject F) e.property.2)) }
  horizontal := fun e => FinPath.Edge.reindex (C := Kernel.Augmented.Horizontal H) (mapHorizontal F e.val)
    ((map_horizontalEndpoint F false e.val).trans (congrArg (mapObject F) e.property.1))
    ((map_horizontalEndpoint F true e.val).trans (congrArg (mapObject F) e.property.2))

theorem skeleton_vertical (F : G ⟶ Q.underlyingGraph) {a b : G.Objects} (e : a ⟶ b) :
    (⟨mapObject F a, mapObject F b, (skeleton F).vertical.map e⟩ : FinPath.Edge C) = mapVertical F e.val :=
  FinPath.Edge.pack_reindex (mapVertical F e.val)
    ((map_verticalEndpoint F false e.val).trans (congrArg (mapObject F) e.property.1))
    ((map_verticalEndpoint F true e.val).trans (congrArg (mapObject F) e.property.2))

theorem skeleton_horizontal (F : G ⟶ Q.underlyingGraph) {a b : G.Objects} (e : G.horizontal a b) :
    (⟨mapObject F a, mapObject F b, (skeleton F).horizontal e⟩ : FinPath.Edge (Kernel.Augmented.Horizontal H)) = mapHorizontal F e.val :=
  FinPath.Edge.pack_reindex (mapHorizontal F e.val)
    ((map_horizontalEndpoint F false e.val).trans (congrArg (mapObject F) e.property.1))
    ((map_horizontalEndpoint F true e.val).trans (congrArg (mapObject F) e.property.2))

end Graph
end Kernel.Augmented.Generating

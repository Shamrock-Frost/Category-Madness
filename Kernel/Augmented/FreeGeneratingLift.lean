import Kernel.Augmented.FreeGeneratingUnit
import Kernel.Augmented.GlobalMapToPullback

/-! Extend a generating-graph map to a global augmented algebra map.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

noncomputable section
open CategoryTheory Opposite
namespace Kernel.Augmented.Generating.Graph
universe w
variable {G : Graph.{w}} {A : BundledAlgebra.{w}}

def lift (F : G ⟶ BundledAlgebra.forget.obj A) : G.freeObject ⟶ A :=
  Operations.Map.overMap (skeleton F).baseMap
    (freeMapEquiv G (skeleton F) A.algebra (cellAssignment F))

theorem lift_generator (F : G ⟶ BundledAlgebra.forget.obj A) {n ε} (x : G.Cell n ε) :
    (lift F).total (CellGraph.pack (G.freeCell x)) = (mapCell F x).val := by
  change CellGraph.pack (G := A.cells)
    (CellGraph.transport (G := A.cells) (mapped_boundary F x).symm (mapCell F x).val.2) = _
  exact CellGraph.pack_transport (G := A.cells) (mapped_boundary F x).symm _

/-- The extended map agrees with the given map on all generating sorts. -/
theorem unit_lift (F : G ⟶ BundledAlgebra.forget.obj A) :
    G.unit ≫ BundledAlgebra.forget.map (lift F) = F := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s⟩
  cases s with
  | point => rfl
  | vertical =>
    ext e
    change (⟨mapObject F _, mapObject F _, (skeleton F).baseMap.vertical.map
      ((Paths.of G.Objects).map (G.verticalPack e).2.2)⟩ : FinPath.Edge A.Obj) = mapVertical F e
    rw [SkeletonAssignment.baseMap_generator]
    exact skeleton_vertical F (G.verticalPack e).2.2
  | horizontal =>
    ext e
    exact skeleton_horizontal F (G.horizontalPack e).2.2
  | cell n ε =>
    ext x
    apply Subtype.ext
    change ((lift F).toOverMap.arityCell (G.unitCell x)).val = (mapCell F x).val
    rw [CellGraph.OverMap.arityCell_val]
    exact lift_generator F x

end Kernel.Augmented.Generating.Graph

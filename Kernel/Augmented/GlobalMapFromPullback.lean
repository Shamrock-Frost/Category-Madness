import Kernel.Augmented.GlobalAlgebras
import Kernel.Augmented.AlgebraMaps

/-! Turn a map into a pulled-back algebra into a global algebra map.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c u' v' h' c'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {H : C → C → Type h} {K : D → D → Type h'}
  {G : CellGraph.{u,v,h,c} C H} {G' : CellGraph.{u',v',h',c'} D K}

namespace CellGraph.OverMap

def ofFamily (B : BaseMap H K) (F : CellGraph.Map G (B.pullback G')) : OverMap G G' where
  base := B
  total x := ⟨B.frame x.1, F.cell x.2⟩
  boundary _ := rfl

theorem ofFamily_cell (B : BaseMap H K) (F : CellGraph.Map G (B.pullback G'))
    {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) :
    (ofFamily B F).cell φ = F.cell φ := rfl

theorem ofFamily_row (B : BaseMap H K) (F : CellGraph.Map G (B.pullback G'))
    {f g : Side C} (r : G.Row f g) : (ofFamily B F).row r = B.row (F.row r) := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg (fun r => r.cons ⟨B.boundary e.1, F.cell e.2⟩) ih

theorem substitute_boundary (F : OverMap G G') {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b) :
    (CellGraph.Row.compositeBoundary (F.nonemptyRow r) (F.base.vertical.map h) (F.base.vertical.map k)
      (F.base.shortPath L)).frame = F.base.frame (CellGraph.Row.compositeBoundary r h k L).frame :=
  Boundary.frame_eq (F.base.side_post f h).symm (F.base.side_post g k).symm
    (heq_of_eq (F.row_input r.val)) (HEq.refl _)

end CellGraph.OverMap
namespace BaseMap

theorem pullback_substitute_heq (B : BaseMap H K) (O : Operations G') {f g : Side C}
    (r : (B.pullback G').NonemptyRow f g) {a b : C}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : (B.pullback G').Cell (CellGraph.Row.outerBoundary r h k L)) :
    HEq ((B.pullbackOperations O).substitute r h k L ψ)
      (O.substitute (B.nonemptyRow r) (B.vertical.map h) (B.vertical.map k) (B.shortPath L)
        (CellGraph.castInput (B.row_output r.val).symm ψ)) :=
  CellGraph.transport_heq (G := G') (B.substitute_boundary r h k L) _

end BaseMap
namespace Operations.Map
variable {O : Operations G} {O' : Operations G'}

/-- The relative mapping property supplies actual global maps over its base functor. -/
def overMap (B : BaseMap H K) (F : O.Map (B.pullbackOperations O')) : O.OverMap O' where
  toOverMap := CellGraph.OverMap.ofFamily B F.toMap
  horizontalIdentity j := by
    change CellGraph.pack (G := G') (F.cell (O.horizontalIdentity j)) = _
    rw [F.horizontalIdentity]
    exact CellGraph.pack_transport (G := G') (B.horizontalIdentity_boundary j) _
  verticalIdentity f := by
    change CellGraph.pack (G := G') (F.cell (O.verticalIdentity f)) = _
    rw [F.verticalIdentity]
    rfl
  substitute := by
    intro f g r a b h k L ψ
    apply Sigma.ext ((CellGraph.OverMap.ofFamily B F.toMap).substitute_boundary r h k L).symm
    have e1 := (heq_of_eq (F.substitute r h k L ψ)).trans (CellGraph.castInput_heq _ _)
    have e2 := B.pullback_substitute_heq O' (F.toMap.nonemptyRow r) h k L
      (CellGraph.castInput (F.toMap.row_output r.val).symm (F.cell ψ))
    apply (e1.trans e2).trans
    apply O'.substitute_heq rfl rfl
      (heq_of_eq (CellGraph.OverMap.ofFamily_row B F.toMap r.val).symm)
      (HEq.refl _) (HEq.refl _) rfl
    apply (CellGraph.castInput_heq (G := G') _ _).trans
    apply (CellGraph.castInput_heq (G := B.pullback G') _ _).trans
    exact (CellGraph.castInput_heq (G := G') _ _).symm

end Operations.Map
end Kernel.Augmented

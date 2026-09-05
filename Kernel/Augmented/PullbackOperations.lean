import Kernel.Augmented.BaseMaps

/-! Change of base for the augmented operation data.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.BaseMap
universe u v h u' v' h' c
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {H : C → C → Type h} {K : D → D → Type h'}
  (F : BaseMap H K) {G : CellGraph.{u',v',h',c} D K}

theorem horizontalIdentity_boundary {a b : C} (j : H a b) :
    (Boundary.horizontalIdentity (F.horizontal j)).frame = (F.boundary (Boundary.horizontalIdentity j)).frame :=
  Boundary.frame_eq (F.side_identity a).symm (F.side_identity b).symm (HEq.refl _) (HEq.refl _)

theorem substitute_boundary {f g : Side C} (r : (F.pullback G).NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b) :
    (CellGraph.Row.compositeBoundary (F.nonemptyRow r) (F.vertical.map h) (F.vertical.map k) (F.shortPath L)).frame =
      (F.boundary (CellGraph.Row.compositeBoundary r h k L)).frame :=
  Boundary.frame_eq (F.side_post f h).symm (F.side_post g k).symm
    (heq_of_eq (F.row_input r.val)) (HEq.refl _)

def pullbackOperations (O : Operations G) : Operations (F.pullback G) where
  horizontalIdentity j := CellGraph.transport (G := G) (F.horizontalIdentity_boundary j) (O.horizontalIdentity (F.horizontal j))
  verticalIdentity f := O.verticalIdentity (F.vertical.map f)
  substitute := by
    intro f g r a b h k L ψ
    exact CellGraph.transport (G := G) (F.substitute_boundary r h k L)
      (O.substitute (F.nonemptyRow r) (F.vertical.map h) (F.vertical.map k) (F.shortPath L)
        (CellGraph.castInput (F.row_output r.val).symm ψ))

end Kernel.Augmented.BaseMap

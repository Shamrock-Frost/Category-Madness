import Kernel.Augmented.GlobalMapToPullback

/-! Reindex a global map along an equality of its complete base map.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Operations.OverMap
universe w
variable {C D : Type w} [Category.{w} C] [Category.{w} D]
  {H : C → C → Type w} {K : D → D → Type w}
  {G : CellGraph.{w,w,w,w} C H} {G' : CellGraph.{w,w,w,w} D K}
  {O : Operations G} {O' : Operations G'}

def changeBase (F : O.OverMap O') (B : BaseMap H K) (e : F.base = B) : O.OverMap O' where
  base := B
  total := F.total
  boundary x := (F.boundary x).trans (congrArg (fun B => B.frame x.1) e)
  horizontalIdentity := by intro a b j; cases e; exact F.horizontalIdentity j
  verticalIdentity := by intro a b f; cases e; exact F.verticalIdentity f
  substitute := by intro f g r a b h k L ψ; cases e; exact F.substitute r h k L ψ

theorem changeBase_eq (F : O.OverMap O') (B : BaseMap H K) (e : F.base = B) :
    F.changeBase B e = F :=
  Operations.OverMap.ext _ _ (CellGraph.OverMap.ext _ _ e.symm rfl)

end Kernel.Augmented.Operations.OverMap

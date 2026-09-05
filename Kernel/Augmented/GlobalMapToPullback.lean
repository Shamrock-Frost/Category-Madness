import Kernel.Augmented.GlobalMapFromPullback

/-! Read a global operation map as a map into the pulled-back target algebra.
This bridges the global category to the proved free-cell uniqueness theorem.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c c' u' v' h' d
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

private theorem map_apply_of_substitute {O : Operations G} {O' : Operations K}
    (F : CellGraph.Map G K)
    (hs : ∀ {f g : Side C} (r : G.NonemptyRow f g) {a b : C}
      (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
      (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)),
      HEq (F.cell (O.substitute r h k L ψ))
        (O'.substitute (F.nonemptyRow r) h k L (CellGraph.castInput (F.row_output r.val).symm (F.cell ψ))))
    (s : SubstitutionShape C H) (x : s.Inputs G) :
    F.cell (O.apply s x) = O'.apply s ⟨F.labels s.row x.1, F.cell x.2⟩ := by
  unfold Operations.apply
  erw [F.castInput]
  apply eq_of_heq
  apply (CellGraph.castInput_heq _ _).trans
  apply (hs _ _ _ _ _).trans
  apply HEq.trans _ (CellGraph.castInput_heq _ _).symm
  apply O'.substitute_heq rfl rfl (heq_of_eq (F.row_join s.row x.1))
    (HEq.refl _) (HEq.refl _) rfl
  apply (CellGraph.castInput_heq _ _).trans
  erw [F.castInput]
  exact (CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _).symm

private def mapOfPrimitive {O : Operations G} {O' : Operations K} (F : CellGraph.Map G K)
    (hh : ∀ {a b : C} (j : H a b), F.cell (O.horizontalIdentity j) = O'.horizontalIdentity j)
    (hv : ∀ {a b : C} (f : a ⟶ b), F.cell (O.verticalIdentity f) = O'.verticalIdentity f)
    (hs : ∀ {f g : Side C} (r : G.NonemptyRow f g) {a b : C}
      (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
      (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)),
      HEq (F.cell (O.substitute r h k L ψ))
        (O'.substitute (F.nonemptyRow r) h k L (CellGraph.castInput (F.row_output r.val).symm (F.cell ψ)))) :
    O.Map O' where
  toMap := F
  map_operation o x := by
    cases o with
    | horizontalIdentity j => exact hh j
    | verticalIdentity f => exact hv f.arrow
    | substitution s =>
      change F.cell (O.apply s _) = O'.apply s _
      erw [map_apply_of_substitute F hs]
      erw [RowShape.collect_map]
      rfl

variable {D : Type u'} [Category.{v'} D] {H' : D → D → Type h'}
  {G' : CellGraph.{u',v',h',d} D H'}

namespace CellGraph.OverMap

def toFamily (F : OverMap G G') : CellGraph.Map G (F.base.pullback G') := ⟨F.cell⟩

theorem toFamily_row (F : OverMap G G') {f g : Side C} (r : G.Row f g) :
    F.base.row (F.toFamily.row r) = F.row r := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg (fun r => r.cons ⟨F.base.boundary e.1, F.cell e.2⟩) ih

end CellGraph.OverMap
namespace Operations.OverMap
variable {O : Operations G} {O' : Operations G'}

def toPullback (F : O.OverMap O') : O.Map (F.base.pullbackOperations O') :=
  mapOfPrimitive F.toOverMap.toFamily
    (by
      intro a b j
      apply eq_of_heq
      have h := CellGraph.Total.cell_heq ((F.toOverMap.pack_cell (O.horizontalIdentity j)).trans (F.horizontalIdentity j))
      exact h.trans (CellGraph.transport_heq (G := G') (F.base.horizontalIdentity_boundary j) _).symm)
    (by
      intro a b f
      exact eq_of_heq (CellGraph.Total.cell_heq ((F.toOverMap.pack_cell (O.verticalIdentity f)).trans (F.verticalIdentity f))))
    (by
      intro f g r a b h k L ψ
      have e1 := CellGraph.Total.cell_heq ((F.toOverMap.pack_cell (O.substitute r h k L ψ)).trans (F.substitute r h k L ψ))
      have e2 := F.base.pullback_substitute_heq O' (F.toOverMap.toFamily.nonemptyRow r) h k L
        (CellGraph.castInput (F.toOverMap.toFamily.row_output r.val).symm (F.toOverMap.cell ψ))
      apply e1.trans
      apply HEq.trans _ e2.symm
      apply O'.substitute_heq rfl rfl (heq_of_eq (F.toOverMap.toFamily_row r.val).symm)
        (HEq.refl _) (HEq.refl _) rfl
      apply (CellGraph.castInput_heq (G := G') _ _).trans
      exact ((CellGraph.castInput_heq (G := G') _ _).trans
        (CellGraph.castInput_heq (G := F.base.pullback G') _ _)).symm)

end Operations.OverMap
end Kernel.Augmented

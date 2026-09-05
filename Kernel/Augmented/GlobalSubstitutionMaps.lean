import Kernel.Augmented.GlobalCellMaps

/-! Complete-boundary substitution images and their compatibility with map composition.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c u' v' h' c' u'' v'' h'' c''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {H : C → C → Type h} {K : D → D → Type h'} {L : E → E → Type h''}
  {G : CellGraph.{u,v,h,c} C H} {G' : CellGraph.{u',v',h',c'} D K}
  {G'' : CellGraph.{u'',v'',h'',c''} E L}

namespace CellGraph

theorem pack_castInput {f g : Side C} {p q : HPath H f.source g.source}
    {L : ShortPath H f.target g.target} (e : p = q) (φ : G.Cell (⟨p, L⟩ : Boundary H f g)) :
    pack (castInput (G := G) e φ) = pack φ := pack_transport _ φ

namespace OverMap

def outerCell (F : OverMap G G') {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (Row.outerBoundary r h k L)) :
    G'.Cell (Row.outerBoundary (F.nonemptyRow r) (F.base.vertical.map h) (F.base.vertical.map k) (F.base.shortPath L)) :=
  castInput (F.row_output r.val).symm (F.cell ψ)

theorem pack_outerCell (F : OverMap G G') {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (Row.outerBoundary r h k L)) :
    pack (F.outerCell r h k L ψ) = F.total (pack ψ) := by
  unfold outerCell
  erw [pack_castInput, F.pack_cell]

def substituteImage (F : OverMap G G') (O : Operations G') {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (Row.outerBoundary r h k L)) : G'.Total :=
  pack (O.substitute (F.nonemptyRow r) (F.base.vertical.map h) (F.base.vertical.map k)
    (F.base.shortPath L) (F.outerCell r h k L ψ))

private theorem pack_substitute_congr (O : Operations G) {f g : Side C}
    {r r' : G.NonemptyRow f g} {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b)
    {L L' : ShortPath H a b} {ψ : G.Cell (Row.outerBoundary r h k L)}
    {ψ' : G.Cell (Row.outerBoundary r' h k L')}
    (hr : r.val = r'.val) (hL : L = L') (hψ : HEq ψ ψ') :
    pack (O.substitute r h k L ψ) = pack (O.substitute r' h k L' ψ') := by
  cases Subtype.ext hr
  cases hL
  cases eq_of_heq hψ
  rfl

theorem comp_substituteImage (F : OverMap G G') (I : OverMap G' G'') (O : Operations G'')
    {f g : Side C} (r : G.NonemptyRow f g) {a b : C}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (Row.outerBoundary r h k L)) :
    (F.comp I).substituteImage O r h k L ψ =
      I.substituteImage O (F.nonemptyRow r) (F.base.vertical.map h) (F.base.vertical.map k)
        (F.base.shortPath L) (F.outerCell r h k L ψ) := by
  apply pack_substitute_congr O _ _ (F.comp_row I r.val) (BaseMap.comp_shortPath _ _ L)
  apply Total.cell_heq
    (x := pack (G := G'') ((F.comp I).outerCell r h k L ψ))
    (y := pack (G := G'') (I.outerCell (F.nonemptyRow r) (F.base.vertical.map h) (F.base.vertical.map k)
      (F.base.shortPath L) (F.outerCell r h k L ψ)))
  erw [pack_outerCell, pack_outerCell, pack_outerCell]
  rfl

theorem id_substituteImage (O : Operations G) {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (Row.outerBoundary r h k L)) :
    (id G).substituteImage O r h k L ψ = pack (O.substitute r h k L ψ) := by
  apply pack_substitute_congr O _ _ (id_row r.val) (BaseMap.id_shortPath L)
  exact Total.cell_heq ((id G).pack_outerCell r h k L ψ)

end OverMap
end CellGraph
end Kernel.Augmented

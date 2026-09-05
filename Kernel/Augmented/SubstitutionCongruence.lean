import Kernel.Augmented.GlobalSubstitutionMaps

/-! Substitution images depend only on the full incident input data.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellGraph.OverMap
universe w
variable {C D : Type w} [Category.{w} C] [Category.{w} D]
  {H : C → C → Type w} {K : D → D → Type w}
  {G : CellGraph.{w,w,w,w} C H} {Q : CellGraph.{w,w,w,w} D K}

theorem substituteImage_congr (F : G.OverMap Q) (O : Operations Q)
    {f g f' g' : Side C} {r : G.NonemptyRow f g} {r' : G.NonemptyRow f' g'}
    {a b : C} {h : f.target ⟶ a} {k : g.target ⟶ b}
    {h' : f'.target ⟶ a} {k' : g'.target ⟶ b} {L L' : ShortPath H a b}
    {ψ : G.Cell (Row.outerBoundary r h k L)} {ψ' : G.Cell (Row.outerBoundary r' h' k' L')}
    (hf : f = f') (hg : g = g') (hr : HEq r.val r'.val)
    (hh : HEq h h') (hk : HEq k k') (hL : L = L') (hψ : HEq ψ ψ') :
    F.substituteImage O r h k L ψ = F.substituteImage O r' h' k' L' ψ' := by
  cases hf; cases hg
  cases Subtype.ext (eq_of_heq hr)
  cases eq_of_heq hh; cases eq_of_heq hk
  cases hL; cases eq_of_heq hψ
  rfl

end Kernel.Augmented.CellGraph.OverMap

import Kernel.Augmented.Algebra

/-! Internal transport adapters for the Mathlib comparison.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

namespace Laws
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {O : Operations G} (laws : Laws O)
include laws

theorem leftUnit_heq {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) :
    HEq (O.leftUnitComposite φ) φ :=
  (CellGraph.transport_eq_iff_heq _ _ _).mp (laws.leftUnit φ)

theorem rightUnit_heq {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) :
    HEq (O.rightUnitComposite φ) φ :=
  (CellGraph.transport_eq_iff_heq _ _ _).mp (laws.rightUnit φ)

theorem insertion_heq {f g k : Side C} (p : G.Row f g) (q : G.Row g k)
    (hn : 0 < (p.comp q).length) {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b)
    (L : ShortPath H a b) (ψ : G.Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    HEq (O.insertedComposite p q hn h l L ψ) (O.substitute ⟨p.comp q, hn⟩ h l L ψ) :=
  (CellGraph.transport_eq_iff_heq _ _ _).mp (laws.insertion p q hn h l L ψ)

theorem assoc_heq {s t : Nested.Side C} (r : Nested.NonemptyRow G s t)
    {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath H a b)
    (χ : G.Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    HEq (O.assocLeft r p q L χ) (O.assocRight r p q L χ) :=
  (CellGraph.transport_eq_iff_heq _ _ _).mp (laws.assoc r p q L χ)

end Laws

namespace CellGraph.Row
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

theorem cons_heq {f g k f' g' k' : Side C}
    {r : G.Row f g} {r' : G.Row f' g'}
    {b : Boundary H g k} {b' : Boundary H g' k'} {φ : G.Cell b} {φ' : G.Cell b'}
    (hf : f = f') (hg : g = g') (hk : k = k')
    (hr : HEq r r') (hb : HEq b b') (hφ : HEq φ φ') :
    HEq (r.cons ⟨b, φ⟩) (r'.cons ⟨b', φ'⟩) := by
  cases hf; cases hg; cases hk
  cases eq_of_heq hr; cases eq_of_heq hb; cases eq_of_heq hφ
  rfl

theorem nil_heq {f g : Side C} (hfg : f = g) :
    HEq (.nil : G.Row f f) (.nil : G.Row g g) := by cases hfg; rfl

end CellGraph.Row

namespace Operations
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

theorem substitute_heq (O : Operations G) {f g f' g' : Side C}
    {r : G.NonemptyRow f g} {r' : G.NonemptyRow f' g'} {a b : C}
    {h : f.target ⟶ a} {k : g.target ⟶ b}
    {h' : f'.target ⟶ a} {k' : g'.target ⟶ b} {L L' : ShortPath H a b}
    {ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)}
    {ψ' : G.Cell (CellGraph.Row.outerBoundary r' h' k' L')}
    (hf : f = f') (hg : g = g') (hr : HEq r.val r'.val)
    (hh : HEq h h') (hk : HEq k k') (hL : L = L') (hψ : HEq ψ ψ') :
    HEq (O.substitute r h k L ψ) (O.substitute r' h' k' L' ψ') := by
  cases hf; cases hg
  cases Subtype.ext (eq_of_heq hr)
  cases eq_of_heq hh; cases eq_of_heq hk; cases hL
  cases eq_of_heq hψ
  rfl

end Operations

end Kernel.Augmented

import Kernel.Augmented.AlgebraMaps

/-! Lifting incident rows through a section of a map of cell families.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellGraph.Map
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}
  (F : Map G K) (S : Map K G)
  (hs : ∀ {f g : Side C} {b : Boundary H f g} (φ : K.Cell b), F.cell (S.cell φ) = φ)

include hs

theorem row_section {f g : Side C} (r : K.Row f g) : F.row (S.row r) = r := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (F.row (S.row r)).cons ⟨e.1, F.cell (S.cell e.2)⟩ = _
    rw [ih, hs]
    rfl

theorem nonemptyRow_section {f g : Side C} (r : K.NonemptyRow f g) :
    F.nonemptyRow (S.nonemptyRow r) = r := Subtype.ext (F.row_section S hs r.val)

omit hs in
private theorem step_ext {s t : Nested.Side C} (e e' : Nested.Step K s t)
    (hi : e.inner = e'.inner) (ho : e.output = e'.output) (hφ : HEq e.outer e'.outer) : e = e' := by
  cases e; cases e'; cases hi; cases ho; cases eq_of_heq hφ; rfl

theorem nestedStep_section {s t : Nested.Side C} (e : Nested.Step K s t) :
    F.nestedStep (S.nestedStep e) = e := by
  refine step_ext (F.nestedStep (S.nestedStep e)) e (F.nonemptyRow_section S hs e.inner) rfl ?_
  dsimp only [nestedStep]
  erw [F.castInput, hs]
  exact (CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _)

theorem nestedRow_section {s t : Nested.Side C} (r : Nested.Row K s t) :
    F.nestedRow (S.nestedRow r) = r := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (F.nestedRow (S.nestedRow r)).cons (F.nestedStep (S.nestedStep e)) = _
    rw [ih, F.nestedStep_section S hs]
    rfl

theorem nestedNonemptyRow_section {s t : Nested.Side C} (r : Nested.NonemptyRow K s t) :
    F.nestedNonemptyRow (S.nestedNonemptyRow r) = r := Subtype.ext (F.nestedRow_section S hs r.val)

end Kernel.Augmented.CellGraph.Map

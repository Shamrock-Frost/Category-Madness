import Kernel.Augmented.Vertical

/-! Elimination of arbitrary incidence rows over an empty horizontal graph.
This is a comparison of two already typed row presentations, not an augmented
arity or normalization claim for general horizontal graphs.
Cites: D-KR-18, D-RT-30, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.NoHorizontal
universe u v c
variable {C : Type u} [Category.{v} C]
  {G : CellGraph.{u,v,0,c} C (fun _ _ : C => Empty)}

structure RowView {f g : Side C} (r : G.Row f g) where
  source : C
  target : C
  left : source ⟶ target
  right : source ⟶ target
  row : Vertical.Row (G := G) left right
  left_eq : f = ⟨source, target, left⟩
  right_eq : g = ⟨source, target, right⟩
  embed_heq : HEq r row.embed

/-- Empty horizontal edges force every cell in a row to be a parallel 2-cell. -/
def rowView {f : Side C} : {g : Side C} → (r : G.Row f g) → RowView r
  | _, .nil =>
    ⟨f.source, f.target, f.arrow, f.arrow, .nil, rfl, rfl, HEq.refl _⟩
  | k, .cons r e => by
    rcases rowView r with ⟨a, b, f, g, p, hf, hg, hr⟩
    cases hf; cases hg
    rcases k with ⟨a', b', k⟩
    rcases e with ⟨⟨input, ⟨output, ho⟩⟩, φ⟩
    cases input with
    | cons _ edge => exact Empty.elim edge
    | nil =>
      cases output with
      | cons _ edge => exact Empty.elim edge
      | nil =>
        exact ⟨a, b, f, k, p.cons φ, rfl, rfl,
          CellGraph.Row.cons_heq rfl rfl rfl hr (HEq.refl _) (HEq.refl _)⟩

def embeddedView {a b : C} {f g : a ⟶ b} (p : Vertical.Row (G := G) f g) :
    RowView p.embed := ⟨a, b, f, g, p, rfl, rfl, HEq.refl _⟩

@[simp] theorem rowView_embed {a b : C} {f g : a ⟶ b}
    (p : Vertical.Row (G := G) f g) : rowView p.embed = embeddedView p := by
  induction p with
  | nil => rfl
  | cons p φ ih =>
    change rowView ((Vertical.Row.embed p).cons ⟨Boundary.vertical _ _, φ⟩) = _
    rw [rowView.eq_def]
    dsimp only
    erw [ih]
    rfl

theorem rowView_length {f g : Side C} (r : G.Row f g) :
    (rowView r).row.length = r.length := by
  rcases rowView r with ⟨a, b, f', g', p, hf, hg, hr⟩
  cases hf; cases hg
  have h := congrArg (Quiver.Path.length (V := G.Vertex)) (eq_of_heq hr)
  exact (Vertical.Row.embed_length p).symm.trans h.symm

end Kernel.Augmented.NoHorizontal

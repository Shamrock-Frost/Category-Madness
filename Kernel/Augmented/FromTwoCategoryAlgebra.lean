import Kernel.Augmented.FromTwoCategory
import Kernel.Augmented.NoHorizontalRows

/-! Augmented substitutions in a supplied strict 2-category.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Bicategory
namespace Kernel.Augmented.FromTwoCategory
universe u v w
variable {C : Type u} [Bicategory.{w,v} C] [Bicategory.Strict C]

def rowFold {a b : C} {f : a ⟶ b} :
    {g : a ⟶ b} → Vertical.Row (G := graph C) f g → Cell f g
  | _, .nil => identity f
  | _, .cons p φ => alongRow (rowFold p) φ

@[simp] theorem rowFold_nil {a b : C} (f : a ⟶ b) :
    rowFold (.nil : Vertical.Row (G := graph C) f f) = identity f := rfl

@[simp] theorem rowFold_cons {a b : C} {f g h : a ⟶ b}
    (p : Vertical.Row (G := graph C) f g) (φ : Cell g h) :
    rowFold (p.cons φ) = alongRow (rowFold p) φ := rfl

@[simp] theorem rowFold_single {a b : C} {f g : a ⟶ b} (φ : Cell f g) :
    rowFold ((.nil : Vertical.Row (G := graph C) f f).cons φ) = φ := identity_alongRow φ

theorem rowFold_comp {a b : C} {f g h : a ⟶ b}
    (p : Vertical.Row (G := graph C) f g) (q : Vertical.Row (G := graph C) g h) :
    rowFold (p.comp q) = alongRow (rowFold p) (rowFold q) := by
  induction q with
  | nil => exact (alongRow_identity _).symm
  | cons q φ ih =>
    change alongRow (rowFold (p.comp q)) φ = alongRow (rowFold p) (alongRow (rowFold q) φ)
    rw [ih, alongRow_assoc]

/-- First compose the incident row, then stack it with the outer cell. -/
def operations : Operations (graph C) where
  horizontalIdentity j := Empty.elim j
  verticalIdentity f := identity f
  substitute := by
    intro f g r d e h k L ψ
    rcases r with ⟨r, hr⟩
    rcases NoHorizontal.rowView r with ⟨a, b, f', g', p, hf, hg, he⟩
    cases hf; cases hg
    have er : r = p.embed := eq_of_heq he
    subst r
    rcases L with ⟨L, hL⟩
    cases L with
    | cons _ edge => exact Empty.elim edge
    | nil =>
      exact CellGraph.castInput (Vertical.Row.embed_input p).symm
        (stack (rowFold p) (CellGraph.castInput (Vertical.Row.embed_output p) ψ))

/-- The general incident operation computes the expected row fold on vertical rows. -/
theorem substitute_vertical {a b d : C} {f g : a ⟶ b}
    (p : Vertical.Row (G := graph C) f g) (hp : 0 < p.length)
    {h k : b ⟶ d} (β : Cell h k) :
    Vertical.substitute operations p hp β = stack (rowFold p) β := by
  unfold Vertical.substitute operations
  dsimp only
  erw [NoHorizontal.rowView_embed]
  simp only [NoHorizontal.embeddedView]
  dsimp only [ShortPath.empty]
  change CellGraph.castInput (G := graph C)
    (f := ⟨a, d, f ≫ h⟩) (g := ⟨a, d, g ≫ k⟩) (L := ShortPath.empty d)
    (Vertical.Row.embed_input p)
    (CellGraph.castInput (G := graph C)
      (f := ⟨a, d, f ≫ h⟩) (g := ⟨a, d, g ≫ k⟩) (L := ShortPath.empty d)
      (Vertical.Row.embed_input p).symm
      (stack (rowFold p) (CellGraph.castInput (G := graph C)
        (f := ⟨b, d, h⟩) (g := ⟨b, d, k⟩) (L := ShortPath.empty d)
        (Vertical.Row.embed_output p)
        (CellGraph.castInput (G := graph C)
          (f := ⟨b, d, h⟩) (g := ⟨b, d, k⟩) (L := ShortPath.empty d)
          (Vertical.Row.embed_output p).symm β)))) = stack (rowFold p) β
  erw [CellGraph.castInput_trans, CellGraph.castInput_trans]
  rfl

end Kernel.Augmented.FromTwoCategory

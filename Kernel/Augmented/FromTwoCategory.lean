import Kernel.Augmented.Rows
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-! The no-horizontal incidence model and its binary 2-cell compositions.
Reference: Koudenburg, arXiv:1910.11189v4, Example 1.5.
Cites: D-KR-18, D-RT-30, AT-FD-7.

This constructs the cell model for a bicategory; strictness gives strict
associativity and units after endpoint transport. Extending this supplied binary
model to the full augmented substitution algebra and proving the discrete nerve
comparison are separate obligations.
-/

open CategoryTheory Bicategory
namespace Kernel.Augmented
universe u v w

/-- In an empty horizontal graph every path has length zero. -/
theorem empty_path_length {C : Type u} {a b : C}
    (p : HPath (fun _ _ : C => Empty) a b) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e => exact Empty.elim e

theorem empty_horizontal_arity {C : Type u} [Quiver.{v} C] {f g : Side C}
    (b : Boundary (fun _ _ : C => Empty) f g) : b.arity = (0, 0) :=
  Prod.ext (empty_path_length b.input) (empty_path_length b.output.val)

namespace FromTwoCategory
variable (C : Type u) [Bicategory.{w,v} C]

/-- Dependent elimination of both empty paths gives precisely a 2-morphism. -/
def graph : CellGraph C (fun _ _ : C => Empty) where
  Cell {f g} boundary := by
    rcases f with ⟨a, c, f⟩
    rcases g with ⟨b, d, g⟩
    rcases boundary with ⟨input, output⟩
    cases input with
    | nil =>
      rcases output with ⟨output, _⟩
      cases output with
      | nil => exact f ⟶ g
      | cons _ e => exact Empty.elim e
    | cons _ e => exact Empty.elim e

variable {C}

abbrev Cell {a b : C} (f g : a ⟶ b) :=
  (graph C).Cell (Boundary.vertical f g)

def cellEquiv {a b : C} (f g : a ⟶ b) : Cell f g ≃ (f ⟶ g) := Equiv.refl _

def identity {a b : C} (f : a ⟶ b) : Cell f f := 𝟙 f

/-- Along a row in the augmented picture means vertical 2-cell composition. -/
def alongRow {a b : C} {f g h : a ⟶ b} (α : Cell f g) (β : Cell g h) : Cell f h :=
  α ≫ β

/-- Stacking augmented vertical cells means horizontal 2-cell composition. -/
def stack {a b c : C} {f g : a ⟶ b} {h k : b ⟶ c}
    (α : Cell f g) (β : Cell h k) : Cell (f ≫ h) (g ≫ k) :=
  α ▷ h ≫ g ◁ β

@[simp] theorem cellEquiv_identity {a b : C} (f : a ⟶ b) :
    cellEquiv f f (identity f) = 𝟙 f := rfl

@[simp] theorem cellEquiv_alongRow {a b : C} {f g h : a ⟶ b}
    (α : Cell f g) (β : Cell g h) :
    cellEquiv f h (alongRow α β) = cellEquiv f g α ≫ cellEquiv g h β := rfl

@[simp] theorem cellEquiv_stack {a b c : C} {f g : a ⟶ b} {h k : b ⟶ c}
    (α : Cell f g) (β : Cell h k) :
    cellEquiv (f ≫ h) (g ≫ k) (stack α β) =
      cellEquiv f g α ▷ h ≫ g ◁ cellEquiv h k β := rfl

@[simp] theorem identity_alongRow {a b : C} {f g : a ⟶ b} (α : Cell f g) :
    alongRow (identity f) α = α := Category.id_comp α

@[simp] theorem alongRow_identity {a b : C} {f g : a ⟶ b} (α : Cell f g) :
    alongRow α (identity g) = α := Category.comp_id α

theorem alongRow_assoc {a b : C} {f g h k : a ⟶ b}
    (α : Cell f g) (β : Cell g h) (γ : Cell h k) :
    alongRow (alongRow α β) γ = alongRow α (alongRow β γ) := Category.assoc α β γ

@[simp] theorem stack_identity {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    stack (identity f) (identity g) = identity (f ≫ g) := by
  change (𝟙 f) ▷ g ≫ f ◁ (𝟙 g) = 𝟙 (f ≫ g)
  simp

/-- The middle interchange is the bicategory's whiskering exchange law. -/
theorem interchange {a b c : C} {f₀ f₁ f₂ : a ⟶ b} {g₀ g₁ g₂ : b ⟶ c}
    (α : Cell f₀ f₁) (α' : Cell f₁ f₂) (β : Cell g₀ g₁) (β' : Cell g₁ g₂) :
    alongRow (stack α β) (stack α' β') =
      stack (alongRow α α') (alongRow β β') := by
  change f₀ ⟶ f₁ at α
  change f₁ ⟶ f₂ at α'
  change g₀ ⟶ g₁ at β
  change g₁ ⟶ g₂ at β'
  change (α ▷ g₀ ≫ f₁ ◁ β) ≫ (α' ▷ g₁ ≫ f₂ ◁ β') =
    (α ≫ α') ▷ g₀ ≫ f₂ ◁ (β ≫ β')
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc]

/-- Associativity of stacking, with the ambient bicategory's associators. -/
theorem stack_assoc_iso {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    {h h' : c ⟶ d} (α : Cell f f') (β : Cell g g') (γ : Cell h h') :
    stack (stack α β) γ ≫ (α_ f' g' h').hom =
      (α_ f g h).hom ≫ stack α (stack β γ) := by
  change f ⟶ f' at α
  change g ⟶ g' at β
  change h ⟶ h' at γ
  change ((α ▷ g ≫ f' ◁ β) ▷ h ≫ (f' ≫ g') ◁ γ) ≫ (α_ f' g' h').hom =
    (α_ f g h).hom ≫ (α ▷ (g ≫ h) ≫ f' ◁ (β ▷ h ≫ g' ◁ γ))
  simp [Category.assoc]

/-- In a strict 2-category, stacking is associative after endpoint transport. -/
theorem stack_assoc [Bicategory.Strict C] {a b c d : C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (α : Cell f f') (β : Cell g g') (γ : Cell h h') :
    HEq (stack (stack α β) γ) (stack α (stack β γ)) := by
  change f ⟶ f' at α
  change g ⟶ g' at β
  change h ⟶ h' at γ
  apply (conj_eqToHom_iff_heq _ _ (Strict.assoc f g h) (Strict.assoc f' g' h')).mp
  simp [stack, Category.assoc, Strict.associator_eqToIso]

/-- Left identity for stacking in a strict 2-category. -/
theorem identity_stack [Bicategory.Strict C] {a b : C} {f g : a ⟶ b}
    (α : Cell f g) : HEq (stack (identity (𝟙 a)) α) α := by
  change f ⟶ g at α
  apply (conj_eqToHom_iff_heq _ _ (Strict.id_comp f) (Strict.id_comp g)).mp
  simp [stack, identity, Strict.leftUnitor_eqToIso]

/-- Right identity for stacking in a strict 2-category. -/
theorem stack_identity_object [Bicategory.Strict C] {a b : C} {f g : a ⟶ b}
    (α : Cell f g) : HEq (stack α (identity (𝟙 b))) α := by
  change f ⟶ g at α
  apply (conj_eqToHom_iff_heq _ _ (Strict.comp_id f) (Strict.comp_id g)).mp
  simp [stack, identity, Strict.rightUnitor_eqToIso]

end FromTwoCategory
end Kernel.Augmented

import Kernel.Augmented.Substitution
import Kernel.Augmented.AlgebraExamples
import Kernel.Augmented.VerticalTwoCategory

/-! Checks of shape independence, boundary-sensitive equality and the derived API.
Cites: D-KR-18, D-RT-30, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.SubstitutionExamples
open Examples (Point H)
open AlgebraExamples (G O algebra)

def row (n : ℕ) : G.NonemptyRow Examples.left Examples.middle :=
  CellGraph.Row.single (b := Examples.cOneEmpty) n

def shape (n : ℕ) := SubstitutionShape.ofRow (row n)
  (3 : (.a : Point) ⟶ .c) (4 : (.a : Point) ⟶ .c) (ShortPath.empty Point.c)

theorem shape_independent (m n : ℕ) : shape m = shape n := rfl

def inputs (n m : ℕ) : (shape 0).Inputs G := ⟨⟨PUnit.unit, n⟩, m⟩

theorem apply_value (n m : ℕ) : O.apply (shape 0) (inputs n m) = n + m := by
  change (0 + n) + m = n + m
  rw [Nat.zero_add]

theorem labels_matter : O.apply (shape 0) (inputs 2 7) ≠ O.apply (shape 0) (inputs 3 7) := by
  rw [apply_value, apply_value]
  decide

def boundary0 : Boundary H ⟨.a, .b, 0⟩ ⟨.a, .b, 0⟩ := Boundary.vertical 0 0
def boundary1 : Boundary H ⟨.a, .b, 1⟩ ⟨.a, .b, 1⟩ := Boundary.vertical 1 1

/-- An erased label alone cannot distinguish these boundaries. -/
theorem raw_labels_heq : HEq (2 : G.Cell boundary0) (2 : G.Cell boundary1) := HEq.refl _

theorem boundaries_distinct : boundary0.frame ≠ boundary1.frame := by
  intro e
  have impossible : (0 : ℕ) = 1 :=
    congrArg (fun b : Σ f : Side Point, Σ g : Side Point, Boundary H f g => (b.1.arrow : ℕ)) e
  exact Nat.zero_ne_one impossible

/-- The transport API requires the missing incidence equality, even for constant cell types. -/
theorem cannot_transport_label :
    ¬ ∃ e : boundary0.frame = boundary1.frame,
      CellGraph.transport (G := G) e (2 : G.Cell boundary0) = (2 : G.Cell boundary1) := by
  rintro ⟨e, _⟩
  exact boundaries_distinct e

/-- These client proofs use ordinary equality and need no endpoint transports. -/
theorem alongRow_assoc {x y : Point} {f g h k : x ⟶ y}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical g h))
    (γ : G.Cell (Boundary.vertical h k)) :
    O.verticalAlongRow (O.verticalAlongRow α β) γ = O.verticalAlongRow α (O.verticalAlongRow β γ) :=
  Vertical.alongRow_assoc algebra α β γ

theorem interchange {x y z : Point} {f₀ f₁ f₂ : x ⟶ y} {g₀ g₁ g₂ : y ⟶ z}
    (α : G.Cell (Boundary.vertical f₀ f₁)) (α' : G.Cell (Boundary.vertical f₁ f₂))
    (β : G.Cell (Boundary.vertical g₀ g₁)) (β' : G.Cell (Boundary.vertical g₁ g₂)) :
    O.verticalAlongRow (O.verticalStack α β) (O.verticalStack α' β') =
      O.verticalStack (O.verticalAlongRow α α') (O.verticalAlongRow β β') :=
  Vertical.interchange algebra α α' β β'

end Kernel.Augmented.SubstitutionExamples

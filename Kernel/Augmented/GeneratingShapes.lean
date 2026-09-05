import Kernel.Augmented.Incidence
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites

/-! The elementary incidence category for generating augmented graphs.
This is a category of generator boundaries, not the category of augmented arities.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating
universe w

inductive Shape
  | point
  | vertical
  | horizontal
  | cell (inputs : ℕ) (output : Bool)
  deriving DecidableEq

/-- The top and bottom objects of a generator boundary, including both empty paths. -/
abbrev Vertex (n : ℕ) (ε : Bool) := Fin (n + 1) ⊕ Fin (ε.toNat + 1)

/-- Ordered input edges and the possible single output edge. -/
abbrev HorizontalEdge (n : ℕ) (ε : Bool) := Fin n ⊕ Fin ε.toNat

def verticalEndpoint (n : ℕ) (ε : Bool) (side endpoint : Bool) : Vertex n ε :=
  if endpoint then .inr (if side then Fin.last ε.toNat else 0)
  else .inl (if side then Fin.last n else 0)

def edgeEndpoint {n : ℕ} {ε : Bool} (i : HorizontalEdge n ε) (endpoint : Bool) : Vertex n ε :=
  match i with
  | .inl i => .inl (if endpoint then i.succ else i.castSucc)
  | .inr i => .inr (if endpoint then i.succ else i.castSucc)

inductive Hom : Shape → Shape → Type
  | id (x : Shape) : Hom x x
  | verticalEndpoint (endpoint : Bool) : Hom .point .vertical
  | horizontalEndpoint (endpoint : Bool) : Hom .point .horizontal
  | cellVertex {n ε} (i : Vertex n ε) : Hom .point (.cell n ε)
  | cellVertical {n ε} (side : Bool) : Hom .vertical (.cell n ε)
  | cellHorizontal {n ε} (i : HorizontalEdge n ε) : Hom .horizontal (.cell n ε)

namespace Hom

def comp {x y z : Shape} : Hom x y → Hom y z → Hom x z
  | .id _, g => g
  | f, .id _ => f
  | .verticalEndpoint endpoint, .cellVertical side => .cellVertex (Generating.verticalEndpoint _ _ side endpoint)
  | .horizontalEndpoint endpoint, .cellHorizontal i => .cellVertex (edgeEndpoint i endpoint)

end Hom

instance : SmallCategory Shape where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intro x y f; rfl
  comp_id := by intro x y f; cases f <;> rfl
  assoc := by intro a b c d f g h; cases f <;> cases g <;> cases h <;> rfl

def Hom.op {x y : Shape} (f : Hom x y) : Opposite.op y ⟶ Opposite.op x :=
  Quiver.Hom.op (V := Shape) f

/-- The explicit candidate base for the global free construction. -/
abbrev Presheaf := Shapeᵒᵖ ⥤ Type w

@[simp] theorem vertical_incidence {n ε} (side endpoint : Bool) :
    Hom.comp (Hom.verticalEndpoint endpoint) (Hom.cellVertical (n := n) (ε := ε) side) =
      Hom.cellVertex (verticalEndpoint n ε side endpoint) := rfl

@[simp] theorem horizontal_incidence {n ε} (i : HorizontalEdge n ε) (endpoint : Bool) :
    Hom.comp (Hom.horizontalEndpoint endpoint) (Hom.cellHorizontal i) = Hom.cellVertex (edgeEndpoint i endpoint) := rfl

/-- Zero outputs have no horizontal output edge but still have one bottom object. -/
theorem empty_output_no_edge (i : Fin Bool.false.toNat) : False := Fin.elim0 i

theorem empty_output_shared_bottom (n : ℕ) :
    verticalEndpoint n false false true = verticalEndpoint n false true true := rfl

theorem empty_input_shared_top (ε : Bool) :
    verticalEndpoint 0 ε false false = verticalEndpoint 0 ε true false := rfl

end Kernel.Augmented.Generating

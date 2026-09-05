import Kernel.Augmented.EquationRows

/-! The incident domain of the nested substitution equation.
Reference: Koudenburg, arXiv:1910.11189v4, Definition 1.2, associativity.
Cites: D-KR-18, D-TL-21, AT-FD-7.

Both bands share their complete vertical arrows. Each inner row is nonempty.
This records when both substitution expressions are defined, without imposing
a canonical arity or a general pasting/normalization theorem.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

namespace Nested

/-- Two incident vertical arrows at a boundary of a nested row. -/
structure Side (C : Type u) [Category.{v} C] where
  upper : Kernel.Augmented.Side C
  bottom : C
  lower : upper.target ⟶ bottom

namespace Side
variable {C : Type u} [Category.{v} C]
def middle (s : Side C) : Kernel.Augmented.Side C := ⟨s.upper.target, s.bottom, s.lower⟩
def composite (s : Side C) : Kernel.Augmented.Side C := s.upper.post s.lower
end Side

/-- One outer cell together with its incident nonempty inner row. -/
structure Step {C : Type u} [Category.{v} C] {H : C → C → Type h}
    (G : CellGraph.{u,v,h,c} C H) (s t : Side C) where
  inner : G.NonemptyRow s.upper t.upper
  output : ShortPath H s.bottom t.bottom
  outer : G.Cell (CellGraph.Row.outerBoundary inner s.lower t.lower output)

variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def Vertex (_G : CellGraph.{u,v,h,c} C H) := Side C
instance quiver (G : CellGraph.{u,v,h,c} C H) : Quiver (Vertex G) where
  Hom s t := Step G s t

abbrev Row (G : CellGraph.{u,v,h,c} C H) (s t : Side C) :=
  Quiver.Path (V := Vertex G) s t
abbrev NonemptyRow (G : CellGraph.{u,v,h,c} C H) (s t : Side C) :=
  {r : Row G s t // 0 < r.length}

namespace Row

def inner {s : Side C} : {t : Side C} → Row G s t → G.Row s.upper t.upper
  | _, .nil => .nil
  | _, .cons r e => (inner r).comp e.inner.val

def outer {s : Side C} : {t : Side C} → Row G s t → G.Row s.middle t.middle
  | _, .nil => .nil
  | _, .cons r e => (outer r).cons ⟨_, e.outer⟩

def composite (O : Operations G) {s : Side C} :
    {t : Side C} → Row G s t → G.Row s.composite t.composite
  | _, .nil => .nil
  | _, .cons r e => (composite O r).cons
      ⟨_, O.substitute e.inner _ _ e.output e.outer⟩

theorem length_le_inner {s t : Side C} (r : Row G s t) : r.length ≤ (inner r).length := by
  induction r with
  | nil => exact Nat.le_refl _
  | cons r e ih =>
    change Quiver.Path.length (V := Vertex G) r + 1 ≤ ((inner r).comp e.inner.val).length
    calc
      _ ≤ (inner r).length + e.inner.val.length := Nat.add_le_add ih e.inner.property
      _ = _ := (Quiver.Path.length_comp (V := G.Vertex) _ _).symm

@[simp] theorem outer_length {s t : Side C} (r : Row G s t) :
    (outer r).length = r.length := by
  induction r with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

@[simp] theorem composite_length (O : Operations G) {s t : Side C} (r : Row G s t) :
    (composite O r).length = r.length := by
  induction r with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The flattened inner outputs are exactly the outer row's inputs. -/
theorem inner_output {s t : Side C} (r : Row G s t) :
    CellGraph.Row.output (inner r) = CellGraph.Row.input (outer r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change CellGraph.Row.output ((inner r).comp e.inner.val) =
      (CellGraph.Row.input (outer r)).comp (CellGraph.Row.output e.inner.val)
    rw [CellGraph.Row.output_comp, ih]
    rfl

theorem composite_input (O : Operations G) {s t : Side C} (r : Row G s t) :
    CellGraph.Row.input (composite O r) = CellGraph.Row.input (inner r) := by
  induction r with
  | nil => rfl
  | @cons t z r e ih =>
    change (CellGraph.Row.input (composite O r)).comp
      (CellGraph.Row.input (f := t.upper) (g := z.upper) e.inner.val) =
      CellGraph.Row.input ((inner r).comp e.inner.val)
    rw [CellGraph.Row.input_comp, ih]
    rfl

theorem composite_output (O : Operations G) {s t : Side C} (r : Row G s t) :
    CellGraph.Row.output (composite O r) = CellGraph.Row.output (outer r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (CellGraph.Row.output (composite O r)).comp e.output.val =
      (CellGraph.Row.output (outer r)).comp e.output.val
    rw [ih]
    rfl

end Row

namespace NonemptyRow
def inner {s t : Side C} (r : NonemptyRow G s t) : G.NonemptyRow s.upper t.upper :=
  ⟨Row.inner r.val, Nat.lt_of_lt_of_le r.property (Row.length_le_inner r.val)⟩

def outer {s t : Side C} (r : NonemptyRow G s t) : G.NonemptyRow s.middle t.middle :=
  ⟨Row.outer r.val, by rw [Row.outer_length]; exact r.property⟩

def composite (O : Operations G) {s t : Side C} (r : NonemptyRow G s t) :
    G.NonemptyRow s.composite t.composite :=
  ⟨Row.composite O r.val, by rw [Row.composite_length]; exact r.property⟩
end NonemptyRow

end Nested
end Kernel.Augmented

import Kernel.Augmented.SimplexObstruction
import Kernel.Augmented.FromTwoCategory
import Kernel.Augmented.Operations

/-! Concrete boundary checks for D-KR-18 and AT-FD-7.
The generator labels below do not assert any substitution equations.
-/

open CategoryTheory
namespace Kernel.Augmented.Examples

inductive Point | a | b | c
deriving DecidableEq

instance : Category Point where
  Hom _ _ := ℕ
  id _ := 0
  comp f g := f + g
  id_comp := Nat.zero_add
  comp_id := Nat.add_zero
  assoc := Nat.add_assoc

instance {x y : Point} (n : ℕ) : OfNat (x ⟶ y) n := ⟨(n : ℕ)⟩

abbrev H (_ _ : Point) := Unit

def generators : CellGraph Point H where
  Cell _ := Unit

-- An inhabitant of the operation types, before imposing the algebra equations.
def operations : Operations generators where
  horizontalIdentity _ := Unit.unit
  verticalIdentity _ := Unit.unit
  substitute := fun {_ _} _ {_ _} _ _ _ _ => Unit.unit

def left : Side Point := ⟨.a, .a, 0⟩
def middle : Side Point := ⟨.b, .a, 1⟩
def right : Side Point := ⟨.c, .b, 2⟩

/-- The required one-input, empty-output generator. -/
def cOneEmpty : Boundary H left middle :=
  ⟨HPath.single Unit.unit, ShortPath.empty Point.a⟩

def cOneOne : Boundary H middle right :=
  ⟨HPath.single Unit.unit, ShortPath.single Unit.unit⟩

def mixed : generators.NonemptyRow left right :=
  ⟨((Quiver.Path.nil : generators.Row left left).cons ⟨cOneEmpty, Unit.unit⟩).cons
    ⟨cOneOne, Unit.unit⟩, by decide⟩

theorem cOneEmpty_arity : cOneEmpty.arity = (1, 0) := rfl

theorem mixed_counts :
    mixed.val.length = 2 ∧ (CellGraph.Row.input mixed.val).length = 2 ∧
      (CellGraph.Row.output mixed.val).length = 1 := by decide

theorem mixed_horizontal_boundary :
    (CellGraph.Row.horizontalBoundary mixed (by decide)).arity = (2, 1) := rfl

def vanished : generators.NonemptyRow left middle :=
  CellGraph.Row.single (b := cOneEmpty) Unit.unit

theorem vanished_no_active_encoding
    (f : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1) :
    ¬ Simplex.IsActive f :=
  Simplex.no_active_zero_to_one f

def nullaryInput : Boundary H ⟨.a, .a, 0⟩ ⟨.a, .b, 1⟩ :=
  ⟨.nil, ShortPath.single Unit.unit⟩

theorem nullaryInput_arity : nullaryInput.arity = (0, 1) := rfl

def vertical01 : Boundary H ⟨.a, .b, 0⟩ ⟨.a, .b, 1⟩ :=
  Boundary.vertical 0 1

def vertical12 : Boundary H ⟨.a, .b, 1⟩ ⟨.a, .b, 2⟩ :=
  Boundary.vertical 1 2

def verticalRow : generators.NonemptyRow ⟨.a, .b, 0⟩ ⟨.a, .b, 2⟩ :=
  ⟨((Quiver.Path.nil : generators.Row ⟨.a, .b, 0⟩ ⟨.a, .b, 0⟩).cons
    ⟨vertical01, Unit.unit⟩).cons ⟨vertical12, Unit.unit⟩, by decide⟩

theorem vertical_row_counts :
    verticalRow.val.length = 2 ∧ (CellGraph.Row.input verticalRow.val).length = 0 ∧
      (CellGraph.Row.output verticalRow.val).length = 0 := by decide

/-- Empty horizontal paths do not allow a zero-cell substitution row. -/
example : ¬ 0 < (Quiver.Path.nil : generators.Row left left).length := by decide

/-- Equal endpoint objects are insufficient: the middle vertical arrows differ. -/
example : True := by
  fail_if_success
    let bad : generators.Row ⟨.a, .b, 0⟩ ⟨.a, .b, 2⟩ :=
      ((Quiver.Path.nil : generators.Row ⟨.a, .b, 0⟩ ⟨.a, .b, 0⟩).cons ⟨vertical01, Unit.unit⟩).cons
        (⟨Boundary.vertical (0 : (.a : Point) ⟶ .b) 2, Unit.unit⟩ :
          generators.quiver.Hom ⟨.a, .b, 0⟩ ⟨.a, .b, 2⟩)
  trivial

/-- Stacking uses the row's whole output as input of its lower cell. -/
def lowerBoundary := CellGraph.Row.outerBoundary mixed
  (3 : (.a : Point) ⟶ .c) (4 : (.b : Point) ⟶ .c) (ShortPath.empty Point.c)

def stackedBoundary := CellGraph.Row.compositeBoundary mixed
  (3 : (.a : Point) ⟶ .c) (4 : (.b : Point) ⟶ .c) (ShortPath.empty Point.c)

theorem lowerBoundary_arity : lowerBoundary.arity = (1, 0) := rfl
theorem stackedBoundary_arity : stackedBoundary.arity = (2, 0) := rfl
theorem stacked_left_side : (left.post (3 : (.a : Point) ⟶ .c)).arrow = 3 := rfl
theorem stacked_right_side : (right.post (4 : (.b : Point) ⟶ .c)).arrow = 6 := rfl

def mixedComposite : generators.Cell stackedBoundary :=
  operations.substitute mixed (3 : (.a : Point) ⟶ .c) (4 : (.b : Point) ⟶ .c)
    (ShortPath.empty Point.c) Unit.unit

def verticalAlongRow : generators.Cell (Boundary.vertical
    (0 : (.a : Point) ⟶ .b) 2) :=
  operations.verticalAlongRow (f := 0) (g := 1) (k := 2) Unit.unit Unit.unit

def verticalStack : generators.Cell (Boundary.vertical
    (3 : (.a : Point) ⟶ .c) 5) :=
  operations.verticalStack (f := (0 : (.a : Point) ⟶ .b)) (g := 1)
    (h := (3 : (.b : Point) ⟶ .c)) (k := 4) Unit.unit Unit.unit

end Kernel.Augmented.Examples

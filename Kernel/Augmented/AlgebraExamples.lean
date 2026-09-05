import Kernel.Augmented.AdditiveModel
import Kernel.Augmented.Examples

/-! Nontrivial equation instances and rejected associativity domains.
Cites: D-KR-18, D-RT-30, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.AlgebraExamples
open Examples (Point H)

abbrev G := AdditiveModel.graph Point H ℕ
def algebra : Algebra G := AdditiveModel.algebra
abbrev O := algebra.toOperations

def left : Nested.Side Point := ⟨Examples.left, .c, 3⟩
def middle : Nested.Side Point := ⟨Examples.middle, .c, 4⟩
def right : Nested.Side Point := ⟨Examples.right, .c, 5⟩

/-- The first inner cell has one input and no output. -/
def first : Nested.Step G left middle where
  inner := CellGraph.Row.single (b := Examples.cOneEmpty) (2 : ℕ)
  output := ShortPath.empty Point.c
  outer := (7 : ℕ)

/-- The second inner cell has one input/output; its outer cell has empty output. -/
def second : Nested.Step G middle right where
  inner := CellGraph.Row.single (b := Examples.cOneOne) (3 : ℕ)
  output := ShortPath.empty Point.c
  outer := (11 : ℕ)

def nested : Nested.NonemptyRow G left right :=
  ⟨((Quiver.Path.nil : Nested.Row G left left).cons first).cons second, by decide⟩

theorem nested_counts :
    nested.val.length = 2 ∧ nested.inner.val.length = 2 ∧
      (CellGraph.Row.input nested.inner.val).length = 2 ∧
      (CellGraph.Row.output nested.inner.val).length = 1 ∧
      (CellGraph.Row.input nested.outer.val).length = 1 ∧
      (CellGraph.Row.output nested.outer.val).length = 0 := by decide

/-- The last cell has empty input and one output. -/
def lastBoundary := CellGraph.Row.outerBoundary nested.outer
  (6 : (.c : Point) ⟶ .a) (7 : (.c : Point) ⟶ .b) (ShortPath.single Unit.unit)

theorem last_arity : lastBoundary.arity = (0, 1) := rfl

def compositeLeft := O.assocLeft nested
  (6 : (.c : Point) ⟶ .a) (7 : (.c : Point) ⟶ .b) (ShortPath.single Unit.unit) (13 : ℕ)

def compositeRight := O.assocRight nested
  (6 : (.c : Point) ⟶ .a) (7 : (.c : Point) ⟶ .b) (ShortPath.single Unit.unit) (13 : ℕ)

theorem nested_associativity : compositeLeft = compositeRight :=
  eq_of_heq (algebra.laws.assoc nested
    (6 : (.c : Point) ⟶ .a) (7 : (.c : Point) ⟶ .b) (ShortPath.single Unit.unit) (13 : ℕ))

theorem nested_value : compositeLeft = 36 ∧ compositeRight = 36 := by decide

theorem outside_left : (left.upper.post (left.lower ≫ (6 : (.c : Point) ⟶ .a))).arrow = 9 := rfl
theorem outside_right : (right.upper.post (right.lower ≫ (7 : (.c : Point) ⟶ .b))).arrow = 14 := rfl

/-- Distinct labels at the same incident boundary remain distinct. -/
theorem cells_distinct : (2 : G.Cell Examples.cOneEmpty) ≠ (3 : G.Cell Examples.cOneEmpty) := by decide

def identityBefore := O.insertedComposite
  (Quiver.Path.nil : G.Row Examples.left Examples.left) first.inner.val (by decide)
  (3 : (.a : Point) ⟶ .c) (4 : (.a : Point) ⟶ .c) (ShortPath.empty Point.c) (7 : ℕ)

def identityAfter := O.insertedComposite first.inner.val
  (Quiver.Path.nil : G.Row Examples.middle Examples.middle) (by decide)
  (3 : (.a : Point) ⟶ .c) (4 : (.a : Point) ⟶ .c) (ShortPath.empty Point.c) (7 : ℕ)

theorem endpoint_insertion_values : identityBefore = 9 ∧ identityAfter = 9 := by decide

/-- Two factorizations with equal composite arrows need not share either band. -/
def splitA : Nested.Side Point := ⟨⟨.a, .a, 1⟩, .a, 2⟩
def splitB : Nested.Side Point := ⟨⟨.a, .a, 2⟩, .a, 1⟩

theorem equal_composites : splitA.composite = splitB.composite := rfl
theorem different_upper_sides : splitA.upper ≠ splitB.upper := by
  intro h
  have impossible : (1 : ℕ) = 2 := congrArg (fun s : Side Point => (s.arrow : ℕ)) h
  contradiction

theorem different_lower_sides : splitA.middle ≠ splitB.middle := by
  intro h
  have impossible : (2 : ℕ) = 1 := congrArg (fun s : Side Point => (s.arrow : ℕ)) h
  contradiction

def selfStep (s : Nested.Side Point) : Nested.Step G s s where
  inner := CellGraph.Row.single (O.verticalIdentity s.upper.arrow)
  output := ShortPath.empty s.bottom
  outer := (1 : ℕ)

-- Positive control: all sides agree and both rows have one cell per block.
def validNested : Nested.NonemptyRow G splitA splitA :=
  ⟨((Quiver.Path.nil : Nested.Row G splitA splitA).cons (selfStep splitA)).cons
    (selfStep splitA), by decide⟩

/-- Matching only the composed arrows cannot justify the associativity equation. -/
example : True := by
  fail_if_success
    let bad : Nested.Row G splitA splitB :=
      ((Quiver.Path.nil : Nested.Row G splitA splitA).cons (selfStep splitA)).cons (selfStep splitB)
  trivial

/-- Empty input is allowed, but an empty inner substitution row is not. -/
example : True := by
  fail_if_success
    let bad : Nested.Step G splitA splitA := {
      inner := ⟨Quiver.Path.nil, by decide⟩
      output := ShortPath.empty splitA.bottom
      outer := (1 : ℕ)
    }
  trivial

end Kernel.Augmented.AlgebraExamples

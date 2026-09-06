import Kernel.Augmented.GeneratingInsertionLaw

/-! Free representatives of nested rows with every intermediate vertical side retained.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

def generatorNestedSide (s : Nested.Side (Vertical A)) : Nested.Side (Paths A.A.Objects) :=
  ⟨generatorSide A s.upper, s.bottom, s.lower.toPath⟩

def generatorNestedStep {s t : Nested.Side (Vertical A)} (e : Nested.Step (cells A) s t) :
    Nested.Step A.A.freeObject.cells (generatorNestedSide A s) (generatorNestedSide A t) where
  inner := generatorNonemptyRow A e.inner
  output := e.output
  outer := generatorOuter A e.inner s.lower t.lower e.output e.outer

def generatorNestedRow {s : Nested.Side (Vertical A)} : {t : Nested.Side (Vertical A)} →
    Nested.Row (cells A) s t → Nested.Row A.A.freeObject.cells (generatorNestedSide A s) (generatorNestedSide A t)
  | _, .nil => .nil
  | _, .cons r e => (generatorNestedRow r).cons (generatorNestedStep A e)

theorem generatorNestedRow_length {s t : Nested.Side (Vertical A)} (r : Nested.Row (cells A) s t) :
    (generatorNestedRow A r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

def generatorNestedNonemptyRow {s t : Nested.Side (Vertical A)} (r : Nested.NonemptyRow (cells A) s t) :
    Nested.NonemptyRow A.A.freeObject.cells (generatorNestedSide A s) (generatorNestedSide A t) :=
  ⟨generatorNestedRow A r.val, by rw [generatorNestedRow_length]; exact r.property⟩

theorem generatorNestedRow_inner {s t : Nested.Side (Vertical A)} (r : Nested.Row (cells A) s t) :
    Nested.Row.inner (generatorNestedRow A r) = generatorRow A (Nested.Row.inner r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (Nested.Row.inner (generatorNestedRow A r)).comp (generatorRow A e.inner.val) = _
    rw [ih, ← generatorRow_comp]
    rfl

theorem generatorNestedRow_outer {s t : Nested.Side (Vertical A)} (r : Nested.Row (cells A) s t) :
    Nested.Row.outer (generatorNestedRow A r) = generatorRow A (Nested.Row.outer r) := by
  induction r with
  | nil => rfl
  | @cons t z r e ih =>
    apply eq_of_heq
    apply CellGraph.Row.cons_heq rfl rfl rfl (heq_of_eq ih)
    · exact Boundary.heq_of_frame_eq (Boundary.frame_eq rfl rfl
        (heq_of_eq (generatorRow_output A e.inner.val)) (HEq.refl _))
    · exact CellGraph.castInput_heq (generatorRow_output A e.inner.val).symm (generatorCell A e.outer)

theorem generatorNestedRow_outer_output {s t : Nested.Side (Vertical A)} (r : Nested.Row (cells A) s t) :
    CellGraph.Row.output (Nested.Row.outer (generatorNestedRow A r)) =
      CellGraph.Row.output (Nested.Row.outer r) := by
  rw [generatorNestedRow_outer, generatorRow_output]

/-- Evaluating the inner-first composites of a lifted nested row recovers all its composite cells. -/
theorem generatorNestedRow_composite_evaluation {s t : Nested.Side (Vertical A)}
    (r : Nested.Row (cells A) s t) :
    HEq ((evaluationCells A).row (Nested.Row.composite A.A.freeAlgebra.toOperations (generatorNestedRow A r)))
      (Nested.Row.composite (operations A) r) := by
  induction r with
  | nil => exact CellGraph.Row.nil_heq (generatorPost_evaluation A s.upper s.lower)
  | @cons t z r e ih =>
    apply CellGraph.Row.cons_heq (generatorPost_evaluation A s.upper s.lower)
      (generatorPost_evaluation A t.upper t.lower) (generatorPost_evaluation A z.upper z.lower) ih
    · exact Boundary.heq_of_frame_eq (generatorComposite_evaluation A e.inner t.lower z.lower e.output)
    · exact CellGraph.Total.cell_heq (((evaluationCells A).pack_cell _).trans
        (operations_substitute A e.inner t.lower z.lower e.output e.outer).symm)

end Kernel.Augmented.GeneratingMonadAlgebra

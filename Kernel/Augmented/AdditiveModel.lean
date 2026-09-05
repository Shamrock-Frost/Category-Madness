import Kernel.Augmented.Algebra
import Mathlib.Algebra.Group.Basic

/-! An augmented algebra with arbitrary commutative additive cell labels.
Cites: D-KR-18, D-RT-30, AT-FD-7.

The vertical category and horizontal graph are arbitrary. Every incident cell
is labelled by an element of a supplied additive commutative monoid, and
substitution adds the labels. This validates all equation families without
collapsing the cells to a singleton or assuming the equations as axioms.
-/

open CategoryTheory
namespace Kernel.Augmented.AdditiveModel
universe u v h c

abbrev graph (C : Type u) [Quiver.{v} C] (H : C → C → Type h) (M : Type c) :
    CellGraph C H where
  Cell _ := M

variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {M : Type c} [AddCommMonoid M]

def rowSum {f : Side C} : {g : Side C} → (graph C H M).Row f g → M
  | _, .nil => 0
  | _, .cons r e => rowSum r + (e.2 : M)

@[simp] theorem rowSum_comp {f g k : Side C}
    (p : (graph C H M).Row f g) (q : (graph C H M).Row g k) :
    rowSum (p.comp q) = rowSum p + rowSum q := by
  induction q with
  | nil => exact (add_zero _).symm
  | cons q e ih =>
    change rowSum (p.comp q) + (e.2 : M) = rowSum p + (rowSum q + (e.2 : M))
    rw [ih]
    exact add_assoc _ _ _

@[simp] theorem rowSum_single {f g : Side C} {b : Boundary H f g}
    (φ : (graph C H M).Cell b) : rowSum (CellGraph.Row.single φ).val = (φ : M) :=
  zero_add (φ : M)

def operations : Operations (graph C H M) where
  horizontalIdentity _ := (0 : M)
  verticalIdentity _ := (0 : M)
  substitute := fun {_ _} r {_ _} _ _ _ ψ => rowSum r.val + (ψ : M)

@[simp] theorem shortIdentity_zero {a b : C} (p : ShortPath H a b) :
    (operations (M := M)).shortIdentity p = (0 : M) := by
  apply ShortPath.cases_on (fun {_ _} p => (operations (M := M)).shortIdentity p = (0 : M))
  · intro a
    rfl
  · intro a b j
    rfl

@[simp] theorem horizontalIdentities_sum {a b : C} (p : HPath H a b) :
    rowSum ((operations (M := M)).horizontalIdentities p) = (0 : M) := by
  induction p with
  | nil => rfl
  | cons p j ih =>
    change rowSum ((operations (M := M)).horizontalIdentities p) + 0 = 0
    rw [add_zero]
    exact ih

@[simp] theorem identityRow_sum {a b : C} (p : HPath H a b) :
    rowSum ((operations (M := M)).identityRow p).val = (0 : M) := by
  cases p with
  | nil => exact zero_add (0 : M)
  | cons p j =>
    exact horizontalIdentities_sum (C := C) (H := H) (M := M)
      (Quiver.Path.cons (V := Horizontal H) p j)

@[simp] theorem insertedRow_sum {f g k : Side C}
    (p : (graph C H M).Row f g) (q : (graph C H M).Row g k) :
    rowSum ((operations (M := M)).insertedRow p q).val = rowSum (p.comp q) := by
  change rowSum ((p.cons _).comp q) = rowSum (p.comp q)
  rw [rowSum_comp, rowSum_comp]
  change (rowSum p + 0) + rowSum q = rowSum p + rowSum q
  rw [add_zero]

/-- Substituting each block adds exactly the labels of both rows. -/
theorem nested_composite_sum {s t : Nested.Side C} (r : Nested.Row (graph C H M) s t) :
    rowSum (Nested.Row.composite operations r) =
      rowSum (Nested.Row.inner r) + rowSum (Nested.Row.outer r) := by
  induction r with
  | nil => exact (add_zero _).symm
  | cons r e ih =>
    change rowSum (Nested.Row.composite operations r) + (rowSum e.inner.val + (e.outer : M)) =
      rowSum ((Nested.Row.inner r).comp e.inner.val) +
        (rowSum (Nested.Row.outer r) + (e.outer : M))
    rw [rowSum_comp, ih]
    exact add_add_add_comm _ _ _ _

/-- Every equation is proved from addition and the incident row constructions. -/
def algebra : Algebra (graph C H M) where
  toOperations := operations
  laws := {
    verticalIdentity_stack := by
      intro a b d f g
      change (0 + 0) + 0 = (0 : M)
      simp
    leftUnit := by
      intro f g b φ
      change rowSum (CellGraph.Row.single φ).val + (operations (M := M)).shortIdentity b.output = φ
      rw [rowSum_single, shortIdentity_zero, add_zero]
    rightUnit := by
      intro f g b φ
      change rowSum ((operations (M := M)).identityRow b.input).val + (φ : M) = φ
      rw [identityRow_sum, zero_add]
    insertion := by
      intro f g k p q hn a b h l L ψ
      change rowSum ((operations (M := M)).insertedRow p q).val + (ψ : M) =
        rowSum (p.comp q) + (ψ : M)
      rw [insertedRow_sum]
    assoc := by
      intro s t r a b p q L χ
      change rowSum (Nested.Row.composite operations r.val) + (χ : M) =
        rowSum (Nested.Row.inner r.val) + (rowSum (Nested.Row.outer r.val) + (χ : M))
      rw [nested_composite_sum, add_assoc]
  }

end Kernel.Augmented.AdditiveModel

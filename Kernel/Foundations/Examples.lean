import Kernel.Foundations.Inventory

/-! Small category and groupoid examples for the first foundation work item.
Cites: D-FD-01, D-KR-14, AT-KR-0.
These check ordinary nerves and strict Segal laws; no groupoid-nerve Kan
instance is assumed from the pinned dependency.
-/

open CategoryTheory

namespace Kernel.Foundations.Examples

abbrev BooleanGroupoid := SingleObj (Equiv.Perm Bool)

def flip : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def loop : SingleObj.star (Equiv.Perm Bool) ⟶ SingleObj.star (Equiv.Perm Bool) :=
  SingleObj.toEnd _ flip

theorem loop_ne_id : loop ≠ 𝟙 _ := by
  intro h
  have h' := congrArg (fun f : Equiv.Perm Bool => f false) h
  cases h'

theorem loop_comp_loop : loop ≫ loop = 𝟙 _ := by
  change flip * flip = 1
  ext b
  exact Bool.not_not b

example : Groupoid BooleanGroupoid := inferInstance

def groupoidNerve : SSet.{0} := nerve BooleanGroupoid

theorem groupoidNerve_strictSegal : SSet.IsStrictSegal groupoidNerve := by
  change SSet.IsStrictSegal (nerve BooleanGroupoid)
  infer_instance

/-- Every arrow is invertible, including the displayed nonidentity loop. -/
theorem arrow_inverse {a b : BooleanGroupoid} (f : a ⟶ b) :
    f ≫ Groupoid.inv f = 𝟙 a := Groupoid.comp_inv f

end Kernel.Foundations.Examples

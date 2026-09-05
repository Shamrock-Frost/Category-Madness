import Interface.Prototype.Operations

/-! A law-using client shared by both builds (D-CH-22, AT-FD-2). -/
set_option autoImplicit false

universe u

namespace Theory.Prototype

open Interface.Prototype

noncomputable def product : List Carrier.{u} → Carrier.{u}
  | [] => one
  | x :: xs => mul x (product xs)

theorem product_append (xs ys : List Carrier.{u}) :
    product (xs ++ ys) = mul (product xs) (product ys) := by
  induction xs with
  | nil => exact (one_mul (product ys)).symm
  | cons x xs ih =>
    change mul x (product (xs ++ ys)) = mul (mul x (product xs)) (product ys)
    rw [ih, mul_assoc]

theorem right_identity_unique (e : Carrier.{u}) (h : ∀ x, mul x e = x) : e = one :=
  (one_mul e).symm.trans (h one)

theorem product_generator_ne_one : product [generator.{u}] ≠ one := by
  change mul generator one ≠ one
  rw [mul_one]
  exact generator_ne_one

end Theory.Prototype

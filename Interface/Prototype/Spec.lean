/-! A dependent, nontrivial specification for AT-FD-2 (D-RT-28, D-CH-25).
This is an experimental seal fragment, not the categorical root interface. -/
set_option autoImplicit false

universe u

namespace Interface.Prototype

structure MonoidSpec where
  Carrier : Type u
  one : Carrier
  mul : Carrier → Carrier → Carrier
  generator : Carrier
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  generator_ne_one : generator ≠ one

end Interface.Prototype

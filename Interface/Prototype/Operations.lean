import Interface.Prototype.Monoid

/-! Transparent projections of the sealed specification (D-RT-28, AT-FD-2). -/
set_option autoImplicit false

universe u

namespace Interface.Prototype

noncomputable section

abbrev Carrier : Type u := monoid.{u}.Carrier
abbrev one : Carrier.{u} := monoid.one
abbrev mul : Carrier.{u} → Carrier.{u} → Carrier.{u} := monoid.mul
abbrev generator : Carrier.{u} := monoid.generator

theorem one_mul (x : Carrier.{u}) : mul one x = x := monoid.one_mul x
theorem mul_one (x : Carrier.{u}) : mul x one = x := monoid.mul_one x
theorem mul_assoc (x y z : Carrier.{u}) : mul (mul x y) z = mul x (mul y z) :=
  monoid.mul_assoc x y z
theorem generator_ne_one : generator.{u} ≠ one := monoid.generator_ne_one

end
end Interface.Prototype

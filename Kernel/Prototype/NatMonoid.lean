import Interface.Prototype.Spec

/-! KERNEL: the complete AT-FD-2 witness, using lifted natural addition.
Cites: D-CH-21, D-CH-25, D-RT-28. -/
set_option autoImplicit false

universe u

namespace Kernel.Prototype

def natMonoid : Interface.Prototype.MonoidSpec.{u} where
  Carrier := ULift.{u} Nat
  one := ⟨0⟩
  mul x y := ⟨x.down + y.down⟩
  generator := ⟨1⟩
  one_mul x := congrArg ULift.up (Nat.zero_add x.down)
  mul_one x := congrArg ULift.up (Nat.add_zero x.down)
  mul_assoc x y z := congrArg ULift.up (Nat.add_assoc x.down y.down z.down)
  generator_ne_one h := Nat.noConfusion (congrArg ULift.down h)

end Kernel.Prototype

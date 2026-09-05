import Kernel.Prototype.NatMonoid

/-! Opaque data and laws sealed together (D-RT-28, D-CH-25, AT-FD-2). -/
set_option autoImplicit false

universe u

namespace Interface.Prototype

noncomputable opaque monoid : MonoidSpec.{u} := Kernel.Prototype.natMonoid

end Interface.Prototype

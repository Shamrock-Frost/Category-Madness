import Interface.Prototype.Spec

/-! The only stub axiom replaces the complete package (D-RT-28, AT-FD-2).
The swap runner preserves all other Interface modules byte for byte. -/
set_option autoImplicit false

universe u

namespace Interface.Prototype

axiom monoid : MonoidSpec.{u}

end Interface.Prototype

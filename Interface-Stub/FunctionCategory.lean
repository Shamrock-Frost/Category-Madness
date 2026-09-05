import Interface.CategorySpec

/-! Swap-only implementation; forbidden in implementation acceptance evidence.
Cites: D-CH-25, D-RT-28, AT-FD-2. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Interface

axiom functionCategory.{u} : CategorySpec.{u+1, u}

end Interface

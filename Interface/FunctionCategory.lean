import Interface.CategorySpec
import Root.MatrixCategory

/-! First inhabited seal, authorized by the nonempty-seal gate.
Cites: D-CH-25, D-RT-28, AT-FD-2. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Interface

noncomputable opaque functionCategory.{u} : CategorySpec.{u+1, u} :=
  ⟨Type u, Root.MatrixCategory.functions⟩

end Interface

import Prototype.Audit
import Interface.Prototype.Operations

namespace Kernel.NegativeFixture
private def implementationValue : Nat := 37
def bridge : Nat := implementationValue
end Kernel.NegativeFixture

-- The immediate client term hides the implementation behind a helper.
def helper : Nat := Kernel.NegativeFixture.bridge
def leakingClient : Nat := helper
#audit_client leakingClient

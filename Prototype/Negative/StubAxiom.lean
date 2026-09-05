import Prototype.Audit
import Interface.Prototype.Operations

-- Must fail only in the stub build: its axiom is forbidden as implementation evidence.
#audit_axioms Interface.Prototype.monoid

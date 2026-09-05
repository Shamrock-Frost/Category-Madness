import Prototype.Audit

axiom falseFoundation : False
theorem invalidAcceptance : False := falseFoundation
#audit_axioms invalidAcceptance

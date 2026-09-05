import Interface.Prototype.Operations

-- Must fail in both modes: the representation is not a public equation (AT-FD-2).
example : Interface.Prototype.Carrier.{0} = ULift.{0} Nat := by
  rfl

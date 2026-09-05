/-! Discrete matrix cells used by the first implementation.
Cites: D-RT-25, D-RT-27, D-FD-01. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Kernel.Matrix
universe u v

abbrev Family (A B : Type u) := A → B → Type v

/-- The equality matrix acts as the unit source. -/
abbrev UnitCell {A : Type u} (M : Family.{u, v} A A) :=
  (a b : A) → a = b → M a b

/-- A binary multicell does not require a composite horizontal to exist. -/
abbrev BinaryCell {A B C : Type u}
    (M : Family.{u, v} A B) (N : Family.{u, v} B C) (P : Family.{u, v} A C) :=
  (a : A) → (b : B) → (c : C) → M a b × N b c → P a c

/-- The discrete monad fragment: a horizontal, unit and multiplication cells,
with the two unit laws and the associativity law for three input entries. -/
structure Monad (A : Type u) where
  hom : Family.{u, v} A A
  unit : UnitCell hom
  mul : BinaryCell hom hom hom
  unit_mul : ∀ (a b : A) (f : hom a b), mul a a b (unit a a rfl, f) = f
  mul_unit : ∀ (a b : A) (f : hom a b), mul a b b (f, unit b b rfl) = f
  mul_assoc : ∀ (a b c d : A) (f : hom a b) (g : hom b c) (h : hom c d),
    mul a c d (mul a b c (f, g), h) = mul a b d (f, mul b c d (g, h))

/-- Types and functions form a concrete matrix monad, with composition as multiplication. -/
def functions : Monad.{u+1, u} (Type u) where
  hom A B := A → B
  unit _A _B e := fun a => e ▸ a
  mul _ _ _ fg := fun a => fg.2 (fg.1 a)
  unit_mul _ _ _ := rfl
  mul_unit _ _ _ := rfl
  mul_assoc _ _ _ _ _ _ _ := rfl

end Kernel.Matrix

import Theory.Prototype.Monoid

/-! Preliminary signature checks for D-RT-27, D-CH-23 and AT-FD-1.
These are data signatures only: no VDC, Kan-space or Mod construction is asserted. -/
set_option autoImplicit false

universe u v w

namespace Prototype.Universes

abbrev Matrix (A B : Type u) : Type (max u (v + 1)) := A → B → Type v

structure CategoryData where
  Obj : Type u
  Hom : Obj → Obj → Type v

def matrix01 : Matrix.{0, 1} Nat Nat := fun _ _ => Type
def matrix11 : Matrix.{1, 1} Type Type := fun _ _ => Type
def matrix10 : Matrix.{1, 0} Type Type := fun _ _ => Nat

def category01 : CategoryData.{0, 1} := ⟨Nat, matrix01⟩
def category11 : CategoryData.{1, 1} := ⟨Type, matrix11⟩
def category10 : CategoryData.{1, 0} := ⟨Type, matrix10⟩

def setCategoryData : CategoryData.{u + 1, u} := ⟨Type u, fun A B => A → B⟩

def liftMatrix {A B : Type u} (M : Matrix.{u, v} A B) : Matrix.{u, max v w} A B :=
  fun a b => ULift.{w} (M a b)

theorem lift_down_up {A B : Type u} (M : Matrix.{u, v} A B)
    (a : A) (b : B) (x : M a b) : (ULift.up.{w} x).down = x := rfl

theorem lift_up_down {A B : Type u} (M : Matrix.{u, v} A B)
    (a : A) (b : B) (x : liftMatrix.{u, v, w} M a b) : ULift.up x.down = x := rfl

-- Exercise the complete sealed package and client proof at distinct carrier levels.
example := Theory.Prototype.product_append.{0}
example := Theory.Prototype.product_append.{1}
example := Theory.Prototype.product_append.{2}

end Prototype.Universes

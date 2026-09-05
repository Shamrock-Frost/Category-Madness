import Root.MatrixCategory

/-! Concrete implementation clients and size checks.
Cites: D-RT-25, D-RT-27, AT-FD-1, AT-RT-10. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Root.MatrixCategory

-- These equations belong on the implementation side of the seal.
example : functions.Hom Nat Bool = (Nat → Bool) := rfl
example : functions.id Nat 3 = 3 := rfl
example : functions.comp (fun n : Nat => n + 1) (fun n => n * 2) 3 = 8 := rfl
example : functions.comp (fun n : Nat => n * 2) (fun n => n + 1) 3 = 7 := rfl

-- Both directions of the construction retain independent object/entry universes.
example {A : Type 0} (M : Kernel.Matrix.Monad.{0, 1} A) :
    ofCategory (toCategory M) = M := ofCategory_toCategory M
example {A : Type 1} (M : Kernel.Matrix.Monad.{1, 1} A) :
    ofCategory (toCategory M) = M := ofCategory_toCategory M
example {A : Type 1} (M : Kernel.Matrix.Monad.{1, 0} A) :
    ofCategory (toCategory M) = M := ofCategory_toCategory M
example {A : Type 0} (C : Interface.Category.{0, 1} A) :
    toCategory (ofCategory C) = C := toCategory_ofCategory C
example {A : Type 1} (C : Interface.Category.{1, 1} A) :
    toCategory (ofCategory C) = C := toCategory_ofCategory C
example {A : Type 1} (C : Interface.Category.{1, 0} A) :
    toCategory (ofCategory C) = C := toCategory_ofCategory C

#print axioms Kernel.Matrix.functions
#print axioms toCategory_ofCategory
#print axioms ofCategory_toCategory
#print axioms functions_comp_apply

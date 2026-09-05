import Kernel.Matrix
import Interface.CategorySpec

/-! The ordinary-category comparison for the discrete matrix monad fragment.
This does not yet construct the augmented or higher root.
Cites: D-RT-25, D-RT-27, D-FD-01, AT-RT-10. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Root.MatrixCategory
universe u v
variable {A : Type u}

def toCategory (M : Kernel.Matrix.Monad.{u, v} A) : Interface.Category.{u, v} A where
  Hom := M.hom
  id a := M.unit a a rfl
  comp {a b c} f g := M.mul a b c (f, g)
  id_comp := M.unit_mul _ _
  comp_id := M.mul_unit _ _
  assoc := M.mul_assoc _ _ _ _

def ofCategory (C : Interface.Category.{u, v} A) : Kernel.Matrix.Monad.{u, v} A where
  hom := C.Hom
  unit a _b e := e ▸ C.id a
  mul _ _ _ fg := C.comp fg.1 fg.2
  unit_mul _ _ f := C.id_comp f
  mul_unit _ _ f := C.comp_id f
  mul_assoc _ _ _ _ f g h := C.assoc f g h

theorem toCategory_ofCategory (C : Interface.Category.{u, v} A) :
    toCategory (ofCategory C) = C := by cases C; rfl

theorem ofCategory_toCategory (M : Kernel.Matrix.Monad.{u, v} A) :
    ofCategory (toCategory M) = M := by
  have hu : (fun (a b : A) (e : a = b) => e ▸ M.unit a a rfl) = M.unit := by
    funext a b e
    cases e
    rfl
  cases M
  dsimp only [ofCategory, toCategory]
  congr 1

/-- A nonconstant, nontrivial example: objects are types and arrows are functions. -/
def functions : Interface.Category.{u+1, u} (Type u) :=
  toCategory Kernel.Matrix.functions

theorem functions_comp_apply {A B C : Type u} (f : A → B) (g : B → C) (a : A) :
    functions.comp f g a = g (f a) := rfl

end Root.MatrixCategory

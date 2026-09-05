import Interface.FunctionCategory

/-! Clients depend only on public specification fields and laws.
Cites: D-CH-14, D-CH-25, D-RT-28, AT-FD-2. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Theory
universe u v

/-- A left inverse and a right inverse of the same arrow coincide. -/
theorem inverse_unique {A : Type u} (C : Interface.Category.{u, v} A)
    {a b : A} (f : C.Hom a b) (g h : C.Hom b a)
    (fg : C.comp f g = C.id a) (hf : C.comp h f = C.id b) : g = h := by
  calc
    g = C.comp (C.id b) g := (C.id_comp g).symm
    _ = C.comp (C.comp h f) g := congrArg (fun k => C.comp k g) hf.symm
    _ = C.comp h (C.comp f g) := C.assoc h f g
    _ = C.comp h (C.id a) := congrArg (C.comp h) fg
    _ = h := C.comp_id h

theorem function_inverse_unique
    {a b : Interface.functionCategory.{u}.Obj}
    (f : Interface.functionCategory.category.Hom a b)
    (g h : Interface.functionCategory.category.Hom b a)
    (fg : Interface.functionCategory.category.comp f g = Interface.functionCategory.category.id a)
    (hf : Interface.functionCategory.category.comp h f = Interface.functionCategory.category.id b) :
    g = h := inverse_unique Interface.functionCategory.category f g h fg hf

end Theory

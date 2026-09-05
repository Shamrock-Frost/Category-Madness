/-! Transparent logical infrastructure; no implementation vocabulary.
Cites: D-CH-14, D-CH-25, D-RT-28, AT-FD-2. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Interface
universe u v

structure Category (A : Type u) where
  Hom : A → A → Type v
  id : (a : A) → Hom a a
  comp : {a b c : A} → Hom a b → Hom b c → Hom a c
  id_comp : ∀ {a b : A} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b : A} (f : Hom a b), comp f (id b) = f
  assoc : ∀ {a b c d : A} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)

-- Both levels occur in the bundle maximum, but remain independent in its fields.
set_option linter.checkUnivs false in
/-- Sealing this whole package hides the carrier and operations together with their laws. -/
structure CategorySpec where
  Obj : Type u
  category : Category.{u, v} Obj

end Interface

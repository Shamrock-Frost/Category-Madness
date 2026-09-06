import Mathlib.CategoryTheory.PathCategory.Basic

/-! Recover a category from evaluation of paths with the unit and flattening laws.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v u' v'

/-- The two path-evaluation laws needed to recover vertical composition. -/
structure PathEvaluation (V : Type u) [Quiver.{v} V] where
  eval : {a b : V} → Quiver.Path a b → (a ⟶ b)
  single : ∀ {a b : V} (f : a ⟶ b), eval f.toPath = f
  flatten : ∀ {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c),
    eval (p.comp q) = eval ((eval p).toPath.comp (eval q).toPath)

namespace PathEvaluation
variable {V : Type u} [Quiver.{v} V] (E : PathEvaluation V)

/-- A type synonym keeps the recovered category separate from the supplied quiver. -/
def Objects (_ : PathEvaluation V) := V

instance : Quiver.{v} E.Objects := inferInstanceAs (Quiver V)

private theorem flatten_left {a b c : V} (p : Quiver.Path a b) (g : b ⟶ c) :
    E.eval ((E.eval p).toPath.comp g.toPath) = E.eval (p.comp g.toPath) := by
  rw [E.flatten p g.toPath, E.single]

private theorem flatten_right {a b c : V} (f : a ⟶ b) (q : Quiver.Path b c) :
    E.eval (f.toPath.comp (E.eval q).toPath) = E.eval (f.toPath.comp q) := by
  rw [E.flatten f.toPath q, E.single]

instance category : Category.{v} E.Objects where
  id a := E.eval (Quiver.Path.nil (a := a))
  comp f g := E.eval (f.toPath.comp g.toPath)
  id_comp f := by
    erw [E.flatten_left, Quiver.Path.nil_comp, E.single]
  comp_id f := by
    erw [E.flatten_right, Quiver.Path.comp_nil, E.single]
  assoc f g h := by
    erw [E.flatten_left, E.flatten_right, Quiver.Path.comp_assoc]

/-- Path evaluation is functorial for the category it reconstructs. -/
def evaluation : Paths V ⥤ E.Objects where
  obj a := a
  map p := E.eval p
  map_id _ := rfl
  map_comp p q := E.flatten p q

/-- Generating edges are recovered exactly, including their endpoints. -/
theorem evaluation_single {a b : V} (f : a ⟶ b) :
    E.evaluation.map ((Paths.of V).map f) = f := E.single f

/-- Evaluation in the recovered category agrees with ordinary path composition. -/
theorem eval_eq_composePath {a b : E.Objects} (p : Quiver.Path a b) :
    E.eval p = composePath p := by
  induction p with
  | nil => rfl
  | cons p f ih =>
    change E.eval (p.comp f.toPath) = _
    erw [E.flatten, E.single]
    change E.eval p ≫ f = composePath p ≫ f
    erw [ih]

variable {W : Type u'} [Quiver.{v'} W] (D : PathEvaluation W)

/-- An edge map commuting with path evaluation is a functor of recovered categories. -/
def functorOfCompatible (F : V ⥤q W)
    (hF : ∀ {a b : V} (p : Quiver.Path a b),
      F.map (E.eval p) = D.eval (F.mapPath p)) : E.Objects ⥤ D.Objects where
  obj := F.obj
  map := F.map
  map_id a := hF (.nil (a := a))
  map_comp f g := by
    change F.map (E.eval (f.toPath.comp g.toPath)) =
      D.eval ((F.map f).toPath.comp (F.map g).toPath)
    exact (hF _).trans (congrArg D.eval (by rfl))

end PathEvaluation
end Kernel.Augmented

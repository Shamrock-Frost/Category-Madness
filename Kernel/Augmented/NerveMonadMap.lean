import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.EssentialImage

/-! The algebra-lifting lemma used by the monad-with-arities nerve proof.
This formalizes the comparison in Berger–Melliès–Weber, arXiv:1101.3064,
Proposition 1.3. It assumes the monad comparison laws, not the nerve conclusion.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category
namespace Kernel.Augmented.Nerve
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A monad morphism over a functor between possibly different base categories. -/
structure MonadMap (T : CategoryTheory.Monad C) (S : CategoryTheory.Monad D) (F : C ⥤ D) where
  comparison : F ⋙ S.toFunctor ⟶ T.toFunctor ⋙ F
  unit : ∀ X, S.η.app (F.obj X) ≫ comparison.app X = F.map (T.η.app X)
  mul : ∀ X, S.μ.app (F.obj X) ≫ comparison.app X =
    S.map (comparison.app X) ≫ comparison.app (T.obj X) ≫ F.map (T.μ.app X)

namespace MonadMap
variable {T : CategoryTheory.Monad C} {S : CategoryTheory.Monad D} {F : C ⥤ D}
  (M : MonadMap T S F)

@[reassoc] theorem naturality {X Y : C} (f : X ⟶ Y) :
    S.map (F.map f) ≫ M.comparison.app Y = M.comparison.app X ≫ F.map (T.map f) :=
  M.comparison.naturality f

/-- Apply the base functor and the comparison to a lawful algebra. -/
def lift : CategoryTheory.Monad.Algebra T ⥤ CategoryTheory.Monad.Algebra S where
  obj A :=
    { A := F.obj A.A
      a := M.comparison.app A.A ≫ F.map A.a
      unit := by
        rw [← assoc, M.unit, ← F.map_comp, A.unit]
        exact F.map_id _
      assoc := by
        dsimp
        rw [← assoc, M.mul]
        simp only [assoc, ← F.map_comp, A.assoc]
        rw [F.map_comp, S.map_comp]
        simp only [assoc]
        erw [← M.comparison.naturality_assoc A.a]
        rfl }
  map f :=
    { f := F.map f.f
      h := by
        dsimp
        rw [← assoc]
        erw [M.comparison.naturality f.f]
        simp only [Functor.comp_map, assoc, ← F.map_comp, f.h] }
  map_id A := by ext; exact F.map_id _
  map_comp f g := by ext; exact F.map_comp _ _

instance lift_faithful [F.Faithful] : M.lift.Faithful where
  map_injective h := CategoryTheory.Monad.Algebra.Hom.ext (F.map_injective (congrArg CategoryTheory.Monad.Algebra.Hom.f h))

/-- A pointwise epimorphic comparison reflects preservation of the algebra operation. -/
theorem reflects_hom [F.Faithful] [∀ X, Epi (M.comparison.app X)]
    {A B : CategoryTheory.Monad.Algebra T} (f : A.A ⟶ B.A)
    (h : S.map (F.map f) ≫ (M.comparison.app B.A ≫ F.map B.a) =
      (M.comparison.app A.A ≫ F.map A.a) ≫ F.map f) :
    T.map f ≫ B.a = A.a ≫ f := by
  apply F.map_injective
  apply (cancel_epi (M.comparison.app A.A)).mp
  simp only [F.map_comp, ← assoc]
  erw [← M.comparison.naturality f]
  simpa only [Functor.comp_obj, Functor.comp_map, assoc] using h

noncomputable instance lift_full [F.Full] [F.Faithful] [∀ X, Epi (M.comparison.app X)] :
    M.lift.Full where
  map_surjective f := by
    refine ⟨⟨F.preimage f.f, M.reflects_hom _ ?_⟩, ?_⟩
    · simpa only [lift, F.map_preimage] using f.h
    · ext
      exact F.map_preimage _

end MonadMap
end Kernel.Augmented.Nerve

import Kernel.Augmented.FreeArityNerve
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monad.Monadicity

/-! The restriction half of the free-arity nerve square is monadic.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.

This uses only the identity-on-objects arity-to-theory functor. It supplies no
arity density, exactness or diagram-model hypothesis.
-/

open CategoryTheory Opposite
noncomputable section
namespace Kernel.Augmented.Nerve
universe w
variable {C : Type w} [Category.{w} C] (i : C ⥤ Generating.Graph.{w})

instance : (restriction i).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have : ∀ c, IsIso (f.app c) := fun c =>
      inferInstanceAs (IsIso (((restriction i).map f).app (op (c.unop : C))))
    exact NatIso.isIso_of_isIso_app f

def restrictionAdjunction : (arityToTheory i).op.lan ⊣ restriction i :=
  (arityToTheory i).op.lanAdjunction (Type w)

def restrictionMonad : CategoryTheory.Monad (Cᵒᵖ ⥤ Type w) := (restrictionAdjunction i).toMonad

instance : Monad.PreservesColimitOfIsReflexivePair (restriction i) where
  out f g := by
    unfold restriction
    infer_instance

@[instance_reducible]
def restrictionMonadic : MonadicRightAdjoint (restriction i) :=
  Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms (restrictionAdjunction i)

instance : MonadicRightAdjoint (restriction i) := restrictionMonadic i

instance : (Monad.comparison (restrictionAdjunction i)).IsEquivalence := (restrictionMonadic i).eqv

/-- Presheaves on the free-arity theory are algebras for the restriction monad. -/
def restrictionMonadicEquivalence : ((Theory i)ᵒᵖ ⥤ Type w) ≌ (restrictionMonad i).Algebra :=
  (Monad.comparison (restrictionAdjunction i)).asEquivalence

end Kernel.Augmented.Nerve

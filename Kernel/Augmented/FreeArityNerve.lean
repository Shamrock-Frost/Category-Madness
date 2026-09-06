import Kernel.Augmented.GeneratingMonadicity
import Kernel.Augmented.NerveSquare
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Functor.KanExtension.Dense

/-! The free-arity theory and the actual augmented nerve restriction square.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.

The arity functor remains an explicit input. Its base density does not by itself
prove density of the free arities or the augmented nerve recognition condition.
-/

open CategoryTheory CategoryTheory.Presheaf Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Nerve
universe w
variable {C : Type w} [Category.{w} C] (i : C ⥤ Generating.Graph.{w})

/-- Free augmented algebras on the selected arities, with all algebra maps between them. -/
abbrev Theory := InducedCategory BundledAlgebra.{w} (fun c => BundledAlgebra.free.obj (i.obj c))

def theoryInclusion : Theory i ⥤ BundledAlgebra.{w} := inducedFunctor _

instance : (theoryInclusion i).Full := inferInstanceAs (inducedFunctor _).Full
instance : (theoryInclusion i).Faithful := inferInstanceAs (inducedFunctor _).Faithful

def arityToTheory : C ⥤ Theory i where
  obj c := c
  map f := InducedCategory.homMk (BundledAlgebra.free.map (i.map f))
  map_id c := by apply InducedCategory.hom_ext; simp
  map_comp f g := by apply InducedCategory.hom_ext; simp

def baseNerve : Generating.Graph.{w} ⥤ (Cᵒᵖ ⥤ Type w) := restrictedULiftYoneda.{w} i

def algebraNerve : BundledAlgebra.{w} ⥤ ((Theory i)ᵒᵖ ⥤ Type w) :=
  restrictedULiftYoneda.{w} (theoryInclusion i)

def restriction : ((Theory i)ᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w) :=
  (Functor.whiskeringLeft _ _ _).obj (arityToTheory i).op

private def restrictionIsoAt (A : BundledAlgebra.{w}) :
    (algebraNerve i ⋙ restriction i).obj A ≅ (BundledAlgebra.forget ⋙ baseNerve i).obj A :=
  NatIso.ofComponents (fun c =>
    { hom := ↾fun x => ULift.up (BundledAlgebra.freeForgetAdjunction.homEquiv (i.obj c.unop) A x.down)
      inv := ↾fun x => ULift.up ((BundledAlgebra.freeForgetAdjunction.homEquiv (i.obj c.unop) A).symm x.down)
      hom_inv_id := by ext ⟨x⟩; exact congrArg ULift.up ((BundledAlgebra.freeForgetAdjunction.homEquiv _ _).symm_apply_apply x)
      inv_hom_id := by ext ⟨x⟩; exact congrArg ULift.up ((BundledAlgebra.freeForgetAdjunction.homEquiv _ _).apply_symm_apply x) }) (by
    intro c d f
    ext ⟨x⟩
    exact congrArg ULift.up (BundledAlgebra.freeForgetAdjunction.homEquiv_naturality_left (i.map f.unop) x))

/-- Restricting an augmented nerve to the arities recovers the nerve of its generating graph. -/
def restrictionIso : algebraNerve i ⋙ restriction i ≅ BundledAlgebra.forget ⋙ baseNerve i :=
  NatIso.ofComponents (restrictionIsoAt i) (by
    intro A B F
    ext c ⟨x⟩
    exact congrArg ULift.up (BundledAlgebra.freeForgetAdjunction.homEquiv_naturality_right x F))

instance [i.IsDense] : (baseNerve i).Full := inferInstanceAs (restrictedULiftYoneda.{w} i).Full
instance [i.IsDense] : (baseNerve i).Faithful := inferInstanceAs (restrictedULiftYoneda.{w} i).Faithful

/-- Base density already makes the augmented nerve faithful; fullness needs the arity theorem. -/
instance [i.IsDense] : (algebraNerve i).Faithful := by
  have : (algebraNerve i ⋙ restriction i).Faithful := Functor.Faithful.of_iso (restrictionIso i).symm
  exact Functor.Faithful.of_comp (algebraNerve i) (restriction i)

/-- The base-nerve condition is necessary for every presheaf in the augmented nerve's image. -/
theorem restriction_mem_essImage {X : (Theory i)ᵒᵖ ⥤ Type w} (h : (algebraNerve i).essImage X) :
    (baseNerve i).essImage ((restriction i).obj X) := by
  rcases h with ⟨A, ⟨e⟩⟩
  exact ⟨BundledAlgebra.forget.obj A, ⟨(restrictionIso i).symm.app A ≪≫ (restriction i).mapIso e⟩⟩

end Kernel.Augmented.Nerve

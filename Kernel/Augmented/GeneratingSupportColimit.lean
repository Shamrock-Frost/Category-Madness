import Kernel.Augmented.GeneratingFiniteSupport
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Every generating presheaf is a filtered colimit of finite incidence subpresheaves.
Cites: D-KR-15, D-KR-18, AT-FD-7.

This supplies a finite incidence presentation of the base. Preservation by the
augmented generating monad, and the required arity exactness, are separate obligations.
-/

open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.Generating
universe w
variable (P : Presheaf.{w})

instance : IsFiltered (Finset (Element P)) := by
  classical
  exact isFiltered_of_semilatticeSup_nonempty _

/-- Finite generators ordered by inclusion, sent to their complete incidence closures. -/
def finiteSupportDiagram : Finset (Element P) ⥤ Presheaf.{w} where
  obj s := (finiteSupport P s).toFunctor
  map f := Subfunctor.homOfLe (finiteSupport_mono P (leOfHom f))
  map_id s := by ext; rfl
  map_comp f g := by ext; rfl

/-- Each term of the diagram has finitely many generators across all sorts combined. -/
instance (s : Finset (Element P)) : Finite (Element ((finiteSupportDiagram P).obj s)) :=
  finite_subfunctor_elements P (finiteSupport P s)

def finiteSupportCocone : Cocone (finiteSupportDiagram P) where
  pt := P
  ι :=
    { app s := (finiteSupport P s).ι
      naturality s t f := by
        ext
        rfl }

/-- Complete incidence closures cover every generator and identify overlaps in a finite union. -/
def finiteSupportIsColimit : IsColimit (finiteSupportCocone P) := by
  classical
  apply evaluationJointlyReflectsColimits
  intro U
  apply Types.FilteredColimit.isColimitOf
  · intro x
    exact ⟨{⟨U, x⟩}, ⟨x, mem_finiteSupport P _ x (by simp)⟩, rfl⟩
  · intro s t x y h
    refine ⟨s ∪ t, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
    exact Subtype.ext h

end Kernel.Augmented.Generating

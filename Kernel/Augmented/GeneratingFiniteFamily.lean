import Kernel.Augmented.GeneratingFinitePresentability
import Kernel.Augmented.ArityNerveComparison
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Category.ULift

/-! A small dense candidate family of finite generating incidence diagrams.
Cites: D-KR-15, D-KR-18, AT-FD-7.

Density and finite presentability are proved. The generating monad's arity
exactness is still required, and no minimal pasting or Reedy structure is asserted.
-/

open CategoryTheory Opposite Cardinal
noncomputable section
namespace Kernel.Augmented.Generating
universe w
attribute [local instance] fact_isRegular_aleph0

instance : IsCardinalLocallyPresentable Presheaf.{w} (ℵ₀ : Cardinal.{w}) := by
  let e : Presheaf.{w} ≌ ((AsSmall.{w} Shape)ᵒᵖ ⥤ Type w) :=
    Equivalence.congrLeft (show Shape ≌ AsSmall.{w} Shape from AsSmall.equiv).op
  exact e.symm.isCardinalLocallyPresentable ℵ₀

/-- A small model of all finite incidence presheaves, with every incidence-preserving map. -/
abbrev FiniteIncidence : Type w :=
  SmallModel.{w} (ObjectProperty.isFinitelyPresentable.{w} Presheaf.{w}).FullSubcategory

def finiteIncidenceInclusion : FiniteIncidence.{w} ⥤ Presheaf.{w} :=
  (equivSmallModel _).inverse ⋙ (ObjectProperty.isFinitelyPresentable.{w} Presheaf.{w}).ι

instance : finiteIncidenceInclusion.{w}.Full := by
  unfold finiteIncidenceInclusion
  infer_instance
instance : finiteIncidenceInclusion.{w}.Faithful := by
  unfold finiteIncidenceInclusion
  infer_instance
instance : finiteIncidenceInclusion.{w}.IsDense := by
  unfold finiteIncidenceInclusion
  infer_instance

theorem finiteIncidence_finite (a : FiniteIncidence.{w}) :
    Finite (Element (finiteIncidenceInclusion.obj a)) := by
  have : IsFinitelyPresentable.{w} (finiteIncidenceInclusion.obj a) :=
    ((equivSmallModel _).inverse.obj a).property
  exact finite_elements_of_finitelyPresentable _

/-- The same small dense family in the explicit generating graph category. -/
def finiteIncidenceGraphs : FiniteIncidence.{w} ⥤ Graph.{w} :=
  finiteIncidenceInclusion ⋙ Graph.presheafEquivalence.inverse

instance : finiteIncidenceGraphs.{w}.Full := by
  unfold finiteIncidenceGraphs
  infer_instance
instance : finiteIncidenceGraphs.{w}.Faithful := by
  unfold finiteIncidenceGraphs
  infer_instance
instance : finiteIncidenceGraphs.{w}.IsDense := by
  unfold finiteIncidenceGraphs
  infer_instance

/-- For this concrete candidate family, canonical-comparison invertibility suffices for fullness. -/
theorem finiteIncidenceNerve_full
    [∀ X, IsIso ((Nerve.arityMonadMap finiteIncidenceGraphs.{w}).comparison.app X)] :
    (Nerve.algebraNerve finiteIncidenceGraphs.{w}).Full :=
  Nerve.algebraNerve_full finiteIncidenceGraphs

theorem finiteIncidenceNerve_essImage_iff
    [∀ X, IsIso ((Nerve.arityMonadMap finiteIncidenceGraphs.{w}).comparison.app X)]
    (X : (Nerve.Theory finiteIncidenceGraphs.{w})ᵒᵖ ⥤ Type w) :
    (Nerve.algebraNerve finiteIncidenceGraphs).essImage X ↔
      (Nerve.baseNerve finiteIncidenceGraphs).essImage ((Nerve.restriction finiteIncidenceGraphs).obj X) :=
  Nerve.algebraNerve_essImage_iff finiteIncidenceGraphs X

end Kernel.Augmented.Generating

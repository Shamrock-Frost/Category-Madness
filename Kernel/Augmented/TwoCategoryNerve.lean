import Kernel.Augmented.TwoCategorySubstitution
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-! The discrete hom nerves in the strict 2-category comparison.
The augmented arity nerve is a separate construction.
Cites: D-KR-14, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Bicategory
namespace Kernel.Augmented.FromTwoCategory
universe u v c
variable {C : Type u} [Bicategory.{c,v} C] [Bicategory.Strict C]

/-- Extraction and reconstruction give isomorphic hom nerves in every simplicial degree. -/
def homNerveIso (a b : C) : nerve (RecoveredHom a b) ≅ nerve (a ⟶ b) := by
  let i : Cat.of (RecoveredHom a b) ≅ Cat.of (a ⟶ b) := {
    hom := Cat.Hom.ofFunctor (toOriginalHom a b)
    inv := Cat.Hom.ofFunctor (fromOriginalHom a b)
    hom_inv_id := rfl
    inv_hom_id := rfl
  }
  exact nerveFunctor.mapIso i

def homNerve_strictSegal (a b : C) : SSet.StrictSegal (nerve (RecoveredHom a b)) :=
  Nerve.strictSegal _

end Kernel.Augmented.FromTwoCategory

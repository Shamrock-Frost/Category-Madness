import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
import Mathlib.AlgebraicTopology.Reedy.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.SingleObj

/-! Checked dependency witnesses at the repository pin.
Cites: D-KR-14, D-KR-22, D-CH-24, AT-KR-0.
The scoped Quillen fibrations do not supply a simplicial-set model structure.
The negative probes describe this import closure, not a mathematical impossibility.
-/

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace Kernel.Foundations.Inventory
universe u v

theorem mappingSpace_kan (A X : SSet.{u}) [SSet.KanComplex X] :
    SSet.KanComplex ((ihom A).obj X) := inferInstance

theorem restriction_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (X : SSet.{u}) [SSet.KanComplex X] :
    Fibration ((MonoidalClosed.pre i).app X) := inferInstance

theorem nerve_strictSegal (C : Type u) [Category.{v} C] :
    SSet.IsStrictSegal (nerve C) := inferInstance

example : True := by
  fail_if_success have _ : CategoryWithWeakEquivalences SSet.{u} := inferInstance
  fail_if_success have _ : ModelCategory SSet.{u} := inferInstance
  trivial

example (G : Type u) [Groupoid.{v} G] : True := by
  fail_if_success have _ : SSet.KanComplex (nerve G) := inferInstance
  trivial

end Kernel.Foundations.Inventory

import Kernel.Augmented.GeneratingNestedSection

/-! Nested associativity for operations recovered from arbitrary generating-monad algebras.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

theorem assoc_law {s t : Nested.Side (Vertical A)} (r : Nested.NonemptyRow (cells A) s t)
    {a b : Vertical A} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath (horizontal A) a b)
    (χ : (cells A).Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    CellGraph.transport ((operations A).assoc_boundary r p q L) ((operations A).assocLeft r p q L χ) =
      (operations A).assocRight r p q L χ := by
  let r0 := generatorNestedNonemptyRow A r
  let χ0 : A.A.freeObject.cells.Cell (CellGraph.Row.outerBoundary r0.outer p.toPath q.toPath L) :=
    CellGraph.castInput (generatorNestedRow_outer_output A r.val).symm (generatorCell A χ)
  have hχ : (evaluationCells A).total (CellGraph.pack χ0) = CellGraph.pack χ := by
    unfold χ0
    erw [CellGraph.pack_castInput, generatorCell_evaluation]
  have houter : HEq ((evaluationCells A).row r0.outer.val) r.outer.val := by
    change HEq ((evaluationCells A).row (Nested.Row.outer (generatorNestedRow A r.val))) _
    rw [generatorNestedRow_outer]
    exact generatorRow_evaluation A (Nested.Row.outer r.val)
  have hinner : HEq ((evaluationCells A).row r0.inner.val) r.inner.val := by
    change HEq ((evaluationCells A).row (Nested.Row.inner (generatorNestedRow A r.val))) _
    rw [generatorNestedRow_inner]
    exact generatorRow_evaluation A (Nested.Row.inner r.val)
  have eouter := (evaluationOperations A).substitute_image r0.outer r.outer
    (generatorSide_evaluation A s.middle) (generatorSide_evaluation A t.middle) houter
    p.toPath q.toPath p q (heq_of_eq (evalPath_single A p)) (heq_of_eq (evalPath_single A q))
    L L (evaluationBase_shortPath A L) χ0 χ hχ
  have eright := (evaluationOperations A).substitute_image r0.inner r.inner
    (generatorSide_evaluation A s.upper) (generatorSide_evaluation A t.upper) hinner
    ((generatorNestedSide A s).lower ≫ p.toPath) ((generatorNestedSide A t).lower ≫ q.toPath)
    (s.lower ≫ p) (t.lower ≫ q) (HEq.refl _) (HEq.refl _) L L (evaluationBase_shortPath A L)
    (CellGraph.castInput (Nested.Row.inner_output r0.val).symm (A.A.freeAlgebra.substitute r0.outer p.toPath q.toPath L χ0))
    (CellGraph.castInput (Nested.Row.inner_output r.val).symm ((operations A).substitute r.outer p q L χ)) (by
      simpa only [CellGraph.pack_castInput] using eouter)
  have eleft := (evaluationOperations A).substitute_image
    (f := (generatorNestedSide A s).composite) (g := (generatorNestedSide A t).composite)
    (f' := s.composite) (g' := t.composite) (a := a) (b := b)
    (r0.composite A.A.freeAlgebra.toOperations) (r.composite (operations A))
    (generatorPost_evaluation A s.upper s.lower) (generatorPost_evaluation A t.upper t.lower)
    (generatorNestedRow_composite_evaluation A r.val)
    p.toPath q.toPath p q (heq_of_eq (evalPath_single A p)) (heq_of_eq (evalPath_single A q))
    L L (evaluationBase_shortPath A L)
    (CellGraph.castInput (Nested.Row.composite_output A.A.freeAlgebra.toOperations r0.val).symm χ0)
    (CellGraph.castInput (Nested.Row.composite_output (operations A) r.val).symm χ) (by
      simpa only [evaluationOperations, CellGraph.pack_castInput] using hχ)
  have hl := congrArg (fun x => (evaluationCells A).total (CellGraph.pack x))
    (A.A.freeAlgebra.laws.assoc r0 p.toPath q.toPath L χ0)
  erw [CellGraph.pack_transport] at hl
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  exact CellGraph.Total.cell_heq (eleft.symm.trans (hl.trans eright))

/-- Every algebra of the generating monad reconstructs a lawful augmented algebra. -/
def algebra : Algebra (cells A) where
  toOperations := operations A
  laws := ⟨verticalIdentity_stack_law A, leftUnit_law A, rightUnit_law A, insertion_law A, assoc_law A⟩

def reconstructed : BundledAlgebra.{w} where
  Obj := Vertical A
  vertical := inferInstance
  horizontal := horizontal A
  cells := cells A
  algebra := algebra A

end Kernel.Augmented.GeneratingMonadAlgebra

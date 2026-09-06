import Kernel.Augmented.GeneratingUnitLaws

/-! Identity insertion for operations recovered from arbitrary generating-monad algebras.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

theorem insertion_law {f g k : Side (Vertical A)} (p : (cells A).Row f g) (q : (cells A).Row g k)
    (hn : 0 < (p.comp q).length) {a b : Vertical A} (h : f.target ⟶ a) (l : k.target ⟶ b)
    (L : ShortPath (horizontal A) a b)
    (ψ : (cells A).Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    CellGraph.transport ((operations A).inserted_boundary p q hn h l L)
      ((operations A).insertedComposite p q hn h l L ψ) =
        (operations A).substitute ⟨p.comp q, hn⟩ h l L ψ := by
  let p0 := generatorRow A p
  let q0 := generatorRow A q
  have hn0 : 0 < (p0.comp q0).length := by
    change 0 < ((generatorRow A p).comp (generatorRow A q)).length
    rw [← generatorRow_comp, generatorRow_length]
    exact hn
  have eo : CellGraph.Row.output (p0.comp q0) = CellGraph.Row.output (p.comp q) := by
    change CellGraph.Row.output ((generatorRow A p).comp (generatorRow A q)) = _
    rw [← generatorRow_comp, generatorRow_output]
  let ψ0 : A.A.freeObject.cells.Cell (CellGraph.Row.outerBoundary ⟨p0.comp q0, hn0⟩ h.toPath l.toPath L) :=
    CellGraph.castInput eo.symm (generatorCell A ψ)
  have hψ : (evaluationCells A).total (CellGraph.pack ψ0) = CellGraph.pack ψ := by
    unfold ψ0
    erw [CellGraph.pack_castInput, generatorCell_evaluation]
  have hr : HEq ((evaluationCells A).row (p0.comp q0)) (p.comp q) := by
    change HEq ((evaluationCells A).row ((generatorRow A p).comp (generatorRow A q))) _
    rw [← generatorRow_comp]
    exact generatorRow_evaluation A (p.comp q)
  have hi : HEq ((evaluationCells A).row (A.A.freeAlgebra.insertedRow p0 q0).val)
      ((operations A).insertedRow p q).val := by
    apply (heq_of_eq ((evaluationOperations A).insertedRow p0 q0)).trans
    exact Operations.insertedRow_heq _ (generatorSide_evaluation A f) (generatorSide_evaluation A g)
      (generatorSide_evaluation A k) (generatorRow_evaluation A p) (generatorRow_evaluation A q)
  have hs := (evaluationOperations A).substitute_image ⟨p0.comp q0, hn0⟩ ⟨p.comp q, hn⟩
    (generatorSide_evaluation A f) (generatorSide_evaluation A k) hr
    h.toPath l.toPath h l (heq_of_eq (evalPath_single A h)) (heq_of_eq (evalPath_single A l))
    L L (evaluationBase_shortPath A L) ψ0 ψ hψ
  have hi' := (evaluationOperations A).substitute_image
    (A.A.freeAlgebra.insertedRow p0 q0) ((operations A).insertedRow p q)
    (generatorSide_evaluation A f) (generatorSide_evaluation A k) hi
    h.toPath l.toPath h l (heq_of_eq (evalPath_single A h)) (heq_of_eq (evalPath_single A l))
    L L (evaluationBase_shortPath A L)
    (CellGraph.castInput (A.A.freeAlgebra.insertedRow_output p0 q0).symm ψ0)
    (CellGraph.castInput ((operations A).insertedRow_output p q).symm ψ) (by
      exact (congrArg (evaluationCells A).total
        (CellGraph.pack_castInput (A.A.freeAlgebra.insertedRow_output p0 q0).symm ψ0)).trans
          (hψ.trans (CellGraph.pack_castInput ((operations A).insertedRow_output p q).symm ψ).symm))
  have hl := congrArg (fun x => (evaluationCells A).total (CellGraph.pack x))
    (A.A.freeAlgebra.laws.insertion p0 q0 hn0 h.toPath l.toPath L ψ0)
  erw [CellGraph.pack_transport] at hl
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  exact CellGraph.Total.cell_heq (hi'.symm.trans (hl.trans hs))

end Kernel.Augmented.GeneratingMonadAlgebra

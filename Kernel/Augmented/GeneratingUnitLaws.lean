import Kernel.Augmented.GeneratingCellSubstitution
import Kernel.Augmented.GlobalOperationImages

/-! Unit equations for operations recovered from arbitrary generating-monad algebras.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

theorem evaluation_shortIdentity {a b : A.A.Objects} (p : ShortPath A.A.freeHorizontal a b) :
    (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.shortIdentity p)) =
      CellGraph.pack ((operations A).shortIdentity p) := by
  apply ShortPath.cases_on (fun {_ _} p =>
    (evaluationCells A).total (CellGraph.pack (A.A.freeAlgebra.shortIdentity p)) =
      CellGraph.pack ((operations A).shortIdentity p))
  · intro a
    exact evaluationCells_verticalIdentity A (𝟙 (a : Paths A.A.Objects))
  · intro a b j
    exact evaluationCells_horizontalIdentity A j

theorem leftUnit_law {f g : Side (Vertical A)} {b : Boundary (horizontal A) f g}
    (φ : (cells A).Cell b) :
    CellGraph.transport (Operations.leftUnit_boundary φ) ((operations A).leftUnitComposite φ) = φ := by
  let φ0 := generatorCell A φ
  have hφ := generatorCell_evaluation A φ
  have hs := (evaluationOperations A).substitute_image
    (CellGraph.Row.single φ0) (CellGraph.Row.single φ)
    (generatorSide_evaluation A f) (generatorSide_evaluation A g)
    ((evaluationCells A).single_image φ0 φ (generatorSide_evaluation A f) (generatorSide_evaluation A g) hφ)
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (HEq.refl _) (HEq.refl _) b.output b.output
    (evaluationBase_shortPath A b.output)
    (CellGraph.castInput (CellGraph.Row.output_single φ0).symm (A.A.freeAlgebra.shortIdentity b.output))
    (CellGraph.castInput (CellGraph.Row.output_single φ).symm ((operations A).shortIdentity b.output)) (by
      erw [CellGraph.pack_castInput, CellGraph.pack_castInput]
      exact evaluation_shortIdentity A b.output)
  have hl := congrArg (fun x => (evaluationCells A).total (CellGraph.pack x)) (A.A.freeAlgebra.laws.leftUnit φ0)
  erw [CellGraph.pack_transport] at hl
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  exact CellGraph.Total.cell_heq (hs.symm.trans (hl.trans hφ))

theorem rightUnit_law {f g : Side (Vertical A)} {b : Boundary (horizontal A) f g}
    (φ : (cells A).Cell b) :
    CellGraph.transport ((operations A).rightUnit_boundary b) ((operations A).rightUnitComposite φ) = φ := by
  let φ0 := generatorCell A φ
  have hr : HEq ((evaluationCells A).row (A.A.freeAlgebra.identityRow b.input).val)
      ((operations A).identityRow b.input).val := by
    have h := (evaluationOperations A).identityRow b.input
    erw [evaluationBase_path] at h
    exact h
  have hs := (evaluationOperations A).substitute_image
    (A.A.freeAlgebra.identityRow b.input) ((operations A).identityRow b.input)
    ((evaluationBase A).side_identity f.source) ((evaluationBase A).side_identity g.source) hr
    f.arrow.toPath g.arrow.toPath f.arrow g.arrow (heq_of_eq (evalPath_single A f.arrow))
    (heq_of_eq (evalPath_single A g.arrow)) b.output b.output (evaluationBase_shortPath A b.output)
    (CellGraph.castInput (A.A.freeAlgebra.identityRow_output b.input).symm φ0)
    (CellGraph.castInput ((operations A).identityRow_output b.input).symm φ) (by
      erw [CellGraph.pack_castInput, CellGraph.pack_castInput]
      exact generatorCell_evaluation A φ)
  have hl := congrArg (fun x => (evaluationCells A).total (CellGraph.pack x)) (A.A.freeAlgebra.laws.rightUnit φ0)
  erw [CellGraph.pack_transport] at hl
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  exact CellGraph.Total.cell_heq (hs.symm.trans (hl.trans (generatorCell_evaluation A φ)))

theorem verticalIdentity_stack_law {a b d : Vertical A} (f : a ⟶ b) (g : b ⟶ d) :
    (operations A).verticalStack ((operations A).verticalIdentity f) ((operations A).verticalIdentity g) =
      (operations A).verticalIdentity (f ≫ g) := by
  have hf := evaluationCells_verticalIdentity A f.toPath
  have hg := evaluationCells_verticalIdentity A g.toPath
  erw [evalPath_single] at hf hg
  have hs := (evaluationOperations A).substitute_image
    (CellGraph.Row.single (A.A.freeAlgebra.verticalIdentity f.toPath))
    (CellGraph.Row.single ((operations A).verticalIdentity f))
    (generatorSide_evaluation A ⟨a, b, f⟩) (generatorSide_evaluation A ⟨a, b, f⟩)
    ((evaluationCells A).single_image _ _ (generatorSide_evaluation A ⟨a, b, f⟩)
      (generatorSide_evaluation A ⟨a, b, f⟩) hf)
    g.toPath g.toPath g g (heq_of_eq (evalPath_single A g)) (heq_of_eq (evalPath_single A g))
    (ShortPath.empty d) (ShortPath.empty d) rfl _ _ hg
  have hl := congrArg (fun x => (evaluationCells A).total (CellGraph.pack x))
    (A.A.freeAlgebra.laws.verticalIdentity_stack f.toPath g.toPath)
  apply eq_of_heq
  exact CellGraph.Total.cell_heq (hs.symm.trans
    (hl.trans (evaluationCells_verticalIdentity A (f.toPath.comp g.toPath))))

end Kernel.Augmented.GeneratingMonadAlgebra

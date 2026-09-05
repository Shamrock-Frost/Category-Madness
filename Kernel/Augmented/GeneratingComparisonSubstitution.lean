import Kernel.Augmented.GeneratingSectionSubstitution

/-! Evaluation-compatible graph maps preserve arbitrary augmented substitution.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating

theorem generatorSubstitution_evaluation (A : BundledAlgebra.{w})
    {f g : Side A.Obj} (r : A.cells.NonemptyRow f g) {a b : A.Obj}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.horizontal a b)
    (ψ : A.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    (evaluation A).total (CellGraph.pack ((forget.obj A).freeAlgebra.substitute
      (A.generatorNonemptyRow r) (A.generatorArrow h) (A.generatorArrow k)
      (A.generatorShortPath L) (A.generatorOuter r h k L ψ))) =
      CellGraph.pack (A.algebra.substitute r h k L ψ) := by
  have e := A.generatorInputs_evaluation (CellGraph.OverMap.id A.cells) A.algebra.toOperations r h k L ψ
  erw [← CellGraph.OverMap.comp_substituteImage, CellGraph.OverMap.comp_id,
    CellGraph.OverMap.id_substituteImage] at e
  exact ((evaluation A).substitute _ _ _ _ _).trans e

theorem comparisonCells_substitute {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F)
    {f g : Side A.Obj} (r : A.cells.NonemptyRow f g) {a b : A.Obj}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath A.horizontal a b)
    (ψ : A.cells.Cell (CellGraph.Row.outerBoundary r h k L)) :
    (comparisonCells F hF).total (CellGraph.pack (A.algebra.substitute r h k L ψ)) =
      (comparisonCells F hF).substituteImage B.algebra.toOperations r h k L ψ := by
  let r0 := A.generatorNonemptyRow r
  let h0 := A.generatorArrow h
  let k0 := A.generatorArrow k
  let L0 := A.generatorShortPath L
  let ψ0 := A.generatorOuter r h k L ψ
  let x := CellGraph.pack ((forget.obj A).freeAlgebra.substitute r0 h0 k0 L0 ψ0)
  calc
    _ = (comparisonCells F hF).total ((evaluation A).total x) :=
      congrArg (comparisonCells F hF).total (A.generatorSubstitution_evaluation r h k L ψ).symm
    _ = (Graph.lift F).total x := comparisonCells_evaluation F hF x
    _ = (Graph.lift F).toOverMap.substituteImage B.algebra.toOperations r0 h0 k0 L0 ψ0 :=
      (Graph.lift F).substitute _ _ _ _ _
    _ = ((evaluation A).toOverMap.comp (comparisonCells F hF)).substituteImage
        B.algebra.toOperations r0 h0 k0 L0 ψ0 := by
      rw [comparisonCells_factorization F hF]
      rfl
    _ = _ := ((evaluation A).toOverMap.comp_substituteImage (comparisonCells F hF)
      B.algebra.toOperations r0 h0 k0 L0 ψ0).trans
        (A.generatorInputs_evaluation (comparisonCells F hF) B.algebra.toOperations r h k L ψ)

/-- Recover the augmented-algebra map from a comparison morphism's evaluation equation. -/
def comparisonMap {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) : A ⟶ B where
  toOverMap := comparisonCells F hF
  horizontalIdentity := comparisonCells_horizontalIdentity F hF
  verticalIdentity := comparisonCells_verticalIdentity F hF
  substitute := comparisonCells_substitute F hF

theorem forget_comparisonMap {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) :
    forget.map (comparisonMap F hF) = F := comparisonCells_graphMap F hF

instance : generatingComparison.{w}.Full where
  map_surjective M := by
    refine ⟨comparisonMap M.f ((evaluationCompatible_iff M.f).mpr M.h), ?_⟩
    apply Monad.Algebra.Hom.ext
    exact forget_comparisonMap _ _

/-- The concrete monadicity comparison is fully faithful. Essential surjectivity remains separate. -/
def generatingComparisonFullyFaithful : generatingComparison.{w}.FullyFaithful :=
  .ofFullyFaithful _

instance : forget.{w}.ReflectsIsomorphisms where
  reflects {A B} f _ := by
    have : IsIso (generatingMonad.forget.map (generatingComparison.map f)) :=
      inferInstanceAs (IsIso (forget.map f))
    have : IsIso (generatingComparison.map f) :=
      isIso_of_reflects_iso _ generatingMonad.forget
    exact isIso_of_reflects_iso f generatingComparison

end Kernel.Augmented.BundledAlgebra

import Kernel.Augmented.CellTermRelations
import Kernel.Augmented.CellTermEvaluation
import Kernel.Augmented.AlgebraMaps

/-! The generated augmented equations are sound in every lawful algebra.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellTerm
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

theorem evaluate_related (A : Algebra K) (F : CellGraph.Map G K)
    {b : CellBoundary C H} {x y : CellTerm G b} (e : Related G x y) :
    evaluate A.toOperations F x = evaluate A.toOperations F y := by
  let E := evaluationMap A.toOperations F
  induction e with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | operation o x y h ih => exact congrArg (o.interpret A.toOperations) (funext ih)
  | verticalIdentity_stack f g =>
    change E.cell ((operations G).verticalStack ((operations G).verticalIdentity f)
      ((operations G).verticalIdentity g)) = E.cell ((operations G).verticalIdentity (f ≫ g))
    erw [E.verticalStack, E.verticalIdentity, E.verticalIdentity, E.verticalIdentity]
    exact A.laws.verticalIdentity_stack f g
  | leftUnit φ =>
    change E.cell _ = E.cell φ
    rw [E.leftUnitEquation]
    exact A.laws.leftUnit (E.cell φ)
  | rightUnit φ =>
    change E.cell _ = E.cell φ
    rw [E.rightUnitEquation]
    exact A.laws.rightUnit (E.cell φ)
  | insertion p q hn h l L ψ => exact E.insertion A.laws p q hn h l L ψ
  | assoc r p q L χ => exact E.assoc A.laws r p q L χ

end Kernel.Augmented.CellTerm

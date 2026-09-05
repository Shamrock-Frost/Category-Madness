import Kernel.Augmented.CellTermOperations
import Kernel.Augmented.OperationMaps

/-! Raw terms are free for the boundary-indexed operation signature.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellTerm
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

def evaluationMap (O : Operations K) (F : CellGraph.Map G K) : (operations G).Map O where
  toMap := evaluation O F
  map_operation o x := by
    change evaluate O F (o.interpret (operations G) x) = _
    erw [interpret_operations]
    rfl

theorem evaluationMap_unique (O : Operations K) (F : CellGraph.Map G K)
    (e : (operations G).Map O)
    (hg : ∀ {b : CellBoundary C H} (φ : G.family b), e.cell (.generator φ) = F.cell φ)
    {b : CellBoundary C H} (t : CellTerm G b) :
    e.cell t = (evaluationMap O F).cell t := by
  apply evaluate_unique O F (fun t => e.cell t) hg
  intro o x
  erw [← interpret_operations]
  exact e.map_operation o x

end Kernel.Augmented.CellTerm

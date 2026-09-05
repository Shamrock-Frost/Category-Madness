import Kernel.Augmented.FreeCells

/-! The free cell algebra's universal property, over fixed vertical/horizontal incidence.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

@[ext] theorem CellGraph.Map.ext (F F' : CellGraph.Map G K)
    (h : ∀ {f g : Side C} {b : Boundary H f g} (φ : G.Cell b), F.cell φ = F'.cell φ) : F = F' := by
  cases F; cases F'
  congr
  funext f g b φ
  exact h φ

@[ext] theorem Operations.Map.ext {O : Operations G} {O' : Operations K} (F F' : O.Map O')
    (h : ∀ {f g : Side C} {b : Boundary H f g} (φ : G.Cell b), F.cell φ = F'.cell φ) : F = F' := by
  have e : F.toMap = F'.toMap := CellGraph.Map.ext _ _ h
  cases F; cases F'; cases e; rfl

namespace CellTerm

def freeGenerators (G : CellGraph.{u,v,h,c} C H) : CellGraph.Map G (quotientGraph G) :=
  (generators G).comp (quotientMap G)

noncomputable def freeLiftEquiv (G : CellGraph.{u,v,h,c} C H) (A : Algebra K) :
    CellGraph.Map G K ≃ (freeAlgebra G).toOperations.Map A.toOperations where
  toFun F := quotientEvaluationMap A F
  invFun E := (freeGenerators G).comp E.toMap
  left_inv F := by
    apply CellGraph.Map.ext
    intro f g b φ
    rfl
  right_inv E := by
    apply Operations.Map.ext
    intro f g b φ
    exact (quotientEvaluation_unique A ((freeGenerators G).comp E.toMap) E (fun _ => rfl) (b := b.frame) φ).symm

end CellTerm
end Kernel.Augmented

import Kernel.Augmented.CellTermSoundness
import Kernel.Augmented.SignatureOperations

/-! Quotient terms and the descent of their interpretations into lawful algebras.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellTerm
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

def quotientGraph (G : CellGraph.{u,v,h,c} C H) : CellGraph C H where
  Cell b := Quotient (setoid G b.frame)

def quotientMap (G : CellGraph.{u,v,h,c} C H) : CellGraph.Map (graph G) (quotientGraph G) :=
  ⟨fun {_ _} {b} t => Quotient.mk (setoid G b.frame) t⟩

noncomputable def quotientInterpretation (G : CellGraph.{u,v,h,c} C H) :
    CellInterpretation (quotientGraph G) :=
  fun o x => Quotient.mk _ (.operation o (fun p => Quotient.out (x p)))

theorem quotientInterpretation_mk (o : CellOperation C H)
    (x : (p : o.Position) → CellTerm G (o.input p)) :
    quotientInterpretation G o (fun p => (quotientMap G).cell (x p)) =
      (quotientMap G).cell (.operation o x) := by
  apply Quotient.sound
  apply Related.operation
  intro p
  exact Quotient.exact (Quotient.out_eq (Quotient.mk (setoid G (o.input p)) (x p)))

noncomputable def quotientOperations (G : CellGraph.{u,v,h,c} C H) :
    Operations (quotientGraph G) := (quotientInterpretation G).operations

noncomputable def quotientOperationMap (G : CellGraph.{u,v,h,c} C H) :
    (operations G).Map (quotientOperations G) where
  toMap := quotientMap G
  map_operation o x := by
    change (quotientMap G).cell (o.interpret (operations G) x) =
      o.interpret (quotientInterpretation G).operations _
    erw [interpret_operations, CellInterpretation.interpret_operations]
    exact (quotientInterpretation_mk o x).symm

def quotientEvaluation (A : Algebra K) (F : CellGraph.Map G K) : CellGraph.Map (quotientGraph G) K where
  cell := Quotient.lift (evaluate A.toOperations F) (fun _ _ h => evaluate_related A F h)

noncomputable def quotientEvaluationMap (A : Algebra K) (F : CellGraph.Map G K) :
    (quotientOperations G).Map A.toOperations where
  toMap := quotientEvaluation A F
  map_operation o x := by
    change (quotientEvaluation A F).cell (o.interpret (quotientInterpretation G).operations x) = _
    erw [CellInterpretation.interpret_operations]
    change (o.interpret A.toOperations (fun p => evaluate A.toOperations F (Quotient.out (x p)))) = _
    apply congrArg (o.interpret A.toOperations)
    funext p
    exact congrArg (fun z : (quotientGraph G).family (o.input p) =>
      (quotientEvaluation A F).cell z) (Quotient.out_eq (x p))

theorem quotientEvaluation_unique (A : Algebra K) (F : CellGraph.Map G K)
    (E : (quotientOperations G).Map A.toOperations)
    (hg : ∀ {b : CellBoundary C H} (φ : G.family b),
      E.cell ((quotientMap G).cell (.generator φ)) = F.cell φ)
    {b : CellBoundary C H} (x : (quotientGraph G).family b) :
    E.cell x = (quotientEvaluation A F).cell x := by
  induction x using Quotient.inductionOn with
  | h t => exact evaluationMap_unique A.toOperations F ((quotientOperationMap G).comp E) hg t

end Kernel.Augmented.CellTerm

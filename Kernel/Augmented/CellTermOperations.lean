import Kernel.Augmented.CellTerms

/-! Compatibility of the raw term constructors with the incident operations.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellTerm
universe u v h c
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

theorem apply_operations (s : SubstitutionShape C H) (x : s.Inputs (graph G)) :
    (operations G).apply s x = substitutionNode s x := by
  have e := substitutionNode_transport (SubstitutionShape.ofRow_join s x)
    (SubstitutionShape.rowInputs (SubstitutionShape.joinedRow s x)
      s.lowerLeft s.lowerRight s.output
      (CellGraph.castInput (RowShape.join_output s.row x.1).symm x.2))
  rw [SubstitutionShape.inputs_split_join] at e
  unfold Operations.apply operations
  dsimp only
  erw [CellGraph.castInput_trans]
  exact e

theorem interpret_operations (o : CellOperation C H)
    (x : (p : o.Position) → CellTerm G (o.input p)) :
    o.interpret (operations G) x = operation o x := by
  cases o with
  | horizontalIdentity j =>
    apply congrArg (operation (.horizontalIdentity j))
    funext p
    exact PEmpty.elim p
  | verticalIdentity f =>
    apply congrArg (operation (.verticalIdentity f))
    funext p
    exact PEmpty.elim p
  | substitution s =>
    change (operations G).apply s _ = _
    erw [apply_operations]
    apply congrArg (operation (.substitution s))
    funext p
    cases p with
    | inl p => exact congrFun (RowShape.atPosition_collect (G := graph G) s.row (fun p => x (Sum.inl p))) p
    | inr p => cases p; rfl

end Kernel.Augmented.CellTerm

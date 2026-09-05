import Kernel.Augmented.OperationSignature

/-! Equivalence between incident operation data and its finitary signature.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

abbrev CellInterpretation (G : CellGraph.{u,v,h,c} C H) :=
  (o : CellOperation C H) → ((p : o.Position) → G.family (o.input p)) → G.family o.output

namespace CellInterpretation
variable (e : CellInterpretation G)

def substitution (s : SubstitutionShape C H) (x : s.Inputs G) : G.Cell s.result :=
  e (.substitution s) (Sum.rec (fun p => RowShape.atPosition s.row x.1 p) (fun _ => x.2))

theorem substitution_transport {s t : SubstitutionShape C H} (h : s = t) (x : s.Inputs G) :
    CellGraph.transport (congrArg (fun s => s.result.frame) h) (e.substitution s x) =
      e.substitution t (SubstitutionShape.Inputs.transport h x) := by cases h; rfl

def operations : Operations G where
  horizontalIdentity j := e (.horizontalIdentity j) (fun p => PEmpty.elim p)
  verticalIdentity f := e (.verticalIdentity ⟨_, _, f⟩) (fun p => PEmpty.elim p)
  substitute := by
    intro f g r a b h k L ψ
    exact CellGraph.castInput (G := G) (f := f.post h) (g := g.post k) (L := L)
      (CellGraph.Row.shape_input r.val)
      (e.substitution (SubstitutionShape.ofRow r h k L) (SubstitutionShape.rowInputs r h k L ψ))

theorem apply_operations (s : SubstitutionShape C H) (x : s.Inputs G) :
    e.operations.apply s x = e.substitution s x := by
  have h := e.substitution_transport (SubstitutionShape.ofRow_join s x)
    (SubstitutionShape.rowInputs (SubstitutionShape.joinedRow s x)
      s.lowerLeft s.lowerRight s.output
      (CellGraph.castInput (RowShape.join_output s.row x.1).symm x.2))
  rw [SubstitutionShape.inputs_split_join] at h
  unfold Operations.apply operations
  dsimp only
  erw [CellGraph.castInput_trans]
  exact h

theorem interpret_operations (o : CellOperation C H) (x : (p : o.Position) → G.family (o.input p)) :
    o.interpret e.operations x = e o x := by
  cases o with
  | horizontalIdentity j =>
    apply congrArg (e (.horizontalIdentity j))
    funext p
    exact PEmpty.elim p
  | verticalIdentity f =>
    apply congrArg (e (.verticalIdentity f))
    funext p
    exact PEmpty.elim p
  | substitution s =>
    change e.operations.apply s _ = _
    erw [apply_operations]
    apply congrArg (e (.substitution s))
    funext p
    cases p with
    | inl p => exact congrFun (RowShape.atPosition_collect (G := G) s.row (fun p => x (Sum.inl p))) p
    | inr p => cases p; rfl

end CellInterpretation
end Kernel.Augmented

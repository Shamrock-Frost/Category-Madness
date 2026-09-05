import Kernel.Augmented.OperationSignature
import Kernel.Augmented.Algebra

/-! Maps preserving the complete finitary operation signature.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c c' c''
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}
  {J : CellGraph.{u,v,h,c''} C H}

structure Operations.Map (O : Operations G) (O' : Operations K) extends CellGraph.Map G K where
  map_operation : ∀ (o : CellOperation C H) (x : (p : o.Position) → G.family (o.input p)),
    cell (o.interpret O x) = o.interpret O' (fun p => cell (x p))

namespace Operations.Map
variable {O : Operations G} {O' : Operations K} {O'' : Operations J}

def id (O : Operations G) : O.Map O := ⟨CellGraph.Map.id G, fun _ _ => rfl⟩

def comp (F : O.Map O') (F' : O'.Map O'') : O.Map O'' where
  toMap := F.toMap.comp F'.toMap
  map_operation o x := by
    change F'.cell (F.cell (o.interpret O x)) = _
    erw [F.map_operation, F'.map_operation]
    rfl

theorem horizontalIdentity (F : O.Map O') {a b : C} (j : H a b) :
    F.cell (O.horizontalIdentity j) = O'.horizontalIdentity j :=
  F.map_operation (.horizontalIdentity j) (fun p => PEmpty.elim p)

theorem verticalIdentity (F : O.Map O') {a b : C} (f : a ⟶ b) :
    F.cell (O.verticalIdentity f) = O'.verticalIdentity f :=
  F.map_operation (.verticalIdentity ⟨a, b, f⟩) (fun p => PEmpty.elim p)

theorem apply (F : O.Map O') (s : SubstitutionShape C H) (x : s.Inputs G) :
    F.cell (O.apply s x) = O'.apply s ⟨F.toMap.labels s.row x.1, F.cell x.2⟩ := by
  let args : (p : (CellOperation.substitution s).Position) →
      G.family ((CellOperation.substitution s).input p) :=
    Sum.rec (fun p => RowShape.atPosition s.row x.1 p) (fun _ => x.2)
  have e := F.map_operation (.substitution s) args
  dsimp only [CellOperation.interpret, args] at e
  erw [RowShape.collect_atPosition, ← RowShape.collect_map, RowShape.collect_atPosition] at e
  exact e

theorem substitute (F : O.Map O') {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)) :
    F.cell (O.substitute r h k L ψ) =
      CellGraph.castInput (G := K) (f := f.post h) (g := g.post k) (L := L)
        (F.toMap.row_input r.val)
        (O'.substitute (F.toMap.nonemptyRow r) h k L
          (CellGraph.castInput (F.toMap.row_output r.val).symm (F.cell ψ))) := by
  let s := SubstitutionShape.ofRow r h k L
  let x := SubstitutionShape.rowInputs r h k L ψ
  let y : s.Inputs K := ⟨F.toMap.labels s.row x.1, F.cell x.2⟩
  have er : SubstitutionShape.joinedRow s y = F.toMap.nonemptyRow r := by
    apply Subtype.ext
    exact (F.toMap.row_join (CellGraph.Row.shape r.val) (CellGraph.Row.labels r.val)).symm.trans
      (congrArg F.toMap.row (CellGraph.Row.join_shape_labels r.val))
  have e := congrArg
    (CellGraph.castInput (G := K) (f := f.post h) (g := g.post k) (L := L) (F.toMap.row_input r.val))
    (O'.substitute_transport er h k L
      (CellGraph.castInput (RowShape.join_output s.row y.1).symm y.2))
  erw [← O.apply_row r h k L ψ, F.toMap.castInput, F.apply]
  unfold Operations.apply
  dsimp only [s, x, y, SubstitutionShape.ofRow, SubstitutionShape.rowInputs] at e ⊢
  erw [F.toMap.castInput, CellGraph.castInput_trans] at e ⊢
  erw [CellGraph.castInput_trans, CellGraph.castInput_trans] at e
  exact e

end Operations.Map
end Kernel.Augmented

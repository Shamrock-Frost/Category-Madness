import Kernel.Augmented.CellTermEvaluation
import Mathlib.Data.Fintype.Sigma

/-! Every raw operation term has finitely many generator occurrences.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellTerm
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

def Leaf : {b : CellBoundary C H} → CellTerm G b → Type
  | _, .generator _ => Unit
  | _, .operation _ x => (p : _) × Leaf (x p)

instance leafFintype : {b : CellBoundary C H} → (t : CellTerm G b) → Fintype (Leaf t)
  | _, .generator _ => inferInstanceAs (Fintype Unit)
  | _, .operation o x => by
    let := fun p => leafFintype (x p)
    exact inferInstanceAs (Fintype ((p : o.Position) × Leaf (x p)))

def leafBoundary : {b : CellBoundary C H} → (t : CellTerm G b) → Leaf t → CellBoundary C H
  | b, .generator _ => fun _ => b
  | _, .operation _ x => fun l => leafBoundary (x l.1) l.2

def leafValue : {b : CellBoundary C H} → (t : CellTerm G b) → (l : Leaf t) → G.family (leafBoundary t l)
  | _, .generator φ => fun _ => φ
  | _, .operation _ x => fun l => leafValue (x l.1) l.2

theorem evaluate_eq_of_leaves (O : Operations K) (F F' : CellGraph.Map G K)
    {b : CellBoundary C H} (t : CellTerm G b)
    (h : ∀ l : Leaf t, F.cell (leafValue t l) = F'.cell (leafValue t l)) :
    evaluate O F t = evaluate O F' t := by
  induction t with
  | generator φ => exact h ()
  | operation o x ih =>
    apply congrArg (o.interpret O)
    funext p
    exact ih p (fun l => h ⟨p, l⟩)

end Kernel.Augmented.CellTerm

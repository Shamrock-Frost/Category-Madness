import Kernel.Augmented.RowPositions

/-! The finitary cell-operation signature over fixed vertical and horizontal incidence.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

abbrev CellBoundary (C : Type u) [Quiver.{v} C] (H : C → C → Type h) :=
  Σ f : Side C, Σ g : Side C, Boundary H f g

inductive CellOperation (C : Type u) [Category.{v} C] (H : C → C → Type h)
  | horizontalIdentity {a b : C} (j : H a b)
  | verticalIdentity (f : Side C)
  | substitution (s : SubstitutionShape C H)

namespace CellOperation
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def Position : CellOperation C H → Type
  | .horizontalIdentity _ => PEmpty
  | .verticalIdentity _ => PEmpty
  | .substitution s => RowShape.Position s.row ⊕ Unit

def output : CellOperation C H → CellBoundary C H
  | .horizontalIdentity j => (Boundary.horizontalIdentity j).frame
  | .verticalIdentity f => (Boundary.vertical (H := H) f.arrow f.arrow).frame
  | .substitution s => s.result.frame

def input : (o : CellOperation C H) → Position o → CellBoundary C H
  | .horizontalIdentity _ => fun p => PEmpty.elim p
  | .verticalIdentity _ => fun p => PEmpty.elim p
  | .substitution s => Sum.elim (RowShape.boundaryAt s.row) (fun _ => s.outer.frame)

instance positionFintype : (o : CellOperation C H) → Fintype o.Position
  | .horizontalIdentity _ => inferInstanceAs (Fintype PEmpty)
  | .verticalIdentity _ => inferInstanceAs (Fintype PEmpty)
  | .substitution s => inferInstanceAs (Fintype (RowShape.Position s.row ⊕ Unit))

def interpret (O : Operations G) : (o : CellOperation C H) →
    ((p : o.Position) → G.family (o.input p)) → G.family o.output
  | .horizontalIdentity j, _ => O.horizontalIdentity j
  | .verticalIdentity f, _ => O.verticalIdentity f.arrow
  | .substitution s, x => O.apply s ⟨RowShape.collect s.row (fun p => x (Sum.inl p)), x (Sum.inr ())⟩

end CellOperation
end Kernel.Augmented

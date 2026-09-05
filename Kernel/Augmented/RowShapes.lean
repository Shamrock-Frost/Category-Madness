import Kernel.Augmented.Incidence

/-! Row incidence independent of cell labels, with lossless split/join adapters.
This is a presentation of incident rows, not a canonical arity theorem.
Cites: D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

/-- The graph of boundaries, with no mathematical cell data. -/
abbrev ShapeGraph (C : Type u) [Quiver.{v} C] (H : C → C → Type h) : CellGraph C H where
  Cell _ := Unit

abbrev RowShape {C : Type u} [Quiver.{v} C] (H : C → C → Type h) (f g : Side C) :=
  (ShapeGraph C H).Row f g

namespace RowShape
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def input {f : Side C} : {g : Side C} → RowShape H f g → HPath H f.source g.source
  | _, .nil => .nil
  | _, .cons s e => (input s).comp e.1.input

def output {f : Side C} : {g : Side C} → RowShape H f g → HPath H f.target g.target
  | _, .nil => .nil
  | _, .cons s e => (output s).comp e.1.output.val

/-- One cell at each boundary of the supplied shape. -/
def Labels (G : CellGraph.{u,v,h,c} C H) {f : Side C} :
    {g : Side C} → RowShape H f g → Type c
  | _, .nil => PUnit
  | _, .cons s e => Labels G s × G.Cell e.1

def join {f : Side C} : {g : Side C} → (s : RowShape H f g) → Labels G s → G.Row f g
  | _, .nil, _ => .nil
  | _, .cons s e, labels => (join s labels.1).cons ⟨e.1, labels.2⟩

@[simp] theorem join_length {f g : Side C} (s : RowShape H f g) (labels : Labels G s) :
    (join s labels).length = s.length := by
  induction s with
  | nil => rfl
  | cons s e ih => exact congrArg Nat.succ (ih labels.1)

end RowShape

namespace CellGraph.Row
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def shape {f : Side C} : {g : Side C} → G.Row f g → RowShape H f g
  | _, .nil => .nil
  | _, .cons r e => (shape r).cons ⟨e.1, ()⟩

def labels {f : Side C} : {g : Side C} → (r : G.Row f g) → RowShape.Labels G (shape r)
  | _, .nil => PUnit.unit
  | _, .cons r e => (labels r, e.2)

@[simp] theorem shape_length {f g : Side C} (r : G.Row f g) : (shape r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

@[simp] theorem join_shape_labels {f g : Side C} (r : G.Row f g) :
    RowShape.join (shape r) (labels r) = r := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (RowShape.join (shape r) (labels r)).cons e = Quiver.Path.cons (V := G.Vertex) r e
    exact congrArg (fun p : G.Row _ _ => Quiver.Path.cons (V := G.Vertex) p e) ih

end CellGraph.Row

namespace RowShape
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

@[simp] theorem split_join {f g : Side C} (s : RowShape H f g) (labels : Labels G s) :
    (⟨CellGraph.Row.shape (join s labels), CellGraph.Row.labels (join s labels)⟩ :
      Σ t : RowShape H f g, Labels G t) = ⟨s, labels⟩ := by
  induction s with
  | nil => cases labels; rfl
  | @cons g k s e ih =>
    rcases e with ⟨b, e⟩
    cases e
    exact congrArg (fun t : Σ t : RowShape H f g, Labels G t =>
      (⟨Quiver.Path.cons (V := (ShapeGraph C H).Vertex) t.1 ⟨b, ()⟩, (t.2, labels.2)⟩ : Σ t : RowShape H f k, Labels G t))
      (ih labels.1)

/-- Splitting a row changes its representation without losing incidence or labels. -/
def rowEquiv (f g : Side C) : G.Row f g ≃ (Σ s : RowShape H f g, Labels G s) where
  toFun r := ⟨CellGraph.Row.shape r, CellGraph.Row.labels r⟩
  invFun s := join s.1 s.2
  left_inv := CellGraph.Row.join_shape_labels
  right_inv s := split_join s.1 s.2

@[simp] theorem shape_join {f g : Side C} (s : RowShape H f g) (x : Labels G s) :
    CellGraph.Row.shape (join s x) = s := congrArg Sigma.fst (split_join s x)

end RowShape
end Kernel.Augmented

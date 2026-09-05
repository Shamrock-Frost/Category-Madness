import Kernel.Augmented.Operations

/-! Identity rows, identity insertion and explicit input transport.
Reference: Koudenburg, arXiv:1910.11189v4, Definition 1.2.
Cites: D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

namespace CellGraph
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {f g : Side C}

/-- Transport only the input path, keeping all other incidence fixed. -/
def castInput {J K : HPath H f.source g.source} {L : ShortPath H f.target g.target}
    (e : J = K) (φ : G.Cell (⟨J, L⟩ : Boundary H f g)) :
    G.Cell (⟨K, L⟩ : Boundary H f g) :=
  (congrArg (fun p => G.Cell (⟨p, L⟩ : Boundary H f g)) e).mp φ

@[simp] theorem castInput_refl {b : Boundary H f g} (φ : G.Cell b) :
    castInput rfl φ = φ := rfl
end CellGraph

namespace Operations
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def shortIdentity (O : Operations G) {a b : C} (p : ShortPath H a b) :
    G.Cell (⟨p.val, p⟩ : Boundary H ⟨a, a, 𝟙 a⟩ ⟨b, b, 𝟙 b⟩) :=
  ShortPath.elim (fun {a b} p =>
    G.Cell (⟨p.val, p⟩ : Boundary H ⟨a, a, 𝟙 a⟩ ⟨b, b, 𝟙 b⟩))
    (fun a => O.verticalIdentity (𝟙 a)) (fun j => O.horizontalIdentity j) p

/-- One horizontal identity per input edge; this row may be empty. -/
def horizontalIdentities (O : Operations G) {a : C} :
    {b : C} → HPath H a b → G.Row ⟨a, a, 𝟙 a⟩ ⟨b, b, 𝟙 b⟩
  | _, .nil => .nil
  | _, .cons p j => (O.horizontalIdentities p).cons
      ⟨Boundary.horizontalIdentity j, O.horizontalIdentity j⟩

@[simp] theorem horizontalIdentities_length (O : Operations G) {a b : C}
    (p : HPath H a b) : (O.horizontalIdentities p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p j ih => exact congrArg Nat.succ ih

@[simp] theorem horizontalIdentities_input (O : Operations G) {a b : C}
    (p : HPath H a b) : CellGraph.Row.input (O.horizontalIdentities p) = p := by
  induction p with
  | nil => rfl
  | cons p j ih =>
    change (CellGraph.Row.input (O.horizontalIdentities p)).comp (HPath.single j) = (Quiver.Path.cons (V := Horizontal H) p j)
    rw [ih]
    rfl

@[simp] theorem horizontalIdentities_output (O : Operations G) {a b : C}
    (p : HPath H a b) : CellGraph.Row.output (O.horizontalIdentities p) = p := by
  induction p with
  | nil => rfl
  | cons p j ih =>
    change (CellGraph.Row.output (O.horizontalIdentities p)).comp (HPath.single j) = (Quiver.Path.cons (V := Horizontal H) p j)
    rw [ih]
    rfl

/-- The right-unit row; an empty input uses the vertical identity of its object. -/
def identityRow (O : Operations G) {a b : C} (p : HPath H a b) :
    G.NonemptyRow ⟨a, a, 𝟙 a⟩ ⟨b, b, 𝟙 b⟩ :=
  match p with
  | .nil => CellGraph.Row.single (O.verticalIdentity (𝟙 a))
  | .cons p j => ⟨O.horizontalIdentities (Quiver.Path.cons (V := Horizontal H) p j),
      lt_of_lt_of_eq (Nat.zero_lt_succ _)
        (O.horizontalIdentities_length (Quiver.Path.cons (V := Horizontal H) p j)).symm⟩

@[simp] theorem identityRow_input (O : Operations G) {a b : C} (p : HPath H a b) :
    CellGraph.Row.input (O.identityRow p).val = p := by
  cases p with
  | nil => rfl
  | cons p j => exact O.horizontalIdentities_input ((Quiver.Path.cons (V := Horizontal H) p j))

@[simp] theorem identityRow_output (O : Operations G) {a b : C} (p : HPath H a b) :
    CellGraph.Row.output (O.identityRow p).val = p := by
  cases p with
  | nil => rfl
  | cons p j => exact O.horizontalIdentities_output ((Quiver.Path.cons (V := Horizontal H) p j))

/-- Insert at a shared side; either neighbouring row may be empty. -/
def insertedRow (O : Operations G) {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) : G.NonemptyRow f k :=
  ⟨(p.cons ⟨Boundary.vertical g.arrow g.arrow, O.verticalIdentity g.arrow⟩).comp q, by
    exact lt_of_lt_of_eq (Nat.add_pos_left (Nat.zero_lt_succ p.length) q.length)
      (Quiver.Path.length_comp (V := G.Vertex)
        (p.cons ⟨Boundary.vertical g.arrow g.arrow, O.verticalIdentity g.arrow⟩) q).symm⟩

@[simp] theorem insertedRow_input (O : Operations G) {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) :
    CellGraph.Row.input (O.insertedRow p q).val = CellGraph.Row.input (p.comp q) := by
  change CellGraph.Row.input ((p.cons _).comp q) = _
  rw [CellGraph.Row.input_comp, CellGraph.Row.input_comp]
  rfl

@[simp] theorem insertedRow_output (O : Operations G) {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) :
    CellGraph.Row.output (O.insertedRow p q).val = CellGraph.Row.output (p.comp q) := by
  change CellGraph.Row.output ((p.cons _).comp q) = _
  rw [CellGraph.Row.output_comp, CellGraph.Row.output_comp]
  rfl

end Operations
end Kernel.Augmented

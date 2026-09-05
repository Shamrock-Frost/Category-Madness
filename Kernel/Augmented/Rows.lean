import Kernel.Augmented.RowShapes

/-! Incident rows and boundaries of substitution.
Reference: Koudenburg, arXiv:1910.11189v4, Definition 1.2, diagrams (3) and (4).
Cites: D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

namespace CellGraph.Row
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {f g k : Side C}

/-- The boundary is computed from the shape, without inspecting its cell labels. -/
def input {f g : Side C} (r : G.Row f g) : HPath H f.source g.source :=
  RowShape.input (shape r)

def output {f g : Side C} (r : G.Row f g) : HPath H f.target g.target :=
  RowShape.output (shape r)

@[simp] theorem input_nil (f : Side C) :
    input (G := G) (.nil : G.Row f f) = .nil := rfl

@[simp] theorem output_nil (f : Side C) :
    output (G := G) (.nil : G.Row f f) = .nil := rfl

@[simp] theorem input_cons (r : G.Row f g) (e : G.quiver.Hom g k) :
    input (r.cons e) = (input r).comp e.1.input := rfl

@[simp] theorem output_cons (r : G.Row f g) (e : G.quiver.Hom g k) :
    output (r.cons e) = (output r).comp e.1.output.val := rfl

@[simp] theorem input_comp (p : G.Row f g) (q : G.Row g k) :
    input (p.comp q) = (input p).comp (input q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (input (p.comp q)).comp e.1.input = (input p).comp ((input q).comp e.1.input)
    rw [ih]
    exact Quiver.Path.comp_assoc (V := Horizontal H) _ _ _

@[simp] theorem output_comp (p : G.Row f g) (q : G.Row g k) :
    output (p.comp q) = (output p).comp (output q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (output (p.comp q)).comp e.1.output.val =
      (output p).comp ((output q).comp e.1.output.val)
    rw [ih]
    exact Quiver.Path.comp_assoc (V := Horizontal H) _ _ _

/-- A row may contain many empty-output cells; they still count as cells. -/
theorem output_length_le (r : G.Row f g) : (output r).length ≤ r.length := by
  induction r with
  | nil => exact Nat.le_refl _
  | cons r e ih =>
    change ((output r).comp e.1.output.val).length ≤
      Quiver.Path.length (V := G.Vertex) r + 1
    calc
      _ = (output r).length + e.1.output.val.length :=
        Quiver.Path.length_comp (V := Horizontal H) _ _
      _ ≤ _ := Nat.add_le_add ih e.1.output.property

def single {b : Boundary H f g} (φ : G.Cell b) : G.NonemptyRow f g :=
  ⟨Quiver.Path.cons .nil ⟨b, φ⟩, Nat.zero_lt_succ _⟩

@[simp] theorem input_single {b : Boundary H f g} (φ : G.Cell b) :
    input (single φ).val = b.input := Quiver.Path.nil_comp (V := Horizontal H) _

@[simp] theorem output_single {b : Boundary H f g} (φ : G.Cell b) :
    output (single φ).val = b.output.val := Quiver.Path.nil_comp (V := Horizontal H) _

/-- Horizontal composition can only have a zero/one-output boundary. -/
def horizontalBoundary (r : G.NonemptyRow f g) (hr : (output r.val).length ≤ 1) :
    Boundary H f g := ⟨input r.val, ⟨output r.val, hr⟩⟩

end CellGraph.Row

namespace Side
variable {C : Type u} [Category.{v} C]

def post (f : Side C) {b : C} (h : f.target ⟶ b) : Side C :=
  ⟨f.source, b, f.arrow ≫ h⟩

@[simp] theorem post_id (f : Side C) : post f (𝟙 f.target) = f := by
  cases f
  simp [post]

theorem post_assoc (f : Side C) {b d : C} (h : f.target ⟶ b) (k : b ⟶ d) :
    post (post f h) k = post f (h ≫ k) := by
  simp [post, Category.assoc]
end Side

namespace CellGraph.Row
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {f g : Side C} {a b : C}

/-- The lower cell must accept the entire concatenated output path of the row. -/
def outerBoundary (r : G.NonemptyRow f g) (h : f.target ⟶ a)
    (k : g.target ⟶ b) (L : ShortPath H a b) :
    Boundary H ⟨f.target, a, h⟩ ⟨g.target, b, k⟩ :=
  ⟨output r.val, L⟩

/-- Boundary of substitution; vertical sides compose in the underlying category. -/
def compositeBoundary (r : G.NonemptyRow f g) (h : f.target ⟶ a)
    (k : g.target ⟶ b) (L : ShortPath H a b) :
    Boundary H (f.post h) (g.post k) :=
  ⟨input (f := f) (g := g) r.val, L⟩

@[simp] theorem composite_input (r : G.NonemptyRow f g) (h : f.target ⟶ a)
    (k : g.target ⟶ b) (L : ShortPath H a b) :
    (compositeBoundary r h k L).input = input r.val := rfl

@[simp] theorem composite_output (r : G.NonemptyRow f g) (h : f.target ⟶ a)
    (k : g.target ⟶ b) (L : ShortPath H a b) :
    (compositeBoundary r h k L).output = L := rfl

end CellGraph.Row
namespace RowShape
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

@[simp] theorem join_input {f g : Side C} (s : RowShape H f g) (labels : Labels G s) :
    CellGraph.Row.input (join s labels) = s.input := by
  induction s with
  | nil => rfl
  | cons s e ih => exact congrArg (fun p => p.comp e.1.input) (ih labels.1)

@[simp] theorem join_output {f g : Side C} (s : RowShape H f g) (labels : Labels G s) :
    CellGraph.Row.output (join s labels) = s.output := by
  induction s with
  | nil => rfl
  | cons s e ih => exact congrArg (fun p => p.comp e.1.output.val) (ih labels.1)

end RowShape

namespace CellGraph.Row
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

@[simp] theorem shape_input {f g : Side C} (r : G.Row f g) : (shape r).input = input r := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg (fun p => p.comp e.1.input) ih

@[simp] theorem shape_output {f g : Side C} (r : G.Row f g) : (shape r).output = output r := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg (fun p => p.comp e.1.output.val) ih

end CellGraph.Row

end Kernel.Augmented

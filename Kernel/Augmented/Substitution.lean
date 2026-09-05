import Kernel.Augmented.RowShapes
import Kernel.Augmented.Operations

/-! Substitution on separate incidence shapes and cell labels.
Boundary transport commutes with this operation by a single naturality lemma.
Cites: D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

/-- All the incidence of a substitution, independent of its cell labels. -/
structure SubstitutionShape (C : Type u) [Category.{v} C] (H : C → C → Type h) where
  left : Side C
  right : Side C
  row : RowShape H left right
  nonempty : 0 < row.length
  targetLeft : C
  targetRight : C
  lowerLeft : left.target ⟶ targetLeft
  lowerRight : right.target ⟶ targetRight
  output : ShortPath H targetLeft targetRight

namespace SubstitutionShape
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def outer (s : SubstitutionShape C H) :
    Boundary H ⟨s.left.target, s.targetLeft, s.lowerLeft⟩
      ⟨s.right.target, s.targetRight, s.lowerRight⟩ := ⟨s.row.output, s.output⟩

def result (s : SubstitutionShape C H) :
    Boundary H (s.left.post s.lowerLeft) (s.right.post s.lowerRight) :=
  ⟨s.row.input, s.output⟩

def Inputs (G : CellGraph.{u,v,h,c} C H) (s : SubstitutionShape C H) :=
  RowShape.Labels G s.row × G.Cell s.outer

def ofRow {f g : Side C} (r : G.NonemptyRow f g) {a b : C}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b) : SubstitutionShape C H :=
  ⟨f, g, CellGraph.Row.shape r.val, by simpa only [CellGraph.Row.shape_length] using r.property,
    a, b, h, k, L⟩

def rowInputs {f g : Side C} (r : G.NonemptyRow f g) {a b : C}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)) : (ofRow r h k L).Inputs G :=
  ⟨CellGraph.Row.labels r.val, CellGraph.castInput (CellGraph.Row.shape_output r.val).symm ψ⟩

def Inputs.transport {s t : SubstitutionShape C H} (e : s = t) (x : Inputs G s) : Inputs G t :=
  cast (congrArg (Inputs G) e) x

@[simp] theorem Inputs.transport_refl {s : SubstitutionShape C H} (x : Inputs G s) :
    Inputs.transport rfl x = x := rfl

@[simp] theorem Inputs.transport_trans {s t z : SubstitutionShape C H}
    (e : s = t) (e' : t = z) (x : Inputs G s) :
    Inputs.transport e' (Inputs.transport e x) = Inputs.transport (e.trans e') x := by
  cases e; cases e'
  rfl

end SubstitutionShape

namespace Operations
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

/-- A caller supplies a shape and its labels; the result boundary depends only on the shape. -/
def apply (O : Operations G) (s : SubstitutionShape C H) (x : s.Inputs G) : G.Cell s.result :=
  CellGraph.castInput (RowShape.join_input s.row x.1)
    (O.substitute ⟨RowShape.join s.row x.1, by simpa only [RowShape.join_length] using s.nonempty⟩
      s.lowerLeft s.lowerRight s.output
      (CellGraph.castInput (RowShape.join_output s.row x.1).symm x.2))

/-- All boundary transport for substitution is handled at the shape level. -/
theorem apply_transport (O : Operations G) {s t : SubstitutionShape C H}
    (e : s = t) (x : s.Inputs G) :
    CellGraph.transport (congrArg (fun s => s.result.frame) e) (O.apply s x) =
      O.apply t (SubstitutionShape.Inputs.transport e x) := by
  cases e
  rfl

/-- The shape API computes exactly the existing incident substitution. -/
theorem apply_row (O : Operations G) {f g : Side C} (r : G.NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)) :
    CellGraph.castInput (G := G) (f := f.post h) (g := g.post k) (L := L)
      (CellGraph.Row.shape_input r.val)
      (O.apply (SubstitutionShape.ofRow r h k L) (SubstitutionShape.rowInputs r h k L ψ)) =
      O.substitute r h k L ψ := by
  unfold apply SubstitutionShape.ofRow SubstitutionShape.rowInputs
  dsimp only
  have er : (⟨RowShape.join (CellGraph.Row.shape r.val) (CellGraph.Row.labels r.val),
      by simpa only [RowShape.join_length, CellGraph.Row.shape_length] using r.property⟩ :
      G.NonemptyRow f g) = r := Subtype.ext (CellGraph.Row.join_shape_labels r.val)
  erw [CellGraph.castInput_trans]
  erw [O.substitute_transport er h k L]
  erw [CellGraph.castInput_trans, CellGraph.castInput_trans]
  rfl

end Operations
end Kernel.Augmented

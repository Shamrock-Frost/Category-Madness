import Kernel.Augmented.PathPositions
import Kernel.Augmented.GlobalAlgebras
import Kernel.Augmented.GeneratingCategory

/-! Forget an augmented algebra to its generating incidence graph.
Cells retain their complete boundaries; arity selects the corresponding generator sort.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe w
namespace CellGraph
variable {C : Type w} [Category.{w} C] {H : C → C → Type w}
  (G : CellGraph.{w,w,w,w} C H)

abbrev ArityCell (n : ℕ) (ε : Bool) := {x : G.Total // x.1.2.2.arity = (n, ε.toNat)}

namespace ArityCell
variable {G} {n : ℕ} {ε : Bool} (x : G.ArityCell n ε)

def left : Side C := x.val.1.1
def right : Side C := x.val.1.2.1
def boundary : Boundary H x.left x.right := x.val.1.2.2

theorem input_length : x.boundary.input.length = n := congrArg Prod.fst x.property
theorem output_length : x.boundary.output.val.length = ε.toNat := congrArg Prod.snd x.property

open Generating

def vertex : Generating.Vertex n ε → C
  | .inl i => FinPath.vertexAt (C := Horizontal H) x.boundary.input i.val (by rw [x.input_length]; omega)
  | .inr i => FinPath.vertexAt (C := Horizontal H) x.boundary.output.val i.val (by rw [x.output_length]; omega)

def vertical (s : Bool) : FinPath.Edge C :=
  let f := if s then x.right else x.left
  ⟨f.source, f.target, f.arrow⟩

def horizontal : HorizontalEdge n ε → FinPath.Edge (Horizontal H)
  | .inl i => FinPath.edgeAt x.boundary.input i.val (by rw [x.input_length]; exact i.isLt)
  | .inr i => FinPath.edgeAt x.boundary.output.val i.val (by rw [x.output_length]; exact i.isLt)

private theorem vertexAt_length_eq {V : Type w} [Quiver.{w} V] {a b : V} (p : Quiver.Path a b)
    (n : ℕ) (hn : p.length = n) (h : n ≤ p.length) : FinPath.vertexAt p n h = b := by
  subst n
  exact FinPath.vertexAt_last p

theorem vertical_incidence (s e : Bool) :
    (if e then (x.vertical s).2.1 else (x.vertical s).1) =
      x.vertex (Generating.verticalEndpoint n ε s e) := by
  cases s <;> cases e
  · exact (FinPath.vertexAt_zero (C := Horizontal H) x.boundary.input).symm
  · exact (FinPath.vertexAt_zero (C := Horizontal H) x.boundary.output.val).symm
  · exact (vertexAt_length_eq (V := Horizontal H) x.boundary.input n x.input_length _).symm
  · exact (vertexAt_length_eq (V := Horizontal H) x.boundary.output.val ε.toNat x.output_length _).symm

theorem horizontal_incidence (i : HorizontalEdge n ε) (e : Bool) :
    (if e then (x.horizontal i).2.1 else (x.horizontal i).1) = x.vertex (edgeEndpoint i e) := by
  cases i with
  | inl i => cases e <;> first | exact FinPath.edgeAt_source _ _ _ | exact FinPath.edgeAt_target _ _ _
  | inr i => cases e <;> first | exact FinPath.edgeAt_source _ _ _ | exact FinPath.edgeAt_target _ _ _

end ArityCell

def underlyingGraph : Generating.Graph.{w} where
  Object := C
  Vertical := Generating.FinPath.Edge C
  Horizontal := Generating.FinPath.Edge (Horizontal H)
  Cell := G.ArityCell
  verticalEndpoint e f := if e then f.2.1 else f.1
  horizontalEndpoint e j := if e then j.2.1 else j.1
  cellVertex i x := x.vertex i
  cellVertical s x := x.vertical s
  cellHorizontal i x := x.horizontal i
  vertical_incidence s e x := x.vertical_incidence s e
  horizontal_incidence i e x := x.horizontal_incidence i e

end CellGraph
end Kernel.Augmented

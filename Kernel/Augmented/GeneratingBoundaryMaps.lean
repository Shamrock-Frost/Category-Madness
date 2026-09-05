import Kernel.Augmented.GeneratingGraphMaps
import Kernel.Augmented.PathPositionExt

/-! A map of generating presheaves matches the complete boundaries of cell assignments.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe w
namespace Side
variable {C : Type w} [Quiver.{w} C]

def edge (f : Side C) : Generating.FinPath.Edge C := ⟨f.source, f.target, f.arrow⟩

theorem edge_injective : Function.Injective (edge (C := C)) := by
  intro f g h
  exact congrArg (fun e : Generating.FinPath.Edge C => (⟨e.1, e.2.1, e.2.2⟩ : Side C)) h

end Side
private theorem shortPath_heq {C : Type w} {H : C → C → Type w} {a b a' b' : C}
    (p : ShortPath H a b) (q : ShortPath H a' b') (ha : a = a') (hb : b = b')
    (hp : HEq p.val q.val) : HEq p q := by
  cases ha; cases hb
  exact heq_of_eq (Subtype.ext (eq_of_heq hp))

namespace Generating.Graph
variable {G : Graph.{w}} {C : Type w} [Category.{w} C] {H : C → C → Type w}
  {Q : CellGraph.{w,w,w,w} C H} (F : G ⟶ Q.underlyingGraph)

private theorem mapped_side {n ε} (x : G.Cell n ε) (s : Bool) :
    (skeleton F).baseMap.side (G.freeSide x s) =
      (if s then (mapCell F x).right else (mapCell F x).left) := by
  apply Side.edge_injective
  change (⟨mapObject F _, mapObject F _, (skeleton F).baseMap.vertical.map
    ((Paths.of G.Objects).map (G.side x s).arrow)⟩ : FinPath.Edge C) = _
  rw [SkeletonAssignment.baseMap_generator]
  exact (skeleton_vertical F (G.side x s).arrow).trans (map_cellVertical F s x).symm

private theorem input_length {n ε} (x : G.Cell n ε) :
    ((skeleton F).baseMap.path (G.freeBoundary x).input).length = n := by
  rw [BaseMap.path_length]
  exact FinPath.length_ofEdges _ _ _

private theorem output_length {n ε} (x : G.Cell n ε) :
    ((skeleton F).baseMap.shortPath (G.freeBoundary x).output).val.length = ε.toNat := by
  change ((skeleton F).baseMap.path (G.freeBoundary x).output.val).length = _
  rw [BaseMap.path_length]
  exact FinPath.length_ofEdges _ _ _

private theorem input_edge {n ε} (x : G.Cell n ε) (i : Fin n) :
    FinPath.edgeAt ((skeleton F).baseMap.path (G.freeBoundary x).input) i.val
      (by rw [input_length F x]; exact i.isLt) = (mapCell F x).horizontal (.inl i) := by
  erw [FinPath.edgeAt_map]
  erw [FinPath.edgeAt_ofEdges]
  exact (skeleton_horizontal F (G.inputEdge x i)).trans (map_cellHorizontal F (.inl i) x).symm
  all_goals erw [FinPath.length_ofEdges]; exact i.isLt

private theorem output_edge {n ε} (x : G.Cell n ε) (i : Fin ε.toNat) :
    FinPath.edgeAt ((skeleton F).baseMap.shortPath (G.freeBoundary x).output).val i.val
      (by rw [output_length F x]; exact i.isLt) = (mapCell F x).horizontal (.inr i) := by
  erw [FinPath.edgeAt_map]
  erw [FinPath.edgeAt_ofEdges]
  exact (skeleton_horizontal F (G.outputEdge x i)).trans (map_cellHorizontal F (.inr i) x).symm
  all_goals erw [FinPath.length_ofEdges]; exact i.isLt

/-- Incidence naturality determines the full boundary required by the free mapping theorem. -/
theorem mapped_boundary {n ε} (x : G.Cell n ε) :
    ((skeleton F).baseMap.boundary (G.freeBoundary x)).frame = (mapCell F x).boundary.frame := by
  have hf := mapped_side F x false
  have hg := mapped_side F x true
  apply Boundary.frame_eq hf hg
  · apply FinPath.path_heq (C := Kernel.Augmented.Horizontal H) _ _ (congrArg (fun f : Side C => f.source) hf) (congrArg (fun f : Side C => f.source) hg)
      ((input_length F x).trans (mapCell F x).input_length.symm)
    intro i hi
    exact input_edge F x ⟨i, by erw [input_length F x] at hi; exact hi⟩
  · have e := FinPath.path_heq (C := Kernel.Augmented.Horizontal H)
      ((skeleton F).baseMap.shortPath (G.freeBoundary x).output).val (mapCell F x).boundary.output.val
      (congrArg (fun f : Side C => f.target) hf) (congrArg (fun f : Side C => f.target) hg)
      ((output_length F x).trans (mapCell F x).output_length.symm)
      (fun i hi => output_edge F x ⟨i, by erw [output_length F x] at hi; exact hi⟩)
    exact shortPath_heq _ _ (congrArg (fun f : Side C => f.target) hf) (congrArg (fun f : Side C => f.target) hg) e

def cellAssignment (F : G ⟶ Q.underlyingGraph) : CellAssignment G (skeleton F) (Q := Q) :=
  fun x => CellGraph.transport (G := Q) (mapped_boundary F x).symm (mapCell F x).val.2

end Generating.Graph
end Kernel.Augmented

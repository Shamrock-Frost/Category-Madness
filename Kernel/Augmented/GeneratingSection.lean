import Kernel.Augmented.GeneratingComparisonIdentities

/-! Choose incident generating representatives before free evaluation.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating
variable (A : BundledAlgebra.{w})

def generatorHorizontal : Horizontal A.horizontal ⥤q Horizontal (forget.obj A).freeHorizontal where
  obj a := a
  map {a b} j := ⟨⟨a, b, j⟩, rfl, rfl⟩

def generatorSide (f : Side A.Obj) : Side (forget.obj A).freeObject.Obj :=
  ⟨f.source, f.target, (Paths.of (forget.obj A).Objects).map (A.arrowGenerators.map f.arrow)⟩

def generatorBoundary {f g : Side A.Obj} (b : Boundary A.horizontal f g) :
    Boundary (forget.obj A).freeHorizontal (A.generatorSide f) (A.generatorSide g) where
  input := A.generatorHorizontal.mapPath b.input
  output := ⟨A.generatorHorizontal.mapPath b.output.val, by
    erw [FinPath.map_length]; exact b.output.property⟩

private theorem generator_side {n ε} (x : A.cells.ArityCell n ε) (s : Bool) :
    (forget.obj A).freeSide x s = A.generatorSide (if s then x.right else x.left) := by
  apply Side.edge_injective
  have h := (forget.obj A).unitCell_vertical x s
  cases s <;> exact h

private theorem generator_input_edge {n ε} (x : A.cells.ArityCell n ε) (i : Fin n) :
    FinPath.edgeAt ((forget.obj A).freeBoundary x).input i.val
      (by erw [FinPath.length_ofEdges]; exact i.isLt) =
    FinPath.edgeAt (A.generatorBoundary x.boundary).input i.val
      (by erw [FinPath.map_length]; rw [x.input_length]; exact i.isLt) := by
  erw [FinPath.edgeAt_map]
  exact (forget.obj A).unitCell_horizontal x (.inl i)

private theorem generator_output_edge {n ε} (x : A.cells.ArityCell n ε) (i : Fin ε.toNat) :
    FinPath.edgeAt ((forget.obj A).freeBoundary x).output.val i.val
      (by erw [FinPath.length_ofEdges]; exact i.isLt) =
    FinPath.edgeAt (A.generatorBoundary x.boundary).output.val i.val
      (by erw [FinPath.map_length]; rw [x.output_length]; exact i.isLt) := by
  erw [FinPath.edgeAt_map]
  exact (forget.obj A).unitCell_horizontal x (.inr i)

private theorem shortPath_heq {C : Type w} {H : C → C → Type w} {a b a' b' : C}
    (p : ShortPath H a b) (q : ShortPath H a' b') (ha : a = a') (hb : b = b')
    (hp : HEq p.val q.val) : HEq p q := by
  cases ha; cases hb
  exact heq_of_eq (Subtype.ext (eq_of_heq hp))

/-- The freely adjoined generator has the boundary obtained by lifting every incident edge. -/
theorem generator_boundary {n ε} (x : A.cells.ArityCell n ε) :
    ((forget.obj A).freeBoundary x).frame = (A.generatorBoundary x.boundary).frame := by
  have hf := A.generator_side x false
  have hg := A.generator_side x true
  apply Boundary.frame_eq hf hg
  · apply FinPath.path_heq (C := Horizontal (forget.obj A).freeHorizontal) _ _
      (congrArg (fun f : Side (forget.obj A).freeObject.Obj => f.source) hf)
      (congrArg (fun f : Side (forget.obj A).freeObject.Obj => f.source) hg)
      ((congrArg Prod.fst ((forget.obj A).freeBoundary_arity x)).trans
        ((FinPath.map_length A.generatorHorizontal x.boundary.input).trans x.input_length).symm)
    intro i hi
    exact A.generator_input_edge x ⟨i, by erw [FinPath.length_ofEdges] at hi; exact hi⟩
  · have e := FinPath.path_heq (C := Horizontal (forget.obj A).freeHorizontal)
      ((forget.obj A).freeBoundary x).output.val (A.generatorBoundary x.boundary).output.val
      (congrArg (fun f : Side (forget.obj A).freeObject.Obj => f.target) hf)
      (congrArg (fun f : Side (forget.obj A).freeObject.Obj => f.target) hg)
      ((congrArg Prod.snd ((forget.obj A).freeBoundary_arity x)).trans
        ((FinPath.map_length A.generatorHorizontal x.boundary.output.val).trans x.output_length).symm)
      (fun i hi => A.generator_output_edge x ⟨i, by erw [FinPath.length_ofEdges] at hi; exact hi⟩)
    exact shortPath_heq _ _
      (congrArg (fun f : Side (forget.obj A).freeObject.Obj => f.target) hf)
      (congrArg (fun f : Side (forget.obj A).freeObject.Obj => f.target) hg) e

def generatorCell {f g : Side A.Obj} {b : Boundary A.horizontal f g} (φ : A.cells.Cell b) :
    (forget.obj A).freeObject.cells.Cell (A.generatorBoundary b) :=
  CellGraph.transport (A.generator_boundary (CellGraph.pack φ).arityCell)
    ((forget.obj A).freeCell (CellGraph.pack φ).arityCell)

theorem generatorCell_evaluation {f g : Side A.Obj} {b : Boundary A.horizontal f g} (φ : A.cells.Cell b) :
    (evaluation A).total (CellGraph.pack (A.generatorCell φ)) = CellGraph.pack φ := by
  unfold generatorCell
  erw [CellGraph.pack_transport, evaluation_cell_generator]
  rfl

end Kernel.Augmented.BundledAlgebra

import Kernel.Augmented.GeneratingSection

/-! Incident row representatives for the global evaluation map.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating
variable (A : BundledAlgebra.{w})

def generatorPath {a b : A.Obj} (p : HPath A.horizontal a b) :
    HPath (forget.obj A).freeHorizontal a b := A.generatorHorizontal.mapPath p

def generatorShortPath {a b : A.Obj} (p : ShortPath A.horizontal a b) :
    ShortPath (forget.obj A).freeHorizontal a b :=
  ⟨A.generatorHorizontal.mapPath p.val, by erw [FinPath.map_length]; exact p.property⟩

def generatorRow (A : BundledAlgebra.{w}) {f : Side A.Obj} : {g : Side A.Obj} → A.cells.Row f g →
    (forget.obj A).freeObject.cells.Row (A.generatorSide f) (A.generatorSide g)
  | _, .nil => .nil
  | _, .cons r e => (A.generatorRow r).cons ⟨A.generatorBoundary e.1, A.generatorCell e.2⟩

theorem generatorRow_length {f g : Side A.Obj} (r : A.cells.Row f g) :
    (A.generatorRow r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

theorem generatorRow_output {f g : Side A.Obj} (r : A.cells.Row f g) :
    CellGraph.Row.output (A.generatorRow r) = A.generatorPath (CellGraph.Row.output r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (CellGraph.Row.output (A.generatorRow r)).comp
      (A.generatorHorizontal.mapPath e.1.output.val) = _
    erw [ih]
    exact (A.generatorHorizontal.mapPath_comp _ _).symm

def generatorNonemptyRow {f g : Side A.Obj} (r : A.cells.NonemptyRow f g) :
    (forget.obj A).freeObject.cells.NonemptyRow (A.generatorSide f) (A.generatorSide g) :=
  ⟨A.generatorRow r.val, by rw [A.generatorRow_length]; exact r.property⟩

theorem generatorSide_evaluation (f : Side A.Obj) :
    (evaluation A).base.side (A.generatorSide f) = f := by
  cases f with
  | mk a b f =>
    apply Side.edge_injective
    change (⟨a, b, (evaluation A).base.vertical.map
      ((Paths.of (forget.obj A).Objects).map (A.arrowGenerators.map f))⟩ : FinPath.Edge A.Obj) = _
    erw [evaluation_generator]
    rfl

theorem generatorPath_evaluation {a b : A.Obj} (p : HPath A.horizontal a b) :
    @Eq (HPath A.horizontal a b) ((evaluation A).base.path (D := A.Obj) (A.generatorPath p)) p := by
  induction p with
  | nil => rfl
  | cons p j ih =>
    change Quiver.Path.cons (V := Horizontal A.horizontal)
      ((evaluation A).base.path (A.generatorPath p)) j =
      Quiver.Path.cons (V := Horizontal A.horizontal) p j
    rw [ih]

theorem generatorShortPath_evaluation {a b : A.Obj} (p : ShortPath A.horizontal a b) :
    (evaluation A).base.shortPath (A.generatorShortPath p) = p :=
  Subtype.ext (A.generatorPath_evaluation p.val)

theorem generatorBoundary_evaluation {f g : Side A.Obj} (b : Boundary A.horizontal f g) :
    ((evaluation A).base.boundary (A.generatorBoundary b)).frame = b.frame :=
  Boundary.frame_eq (A.generatorSide_evaluation f) (A.generatorSide_evaluation g)
    (heq_of_eq (A.generatorPath_evaluation b.input))
    (heq_of_eq (A.generatorShortPath_evaluation b.output))

private theorem generatorRow_evaluation_heq {f g : Side A.Obj} (r : A.cells.Row f g) :
    HEq ((evaluation A).toOverMap.row (A.generatorRow r)) r := by
  induction r with
  | nil => exact CellGraph.Row.nil_heq (A.generatorSide_evaluation f)
  | @cons g k r e ih =>
    apply CellGraph.Row.cons_heq (A.generatorSide_evaluation f) (A.generatorSide_evaluation g)
      (A.generatorSide_evaluation k) ih (Boundary.heq_of_frame_eq (A.generatorBoundary_evaluation e.1))
    exact CellGraph.Total.cell_heq (((evaluation A).toOverMap.pack_cell _).trans
      (A.generatorCell_evaluation e.2))

private theorem packedRow_congr {f g f' g' : Side A.Obj} {r : A.cells.Row f g}
    {r' : A.cells.Row f' g'} (hf : f = f') (hg : g = g') (hr : HEq r r') :
    (⟨f, g, r⟩ : Σ f : Side A.Obj, Σ g : Side A.Obj, A.cells.Row f g) = ⟨f', g', r'⟩ := by
  cases hf; cases hg; cases eq_of_heq hr; rfl

/-- Evaluation recovers the whole incident row, including both outside sides. -/
theorem generatorRow_evaluation {f g : Side A.Obj} (r : A.cells.Row f g) :
    (⟨(evaluation A).base.side (A.generatorSide f), (evaluation A).base.side (A.generatorSide g),
      (evaluation A).toOverMap.row (A.generatorRow r)⟩ : Σ f : Side A.Obj, Σ g : Side A.Obj, A.cells.Row f g) =
      ⟨f, g, r⟩ :=
  packedRow_congr A (A.generatorSide_evaluation f) (A.generatorSide_evaluation g)
    (A.generatorRow_evaluation_heq r)

end Kernel.Augmented.BundledAlgebra

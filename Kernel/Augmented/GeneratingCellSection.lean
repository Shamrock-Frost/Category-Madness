import Kernel.Augmented.GeneratingCellAction
import Kernel.Augmented.GeneratingSectionRows

/-! Incident representatives for cells reconstructed from a generating-monad algebra.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

def generatorSide (f : Side (Vertical A)) : Side (Paths A.A.Objects) :=
  ⟨f.source, f.target, f.arrow.toPath⟩

def generatorBoundary {f g : Side (Vertical A)} (b : Boundary (horizontal A) f g) :
    Boundary A.A.freeHorizontal (generatorSide A f) (generatorSide A g) :=
  ⟨b.input, b.output⟩

def generatorFrame (b : CellBoundary (Vertical A) (horizontal A)) :
    CellBoundary (Paths A.A.Objects) A.A.freeHorizontal := (generatorBoundary A b.2.2).frame

def generatorCell {f g : Side (Vertical A)} {b : Boundary (horizontal A) f g}
    (φ : (cells A).Cell b) : A.A.freeObject.cells.Cell (generatorBoundary A b) :=
  CellGraph.transport (congrArg (generatorFrame A) φ.property) (A.A.freeCell φ.val.2.2)

theorem pack_generatorCell {f g : Side (Vertical A)} {b : Boundary (horizontal A) f g}
    (φ : (cells A).Cell b) :
    CellGraph.pack (generatorCell A φ) = CellGraph.pack (A.A.freeCell φ.val.2.2) :=
  CellGraph.pack_transport (congrArg (generatorFrame A) φ.property) _

def generatorTotal (x : (cells A).Total) : A.A.freeObject.cells.Total :=
  CellGraph.pack (generatorCell A x.2)

theorem generatorCell_congr {f g f' g' : Side (Vertical A)}
    {b : Boundary (horizontal A) f g} {b' : Boundary (horizontal A) f' g'}
    {φ : (cells A).Cell b} {ψ : (cells A).Cell b'} (h : CellGraph.pack φ = CellGraph.pack ψ) :
    CellGraph.pack (generatorCell A φ) = CellGraph.pack (generatorCell A ψ) :=
  congrArg (generatorTotal A) h

private theorem generator_transport {n ε} (x : A.A.Cell n ε)
    {f g : Side (Vertical A)} {b : Boundary (horizontal A) f g}
    (e : (A.A.boundary x).frame = b.frame) :
    CellGraph.transport (G := cells A) e (A.A.generator x) = ⟨⟨n, ε, x⟩, e⟩ := by
  have aux : ∀ (b' : CellBoundary (Vertical A) (horizontal A)) (h : (A.A.boundary x).frame = b'),
      cast (congrArg (cells A).family h) (A.A.generator x) =
        (⟨⟨n, ε, x⟩, h⟩ : (cells A).family b') := by
    intro b' h
    cases h
    rfl
  exact aux b.frame e

/-- The chosen free representative evaluates to the original incident cell. -/
theorem generatorCell_evaluation {f g : Side (Vertical A)} {b : Boundary (horizontal A) f g}
    (φ : (cells A).Cell b) :
    (evaluationCells A).total (CellGraph.pack (generatorCell A φ)) = CellGraph.pack φ := by
  rcases φ with ⟨⟨n, ε, x⟩, e⟩
  unfold generatorCell
  erw [CellGraph.pack_transport, evaluationCells_generator]
  exact (CellGraph.pack_transport (G := cells A) e (A.A.generator x)).symm.trans
    (congrArg CellGraph.pack (generator_transport A x e))

theorem generatorSide_evaluation (f : Side (Vertical A)) :
    (evaluationBase A).side (generatorSide A f) = f := by
  cases f with
  | mk a b f =>
    change Side.mk a b (evalPath A f.toPath) = Side.mk a b f
    rw [evalPath_single]

theorem evaluationBase_path {a b : A.A.Objects} (p : HPath A.A.freeHorizontal a b) :
    (evaluationBase A).path p = p := by
  induction p with
  | nil => rfl
  | cons p j ih =>
    exact congrArg (fun p => Quiver.Path.cons (V := Kernel.Augmented.Horizontal (horizontal A)) p j) ih

theorem evaluationBase_shortPath {a b : A.A.Objects} (p : ShortPath A.A.freeHorizontal a b) :
    (evaluationBase A).shortPath p = p := Subtype.ext (evaluationBase_path A p.val)

theorem generatorBoundary_evaluation {f g : Side (Vertical A)} (b : Boundary (horizontal A) f g) :
    ((evaluationBase A).boundary (generatorBoundary A b)).frame = b.frame :=
  Boundary.frame_eq (generatorSide_evaluation A f) (generatorSide_evaluation A g)
    (heq_of_eq (evaluationBase_path A b.input)) (heq_of_eq (evaluationBase_shortPath A b.output))

/-- Evaluation is surjective on cells together with their full boundaries. -/
theorem evaluationCells_surjective : Function.Surjective (evaluationCells A).total := by
  rintro ⟨⟨f, g, b⟩, φ⟩
  exact ⟨CellGraph.pack (generatorCell A φ), generatorCell_evaluation A φ⟩

def generatorRow {f : Side (Vertical A)} : {g : Side (Vertical A)} → (cells A).Row f g →
    A.A.freeObject.cells.Row (generatorSide A f) (generatorSide A g)
  | _, .nil => .nil
  | _, .cons r e => (generatorRow r).cons ⟨generatorBoundary A e.1, generatorCell A e.2⟩

theorem generatorRow_length {f g : Side (Vertical A)} (r : (cells A).Row f g) :
    (generatorRow A r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

theorem generatorRow_input {f g : Side (Vertical A)} (r : (cells A).Row f g) :
    CellGraph.Row.input (generatorRow A r) = CellGraph.Row.input r := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg (fun p => p.comp e.1.input) ih

theorem generatorRow_output {f g : Side (Vertical A)} (r : (cells A).Row f g) :
    CellGraph.Row.output (generatorRow A r) = CellGraph.Row.output r := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg (fun p => p.comp e.1.output.val) ih

def generatorNonemptyRow {f g : Side (Vertical A)} (r : (cells A).NonemptyRow f g) :
    A.A.freeObject.cells.NonemptyRow (generatorSide A f) (generatorSide A g) :=
  ⟨generatorRow A r.val, by rw [generatorRow_length]; exact r.property⟩

/-- Every cell and every shared vertical side in a row survives section and evaluation. -/
theorem generatorRow_evaluation {f g : Side (Vertical A)} (r : (cells A).Row f g) :
    HEq ((evaluationCells A).row (generatorRow A r)) r := by
  induction r with
  | nil => exact CellGraph.Row.nil_heq (generatorSide_evaluation A f)
  | @cons g k r e ih =>
    apply CellGraph.Row.cons_heq (generatorSide_evaluation A f) (generatorSide_evaluation A g)
      (generatorSide_evaluation A k) ih (Boundary.heq_of_frame_eq (generatorBoundary_evaluation A e.1))
    exact CellGraph.Total.cell_heq (((evaluationCells A).pack_cell _).trans
      (generatorCell_evaluation A e.2))

end Kernel.Augmented.GeneratingMonadAlgebra

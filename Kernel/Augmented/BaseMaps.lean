import Kernel.Augmented.OperationSignature
import Kernel.Augmented.Algebra
import Mathlib.CategoryTheory.Functor.Basic

/-! Maps of vertical categories and horizontal graphs, with complete incidence transport.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h u' v' h' c
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {H : C → C → Type h} {K : D → D → Type h'}

structure BaseMap (H : C → C → Type h) (K : D → D → Type h') where
  vertical : C ⥤ D
  horizontal : {a b : C} → H a b → K (vertical.obj a) (vertical.obj b)

namespace BaseMap
variable (F : BaseMap H K)

def horizontalPrefunctor : Horizontal H ⥤q Horizontal K where
  obj := F.vertical.obj
  map := F.horizontal

def side (f : Side C) : Side D := ⟨F.vertical.obj f.source, F.vertical.obj f.target, F.vertical.map f.arrow⟩

def path {a b : C} (p : HPath H a b) : HPath K (F.vertical.obj a) (F.vertical.obj b) :=
  F.horizontalPrefunctor.mapPath p

theorem path_length {a b : C} (p : HPath H a b) : (F.path p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p j ih => exact congrArg Nat.succ ih

theorem path_comp {a b d : C} (p : HPath H a b) (q : HPath H b d) :
    F.path (p.comp q) = (F.path p).comp (F.path q) := F.horizontalPrefunctor.mapPath_comp p q

def shortPath {a b : C} (p : ShortPath H a b) : ShortPath K (F.vertical.obj a) (F.vertical.obj b) :=
  ⟨F.path p.val, by rw [F.path_length]; exact p.property⟩

def boundary {f g : Side C} (b : Boundary H f g) : Boundary K (F.side f) (F.side g) :=
  ⟨F.path b.input, F.shortPath b.output⟩

def frame : CellBoundary C H → CellBoundary D K := fun b => (F.boundary b.2.2).frame

theorem side_post (f : Side C) {a : C} (h : f.target ⟶ a) :
    F.side (f.post h) = (F.side f).post (F.vertical.map h) := by
  cases f
  unfold side Side.post
  congr 1
  exact F.vertical.map_comp _ _

theorem side_identity (a : C) : F.side ⟨a, a, 𝟙 a⟩ = ⟨F.vertical.obj a, F.vertical.obj a, 𝟙 _⟩ := by
  unfold side
  rw [F.vertical.map_id]

def pullback (G : CellGraph.{u',v',h',c} D K) : CellGraph C H where
  Cell b := G.Cell (F.boundary b)

def row (F : BaseMap H K) {G : CellGraph.{u',v',h',c} D K} {f : Side C} :
    {g : Side C} → (F.pullback G).Row f g → G.Row (F.side f) (F.side g)
  | _, .nil => .nil
  | _, .cons r e => (F.row r).cons ⟨F.boundary e.1, e.2⟩

theorem row_length {G : CellGraph.{u',v',h',c} D K} {f g : Side C} (r : (F.pullback G).Row f g) :
    (F.row r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

theorem row_input {G : CellGraph.{u',v',h',c} D K} {f g : Side C} (r : (F.pullback G).Row f g) :
    CellGraph.Row.input (F.row r) = F.path (CellGraph.Row.input r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (CellGraph.Row.input (F.row r)).comp (F.path e.1.input) =
      F.path ((CellGraph.Row.input r).comp e.1.input)
    rw [ih, F.path_comp]
    rfl

theorem row_output {G : CellGraph.{u',v',h',c} D K} {f g : Side C} (r : (F.pullback G).Row f g) :
    CellGraph.Row.output (F.row r) = F.path (CellGraph.Row.output r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (CellGraph.Row.output (F.row r)).comp (F.path e.1.output.val) =
      F.path ((CellGraph.Row.output r).comp e.1.output.val)
    rw [ih, F.path_comp]
    rfl

def nonemptyRow {G : CellGraph.{u',v',h',c} D K} {f g : Side C}
    (r : (F.pullback G).NonemptyRow f g) : G.NonemptyRow (F.side f) (F.side g) :=
  ⟨F.row r.val, by rw [F.row_length]; exact r.property⟩

end BaseMap
end Kernel.Augmented

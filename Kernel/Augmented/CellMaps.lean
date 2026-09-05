import Kernel.Augmented.Substitution

/-! Maps of cell families over fixed vertical and horizontal incidence.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellGraph
universe u v h c c' c''
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}
  {J : CellGraph.{u,v,h,c''} C H}

/-- A map changes cell labels at each fixed complete boundary. -/
structure Map (G : CellGraph.{u,v,h,c} C H) (K : CellGraph.{u,v,h,c'} C H) where
  cell : {f g : Side C} → {b : Boundary H f g} → G.Cell b → K.Cell b

namespace Map

def id (G : CellGraph.{u,v,h,c} C H) : Map G G := ⟨fun φ => φ⟩

def comp (F : Map G K) (F' : Map K J) : Map G J := ⟨fun φ => F'.cell (F.cell φ)⟩

@[simp] theorem transport (F : Map G K) {f g f' g' : Side C}
    {b : Boundary H f g} {b' : Boundary H f' g'} (e : b.frame = b'.frame) (φ : G.Cell b) :
    F.cell (CellGraph.transport e φ) = CellGraph.transport e (F.cell φ) := by
  have aux : ∀ {x y : Σ f : Side C, Σ g : Side C, Boundary H f g}
      (e : x = y) (φ : G.family x),
      F.cell (cast (congrArg G.family e) φ) = cast (congrArg K.family e) (F.cell φ) := by
    intro x y e φ
    cases e
    rfl
  exact aux e φ

@[simp] theorem castInput (F : Map G K) {f g : Side C}
    {p q : HPath H f.source g.source} {L : ShortPath H f.target g.target}
    (e : p = q) (φ : G.Cell (⟨p, L⟩ : Boundary H f g)) :
    F.cell (CellGraph.castInput e φ) = CellGraph.castInput e (F.cell φ) := by
  cases e
  rfl

def row (F : Map G K) {f : Side C} : {g : Side C} → G.Row f g → K.Row f g
  | _, .nil => .nil
  | _, .cons r e => (F.row r).cons ⟨e.1, F.cell e.2⟩

@[simp] theorem row_length (F : Map G K) {f g : Side C} (r : G.Row f g) :
    (F.row r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

@[simp] theorem row_shape (F : Map G K) {f g : Side C} (r : G.Row f g) :
    Row.shape (F.row r) = Row.shape r := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (Row.shape (F.row r)).cons _ = (Row.shape r).cons _
    rw [ih]

@[simp] theorem row_input (F : Map G K) {f g : Side C} (r : G.Row f g) :
    Row.input (F.row r) = Row.input r := congrArg RowShape.input (F.row_shape r)

@[simp] theorem row_output (F : Map G K) {f g : Side C} (r : G.Row f g) :
    Row.output (F.row r) = Row.output r := congrArg RowShape.output (F.row_shape r)

def nonemptyRow (F : Map G K) {f g : Side C} (r : G.NonemptyRow f g) : K.NonemptyRow f g :=
  ⟨F.row r.val, by simpa only [row_length] using r.property⟩

def labels (F : Map G K) {f : Side C} : {g : Side C} → (s : RowShape H f g) →
    RowShape.Labels G s → RowShape.Labels K s
  | _, .nil, _ => PUnit.unit
  | _, .cons s _, x => ⟨F.labels s x.1, F.cell x.2⟩

@[simp] theorem row_join (F : Map G K) {f g : Side C} (s : RowShape H f g)
    (x : RowShape.Labels G s) : F.row (RowShape.join s x) = RowShape.join s (F.labels s x) := by
  induction s with
  | nil => rfl
  | cons s e ih =>
    change (F.row (RowShape.join s x.1)).cons _ = (RowShape.join s (F.labels s x.1)).cons _
    rw [ih]
    rfl

end Map
end Kernel.Augmented.CellGraph

import Kernel.Augmented.CellMaps
import Mathlib.Data.Fintype.Sum

/-! Finite cell positions of an incident row, retaining each position's full boundary.
These are inputs of an operation, not yet objects of an arity category.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.RowShape
universe u v h c
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def Position {f : Side C} : {g : Side C} → RowShape H f g → Type
  | _, .nil => PEmpty
  | _, .cons s _ => Position s ⊕ Unit

def boundaryAt {f : Side C} : {g : Side C} → (s : RowShape H f g) →
    Position s → (Σ f : Side C, Σ g : Side C, Boundary H f g)
  | _, .nil => fun p => PEmpty.elim p
  | _, .cons s e => Sum.elim (boundaryAt s) (fun _ => e.1.frame)

instance positionFintype {f : Side C} : {g : Side C} → (s : RowShape H f g) → Fintype (Position s)
  | _, .nil => inferInstanceAs (Fintype PEmpty)
  | _, .cons s _ => by
      let := positionFintype s
      exact inferInstanceAs (Fintype (Position s ⊕ Unit))

def atPosition {f : Side C} : {g : Side C} → (s : RowShape H f g) → Labels G s →
    (p : Position s) → G.family (boundaryAt s p)
  | _, .nil, _ => fun p => PEmpty.elim p
  | _, .cons s e, x => by
      intro p
      cases p with
      | inl p => exact atPosition s x.1 p
      | inr _ => exact x.2

def collect {f : Side C} : {g : Side C} → (s : RowShape H f g) →
    ((p : Position s) → G.family (boundaryAt s p)) → Labels G s
  | _, .nil, _ => PUnit.unit
  | _, .cons s _, x => ⟨collect s (fun p => x (Sum.inl p)), x (Sum.inr ())⟩

@[simp] theorem collect_atPosition {f g : Side C} (s : RowShape H f g) (x : Labels G s) :
    collect s (atPosition s x) = x := by
  induction s with
  | nil => cases x; rfl
  | cons s e ih => exact congrArg (fun y => (y, x.2)) (ih x.1)

@[simp] theorem atPosition_collect {f g : Side C} (s : RowShape H f g)
    (x : (p : Position s) → G.family (boundaryAt s p)) : atPosition s (collect s x) = x := by
  funext p
  induction s with
  | nil => exact PEmpty.elim p
  | cons s e ih =>
    cases p with
    | inl p => exact ih _ p
    | inr p => cases p; rfl

/-- The row's dependent product is exactly its finite family of typed cell positions. -/
def positionEquiv {f g : Side C} (s : RowShape H f g) :
    Labels G s ≃ ((p : Position s) → G.family (boundaryAt s p)) where
  toFun := atPosition s
  invFun := collect s
  left_inv := collect_atPosition s
  right_inv := atPosition_collect s

theorem collect_map {K : CellGraph C H} (F : CellGraph.Map G K) {f g : Side C}
    (s : RowShape H f g) (x : (p : Position s) → G.family (boundaryAt s p)) :
    F.labels s (collect s x) = collect s (fun p => F.cell (x p)) := by
  induction s with
  | nil => rfl
  | cons s e ih => exact congrArg (fun y => (y, F.cell (x (Sum.inr ())))) (ih _)

end Kernel.Augmented.RowShape

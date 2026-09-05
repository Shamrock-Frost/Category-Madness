import Kernel.Augmented.GeneratingCells

/-! Ordered vertices and edges of an incident path, including its two endpoints.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating.FinPath
universe u v u' v'
variable {C : Type u} [Quiver.{v} C] {D : Type u'} [Quiver.{v'} D]

abbrev Edge (C : Type u) [Quiver.{v} C] := Σ a : C, Σ b : C, a ⟶ b

def vertexAt {a : C} : {b : C} → (p : Quiver.Path a b) → (i : ℕ) → i ≤ p.length → C
  | _, .nil, _, _ => a
  | b, .cons p _, i, _ => if h : i ≤ p.length then vertexAt p i h else b

def edgeAt {a : C} : {b : C} → (p : Quiver.Path a b) → (i : ℕ) → i < p.length → Edge C
  | _, .nil, _, h => False.elim (Nat.not_lt_zero _ h)
  | _, .cons p e, i, _ => if h : i < p.length then edgeAt p i h else ⟨_, _, e⟩

@[simp] theorem vertexAt_zero {a b : C} (p : Quiver.Path a b) : vertexAt p 0 (Nat.zero_le _) = a := by
  induction p with
  | nil => rfl
  | cons p e ih => simpa only [vertexAt, dif_pos (Nat.zero_le _)] using ih

@[simp] theorem vertexAt_last {a b : C} (p : Quiver.Path a b) : vertexAt p p.length (Nat.le_refl _) = b := by
  cases p with
  | nil => rfl
  | cons p e => simp only [Quiver.Path.length, vertexAt, Nat.not_succ_le_self, ↓reduceDIte]

theorem edgeAt_source {a b : C} (p : Quiver.Path a b) (i : ℕ) (hi : i < p.length) :
    (edgeAt p i hi).1 = vertexAt p i (Nat.le_of_lt hi) := by
  induction p with
  | nil => exact False.elim (Nat.not_lt_zero i hi)
  | cons p e ih =>
    by_cases h : i < p.length
    · simpa only [edgeAt, vertexAt, dif_pos h, dif_pos (Nat.le_of_lt h)] using ih h
    · have eq : i = p.length := by
        simp only [Quiver.Path.length] at hi
        omega
      subst i
      simp only [edgeAt, Nat.lt_irrefl, ↓reduceDIte, vertexAt, le_refl, vertexAt_last]

theorem edgeAt_target {a b : C} (p : Quiver.Path a b) (i : ℕ) (hi : i < p.length) :
    (edgeAt p i hi).2.1 = vertexAt p (i + 1) hi := by
  induction p with
  | nil => exact False.elim (Nat.not_lt_zero i hi)
  | cons p e ih =>
    by_cases h : i < p.length
    · rw [edgeAt, dif_pos h, vertexAt, dif_pos (show i + 1 ≤ p.length from h)]
      exact ih h
    · have eq : i = p.length := by
        simp only [Quiver.Path.length] at hi
        omega
      subst i
      rw [edgeAt, dif_neg (Nat.lt_irrefl _), vertexAt, dif_neg (Nat.not_succ_le_self _)]

def mapEdge (F : C ⥤q D) (e : Edge C) : Edge D := ⟨F.obj e.1, F.obj e.2.1, F.map e.2.2⟩

theorem map_length (F : C ⥤q D) {a b : C} (p : Quiver.Path a b) : (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => exact congrArg Nat.succ ih

theorem vertexAt_map (F : C ⥤q D) {a b : C} (p : Quiver.Path a b) (i : ℕ) (hi : i ≤ p.length) :
    vertexAt (F.mapPath p) i (by rw [map_length]; exact hi) = F.obj (vertexAt p i hi) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath, vertexAt, map_length]
    split <;> simp_all

theorem edgeAt_map (F : C ⥤q D) {a b : C} (p : Quiver.Path a b) (i : ℕ) (hi : i < p.length) :
    edgeAt (F.mapPath p) i (by rw [map_length]; exact hi) = mapEdge F (edgeAt p i hi) := by
  induction p with
  | nil => exact False.elim (Nat.not_lt_zero i hi)
  | cons p e ih =>
    simp only [Prefunctor.mapPath, edgeAt, map_length]
    split <;> simp_all [mapEdge]

end Kernel.Augmented.Generating.FinPath

import Kernel.Augmented.GeneratingShapes
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

/-! Each elementary generating boundary has only finitely many incident faces.
Cites: D-KR-15, D-KR-18, AT-FD-7.

Both endpoint rows and both vertical sides remain present for nullary inputs and
empty outputs. This concerns the incidence base, not composite augmented arities.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating

/-- All positions incident to an elementary generator, including the generator itself. -/
def Face : Shape → Type
  | .point => Unit
  | .vertical => Unit ⊕ Bool
  | .horizontal => Unit ⊕ Bool
  | .cell n ε => Unit ⊕ (Vertex n ε ⊕ (Bool ⊕ HorizontalEdge n ε))

instance (s : Shape) : Fintype (Face s) := by
  cases s <;> dsimp [Face] <;> infer_instance

/-- Each position supplies its sort and its incidence arrow into the generator. -/
def faceArrow : (s : Shape) → Face s → (Σ t, Hom t s)
  | .point, _ => ⟨.point, .id _⟩
  | .vertical, .inl _ => ⟨.vertical, .id _⟩
  | .vertical, .inr e => ⟨.point, .verticalEndpoint e⟩
  | .horizontal, .inl _ => ⟨.horizontal, .id _⟩
  | .horizontal, .inr e => ⟨.point, .horizontalEndpoint e⟩
  | .cell n ε, .inl _ => ⟨.cell n ε, .id _⟩
  | .cell _ _, .inr (.inl v) => ⟨.point, .cellVertex v⟩
  | .cell _ _, .inr (.inr (.inl side)) => ⟨.vertical, .cellVertical side⟩
  | .cell _ _, .inr (.inr (.inr e)) => ⟨.horizontal, .cellHorizontal e⟩

theorem faceArrow_surjective (s : Shape) : Function.Surjective (faceArrow s) := by
  rintro ⟨t, f⟩
  cases f with
  | id s =>
    cases s with
    | point => exact ⟨(), rfl⟩
    | vertical => exact ⟨.inl (), rfl⟩
    | horizontal => exact ⟨.inl (), rfl⟩
    | cell n ε => exact ⟨.inl (), rfl⟩
  | verticalEndpoint e => exact ⟨.inr e, rfl⟩
  | horizontalEndpoint e => exact ⟨.inr e, rfl⟩
  | cellVertex v => exact ⟨.inr (.inl v), rfl⟩
  | cellVertical side => exact ⟨.inr (.inr (.inl side)), rfl⟩
  | cellHorizontal e => exact ⟨.inr (.inr (.inr e)), rfl⟩

/-- Finiteness is over all source sorts, not just each individual hom-set. -/
instance (s : Shape) : Finite (Σ t, Hom t s) :=
  Finite.of_surjective (faceArrow s) (faceArrow_surjective s)

instance (s t : Shape) : Finite (s ⟶ t) :=
  Finite.of_injective (fun f : s ⟶ t => (⟨s, f⟩ : Σ r, Hom r t))
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

instance (s t : Shapeᵒᵖ) : Finite (s ⟶ t) :=
  Finite.of_injective (fun f : s ⟶ t => f.unop)
    (fun f g h => by cases f; cases g; cases h; rfl)

end Kernel.Augmented.Generating

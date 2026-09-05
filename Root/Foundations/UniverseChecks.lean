import Root.Foundations.Signatures
import Kernel.Foundations.Examples
import Prototype.Universes.Examples
import Prototype.MatrixCategoryExamples

/-! Executable size checks, including all three requested object/entry orderings.
Only the existing matrix tests are imported; no matrix construction is added.
Cites: D-RT-27, D-SP-10, AT-FD-1.
-/

open CategoryTheory Kernel.Foundations Root.Foundations
namespace Root.Foundations.UniverseChecks

universe u v w

example : Type (u + 1) := Type u
example : Type (v + 1) := SmallSpace.{v}
example : Type (v + 2) := ClassifierData.{v}
example : Type (max (u + 1) (v + 1)) := CategoryCollection.{u,v}
example (A : Type u) : Type (max u (v + 1)) := CategoryOn.{u,v} A
example (S : ShapeSignature) : Type (max (u + 1) (v + 2)) :=
  Diagram.{u+1,max u (v+1)} S (Type u)

-- The intended ambient parameters from D-RT-27, including the label collection.
example (S : ShapeSignature)
    (conditions : (X : Type (u + 1)) → Diagram.{u+1,max u (v+1)} S X → Prop) :
    Type (max (u + 2) (v + 2)) := RootSignature S conditions

section
variable (S : ShapeSignature) (X : Type 0)
variable (P : Diagram.{0,1} S X) (W : MonadNerves.{0,1} S X)
variable (conditions : (Y : Type 0) → Diagram.{0,1} S Y → Prop)

example : Type 0 := Labelled S X
example : Category.{0} (Labelled S X) := inferInstance
example : Type 2 := Diagram.{0,1} S X
example : Type 2 := RootSignature S conditions
example : Type 2 := WalkingSignature.{0,1} S X
example (T : WalkingSignature.{0,1} S X) (b : T.boundary ⟶ P) :
    Type 1 := RelativeChoice T P b
example : Type 1 := MonadCollection W P
example : Type 2 := ModSignature W P
example : Type 2 := RelativeMappingSpace.{0,1}
example : Type 2 := CategoryOn.{0,1} X
example : Type 2 := CategoryCollection.{0,1}
example : Type 2 := SmallSpace.{1}
example : Type 3 := ClassifierData.{1}
example : Labelled S X ≌ Labelled S (ULift.{3} X) :=
  liftLabelsEquivalence S X
example (A B : SSet.{1}) : (A ⟶ B) ≃ (liftSSet.{1,2} A ⟶ liftSSet.{1,2} B) :=
  liftSSetHomEquiv A B
end

section
variable (S : ShapeSignature) (X : Type 1)
variable (P : Diagram.{1,1} S X) (W : MonadNerves.{1,1} S X)
variable (conditions : (Y : Type 1) → Diagram.{1,1} S Y → Prop)

example : Type 1 := Labelled S X
example : Category.{0} (Labelled S X) := inferInstance
example : Type 2 := Diagram.{1,1} S X
example : Type 2 := RootSignature S conditions
example : Type 2 := WalkingSignature.{1,1} S X
example (T : WalkingSignature.{1,1} S X) (b : T.boundary ⟶ P) :
    Type 1 := RelativeChoice T P b
example : Type 1 := MonadCollection W P
example : Type 2 := ModSignature W P
example : Type 2 := RelativeMappingSpace.{1,1}
example : Type 2 := CategoryOn.{1,1} X
example : Type 2 := CategoryCollection.{1,1}
example : Type 2 := SmallSpace.{1}
example : Type 3 := ClassifierData.{1}
example : Labelled S X ≌ Labelled S (ULift.{3} X) :=
  liftLabelsEquivalence S X
example (A B : SSet.{1}) : (A ⟶ B) ≃ (liftSSet.{1,3} A ⟶ liftSSet.{1,3} B) :=
  liftSSetHomEquiv A B
end

section
variable (S : ShapeSignature) (X : Type 1)
variable (P : Diagram.{1,0} S X) (W : MonadNerves.{1,0} S X)
variable (conditions : (Y : Type 1) → Diagram.{1,0} S Y → Prop)

example : Type 1 := Labelled S X
example : Category.{0} (Labelled S X) := inferInstance
example : Type 1 := Diagram.{1,0} S X
example : Type 2 := RootSignature S conditions
example : Type 1 := WalkingSignature.{1,0} S X
example (T : WalkingSignature.{1,0} S X) (b : T.boundary ⟶ P) :
    Type 1 := RelativeChoice T P b
example : Type 1 := MonadCollection W P
example : Type 2 := ModSignature W P
example : Type 2 := RelativeMappingSpace.{1,0}
example : Type 1 := CategoryOn.{1,0} X
example : Type 2 := CategoryCollection.{1,0}
example : Type 1 := SmallSpace.{0}
example : Type 2 := ClassifierData.{0}
example : Labelled S X ≌ Labelled S (ULift.{2} X) :=
  liftLabelsEquivalence S X
example (A B : SSet.{0}) : (A ⟶ B) ≃ (liftSSet.{0,3} A ⟶ liftSSet.{0,3} B) :=
  liftSSetHomEquiv A B
end

end Root.Foundations.UniverseChecks

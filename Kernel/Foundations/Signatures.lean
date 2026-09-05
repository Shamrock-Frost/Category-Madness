import Kernel.Foundations.Inventory

/-! Minimal universe contracts; no augmented shape algebra is asserted here.
The finite-level shape category and position functor are explicit inputs.
Cites: D-KR-19, D-RT-27, D-SP-10, AT-FD-1.
-/

open CategoryTheory
open scoped SSet.modelCategoryQuillen

namespace Kernel.Foundations
universe l s w

/-- Collection of Kan simplicial sets, one successor above simplex size. -/
abbrev SmallSpace : Type (s + 1) := { X : SSet.{s} // SSet.KanComplex X }

/-- Size of classifier data; classification and univalence are separate obligations. -/
structure ClassifierData where
  base : SSet.{s + 1}
  total : SSet.{s + 1}
  projection : total ⟶ base

/-- Input required from the later augmented-shape construction. -/
structure ShapeSignature where
  Shape : Type
  category : SmallCategory Shape
  positions : Shape ⥤ Type

attribute [instance] ShapeSignature.category

/-- Labellings vary contravariantly in shapes. -/
def labels (S : ShapeSignature) (X : Type l) : S.Shapeᵒᵖ ⥤ Type l where
  obj a := S.positions.obj a.unop → X
  map f := ↾fun x p => x (S.positions.map f.unop p)
  map_id a := by ext x p; simp
  map_comp f g := by ext x p; simp

/-- The opposite restores the direction of the original shape arrows. -/
abbrev Labelled (S : ShapeSignature) (X : Type l) : Type l :=
  (labels S X).Elementsᵒᵖ

abbrev Diagram (S : ShapeSignature) (X : Type l) : Type (max l (s + 1)) :=
  (Labelled S X)ᵒᵖ ⥤ SSet.{s}

def reindexLabels (S : ShapeSignature) {X Y : Type l} (f : X → Y) :
    Labelled S X ⥤ Labelled S Y :=
  (NatTrans.mapElements
    ({ app := fun _ => ↾fun x p => f (x p)
       naturality := by intros; rfl } : labels S X ⟶ labels S Y)).op

/-- Raise simplex size pointwise. There is no lowering operation on arbitrary objects. -/
def liftSSet (X : SSet.{s}) : SSet.{max s w} where
  obj n := ULift.{w} (X.obj n)
  map f := ↾fun x => ⟨X.map f x.down⟩
  map_id n := by ext x; simp
  map_comp f g := by ext x; simp

def liftSSetMap {X Y : SSet.{s}} (f : X ⟶ Y) :
    liftSSet.{s,w} X ⟶ liftSSet.{s,w} Y where
  app n := ↾fun x => ⟨f.app n x.down⟩
  naturality a b g := by
    ext x
    exact congrArg ULift.up (NatTrans.naturality_apply f g x.down)

/-- Lower a map only between two specified lifted objects. -/
def lowerSSetMap {X Y : SSet.{s}}
    (f : liftSSet.{s,w} X ⟶ liftSSet.{s,w} Y) : X ⟶ Y where
  app n := ↾fun x => (f.app n ⟨x⟩).down
  naturality a b g := by
    ext x
    exact congrArg ULift.down (NatTrans.naturality_apply f g ⟨x⟩)

@[simp] theorem lower_liftSSetMap {X Y : SSet.{s}} (f : X ⟶ Y) :
    lowerSSetMap (liftSSetMap.{s,w} f) = f := by
  ext n x
  rfl

@[simp] theorem lift_lowerSSetMap {X Y : SSet.{s}}
    (f : liftSSet.{s,w} X ⟶ liftSSet.{s,w} Y) :
    liftSSetMap (lowerSSetMap f) = f := by
  ext n x
  rfl

def liftSSetHomEquiv (X Y : SSet.{s}) :
    (X ⟶ Y) ≃ (liftSSet.{s,w} X ⟶ liftSSet.{s,w} Y) where
  toFun := liftSSetMap
  invFun := lowerSSetMap
  left_inv := lower_liftSSetMap
  right_inv := lift_lowerSSetMap

@[simp] theorem liftSSetMap_id (X : SSet.{s}) :
    liftSSetMap.{s,w} (𝟙 X) = 𝟙 (liftSSet.{s,w} X) := rfl

@[simp] theorem liftSSetMap_comp {X Y Z : SSet.{s}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftSSetMap.{s,w} (f ≫ g) = liftSSetMap f ≫ liftSSetMap g := rfl

/-- Raise the labels, preserving the underlying shape and its arrows. -/
def liftLabels (S : ShapeSignature) (X : Type l) :
    Labelled S X ⥤ Labelled S (ULift.{w} X) where
  obj a := Opposite.op ⟨a.unop.1, fun p => ⟨a.unop.2 p⟩⟩
  map f := Quiver.Hom.op ⟨f.unop.val, by
    funext p
    exact congrArg ULift.up (congrFun f.unop.property p)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison back is defined only for this specified lifted label type. -/
def lowerLabels (S : ShapeSignature) (X : Type l) :
    Labelled S (ULift.{w} X) ⥤ Labelled S X where
  obj a := Opposite.op ⟨a.unop.1, fun p => (a.unop.2 p).down⟩
  map f := Quiver.Hom.op ⟨f.unop.val, by
    funext p
    exact congrArg ULift.down (congrFun f.unop.property p)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Label lifting is an equivalence of indexing categories, not a size axiom. -/
def liftLabelsEquivalence (S : ShapeSignature) (X : Type l) :
    Labelled S X ≌ Labelled S (ULift.{w} X) where
  functor := liftLabels S X
  inverse := lowerLabels S X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change f ≫ 𝟙 b = 𝟙 a ≫ f
    simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change f ≫ 𝟙 b = 𝟙 a ≫ f
    simp)
  functor_unitIso_comp a := by
    change 𝟙 ((liftLabels S X).obj a) ≫ 𝟙 _ = 𝟙 _
    simp

end Kernel.Foundations

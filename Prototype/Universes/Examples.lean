import Prototype.Universes.Matrix
import Prototype.Universes.Reindex

/-!
Explicit AT-FD-1 matrix examples. These exercise all three requested orderings
of object and entry universes, and a genuine lift from entry level 0 to 1.
Object-label lifts and mixed lifts additionally use levels 2 and 3.

Cites: D-CH-23, D-RT-27, D-WF-10, AT-FD-1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Prototype.Universes

-- Family collections: (u, v) = (0, 1), (1, 1), and (1, 0).
example (A B : Type 0) : Type 2 := Matrix.{0, 1} A B
example (A B : Type 1) : Type 2 := Matrix.{1, 1} A B
example (A B : Type 1) : Type 1 := Matrix.{1, 0} A B

-- Actual families and entries, including a large collection of small labels.
example : Matrix.{0, 1} Nat Bool := fun _ _ => Type 0
example : Matrix.{1, 1} (Type 0) (Type 0) := fun _ _ => Type 0
example : Matrix.{1, 0} (Type 0) (Type 0) := fun A B => A → B

-- The same map laws elaborate without equating object and entry levels.
example {A B : Type 0} {M N : Matrix.{0, 1} A B} (f : Matrix.Map M N) :
    Matrix.comp (Matrix.id N) f = f := Matrix.id_comp f

example {A B : Type 1} {M N : Matrix.{1, 1} A B} (f : Matrix.Map M N) :
    Matrix.comp (Matrix.id N) f = f := Matrix.id_comp f

example {A B : Type 1} {M N : Matrix.{1, 0} A B} (f : Matrix.Map M N) :
    Matrix.comp (Matrix.id N) f = f := Matrix.id_comp f

-- Entry lifting preserves all maps in both directions at unequal levels.
example {M N : Matrix.{1, 0} (Type 0) (Type 0)} (f : Matrix.Map M N) :
    Matrix.lowerMap (Matrix.liftMap.{1, 0, 1} f) = f :=
  Matrix.lowerMap_liftMap f

example {M N : Matrix.{1, 0} (Type 0) (Type 0)}
    (f : Matrix.Map (Matrix.liftEntries.{1, 0, 1} M) (Matrix.liftEntries N)) :
    Matrix.liftMap (Matrix.lowerMap f) = f := Matrix.liftMap_lowerMap f

-- Raising the object level leaves the entry level fixed in all three orderings.
example {A B : Type 0} (M : Matrix.{0, 1} A B) :
    Matrix.{2, 1} (ULift.{2} A) (ULift.{2} B) := Matrix.liftLabels.{0, 1, 2} M

example {A B : Type 1} (M : Matrix.{1, 1} A B) :
    Matrix.{2, 1} (ULift.{2} A) (ULift.{2} B) := Matrix.liftLabels.{1, 1, 2} M

example {A B : Type 1} (M : Matrix.{1, 0} A B) :
    Matrix.{2, 0} (ULift.{2} A) (ULift.{2} B) := Matrix.liftLabels.{1, 0, 2} M

-- Restricting a family of small types to chosen labels is legitimate; it does
-- not produce a small collection of every small type.
example (M : Matrix.{1, 0} (Type 0) (Type 0)) : Matrix.{0, 0} Nat Bool :=
  Matrix.reindex (fun n => Fin n) (fun b => if b then Nat else Bool) M

example :
    Matrix.reindex (fun n => Fin n) (fun _ : Bool => Nat)
      (fun A B : Type 0 => A → B) 3 true = (Fin 3 → Nat) := rfl

-- Both family and map comparisons work after a genuine object-level increase.
example {A B : Type 0} (M : Matrix.{0, 1} A B) :
    Matrix.lowerLabels (Matrix.liftLabels.{0, 1, 2} M) = M :=
  Matrix.lowerLabels_liftLabels M

example {A B : Type 1}
    (L : Matrix.{2, 0} (ULift.{2} A) (ULift.{2} B)) :
    Matrix.liftLabels (Matrix.lowerLabels L) = L := Matrix.liftLabels_lowerLabels L

example {A B : Type 1} {M N : Matrix.{1, 0} A B} (α : Matrix.Map M N) :
    Matrix.lowerLabelsMap (Matrix.liftLabelsMap.{1, 0, 2} α) = α :=
  Matrix.lowerLabelsMap_liftLabelsMap α

example {A B : Type 1} {M N : Matrix.{1, 0} A B}
    (α : Matrix.Map (Matrix.liftLabels.{1, 0, 2} M) (Matrix.liftLabels N)) :
    Matrix.liftLabelsMap (Matrix.lowerLabelsMap α) = α :=
  Matrix.liftLabelsMap_lowerLabelsMap α

-- Object, entry, and the two lift levels are all distinct: (0, 1, 2, 3).
example {A B : Type 0} (M : Matrix.{0, 1} A B) :
    Matrix.liftLabels.{0, 3, 2} (Matrix.liftEntries.{0, 1, 3} M) =
      Matrix.liftEntries.{2, 1, 3} (Matrix.liftLabels.{0, 1, 2} M) :=
  Matrix.liftLabels_liftEntries M

example {A B : Type 0} {M N : Matrix.{0, 1} A B} (α : Matrix.Map M N) :
    Matrix.liftLabelsMap.{0, 3, 2} (Matrix.liftMap.{0, 1, 3} α) =
      Matrix.liftMap.{2, 1, 3} (Matrix.liftLabelsMap.{0, 1, 2} α) :=
  Matrix.liftLabelsMap_liftMap α

-- Reproducible theorem-level axiom reports; the complete AT-FD-11 audit is later.
#print axioms Matrix.id_comp
#print axioms Matrix.comp_id
#print axioms Matrix.comp_assoc
#print axioms Matrix.lowerMap_liftMap
#print axioms Matrix.liftMap_lowerMap
#print axioms Matrix.liftMap_id
#print axioms Matrix.liftMap_comp
#print axioms Matrix.reindex_id
#print axioms Matrix.reindex_comp
#print axioms Matrix.reindexMap_id
#print axioms Matrix.reindexMap_comp
#print axioms Matrix.lowerLabels_liftLabels
#print axioms Matrix.liftLabels_lowerLabels
#print axioms Matrix.lowerLabelsMap_liftLabelsMap
#print axioms Matrix.liftLabelsMap_lowerLabelsMap
#print axioms Matrix.liftLabelsMap_id
#print axioms Matrix.liftLabelsMap_comp
#print axioms Matrix.liftLabels_liftEntries
#print axioms Matrix.liftLabelsMap_liftMap

end Prototype.Universes

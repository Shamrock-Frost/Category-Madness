import Prototype.Universes.Matrix

/-!
Explicit AT-FD-1 matrix examples. These exercise all three requested orderings
of object and entry universes, and a genuine lift from entry level 0 to 1.

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

-- Reproducible theorem-level axiom reports; the complete AT-FD-11 audit is later.
#print axioms Matrix.id_comp
#print axioms Matrix.comp_id
#print axioms Matrix.comp_assoc
#print axioms Matrix.lowerMap_liftMap
#print axioms Matrix.liftMap_lowerMap
#print axioms Matrix.liftMap_id
#print axioms Matrix.liftMap_comp

end Prototype.Universes

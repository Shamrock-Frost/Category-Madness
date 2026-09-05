/-!
# Matrix families with separate object and entry universes

First, partial AT-FD-1 experiment. This tests the family-collection level from
D-RT-27 and entry lifts; it does not define the proposed VDC∞ root or its seal.

Cites: D-FD-01, D-CH-23, D-RT-25, D-RT-27, AT-FD-1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Prototype.Universes

/-- A collection of matrices is larger than an individual entry type. -/
abbrev Matrix.{u, v} (A B : Type u) : Type (max u (v + 1)) :=
  A → B → Type v

namespace Matrix

universe u v w

variable {A B : Type u} {M N P Q : Matrix.{u, v} A B}

/-- A map of families fixes both object labels. -/
abbrev Map (M N : Matrix.{u, v} A B) : Type (max u v) :=
  (a : A) → (b : B) → M a b → N a b

def id (M : Matrix.{u, v} A B) : Map M M :=
  fun _ _ x => x

def comp (g : Map N P) (f : Map M N) : Map M P :=
  fun a b x => g a b (f a b x)

theorem id_comp (f : Map M N) : comp (id N) f = f := rfl

theorem comp_id (f : Map M N) : comp f (id M) = f := rfl

theorem comp_assoc (h : Map P Q) (g : Map N P) (f : Map M N) :
    comp (comp h g) f = comp h (comp g f) := rfl

/-- Raise each entry to `Type (max v w)`, leaving the object labels fixed. -/
def liftEntries (M : Matrix.{u, v} A B) : Matrix.{u, max v w} A B :=
  fun a b => ULift.{w} (M a b)

def liftMap (f : Map M N) : Map (liftEntries.{u, v, w} M) (liftEntries N) :=
  fun a b x => ⟨f a b x.down⟩

/-- Recover a map between the original entries, which are already given.
This is not an operation that lowers arbitrary types to a smaller universe. -/
def lowerMap (f : Map (liftEntries.{u, v, w} M) (liftEntries N)) : Map M N :=
  fun a b x => (f a b ⟨x⟩).down

theorem lowerMap_liftMap (f : Map M N) :
    lowerMap (liftMap.{u, v, w} f) = f := rfl

theorem liftMap_lowerMap (f : Map (liftEntries.{u, v, w} M) (liftEntries N)) :
    liftMap (lowerMap f) = f := by
  funext a b x
  cases x
  rfl

theorem liftMap_id (M : Matrix.{u, v} A B) :
    liftMap.{u, v, w} (id M) = id (liftEntries M) := by
  funext a b x
  cases x
  rfl

theorem liftMap_comp (g : Map N P) (f : Map M N) :
    liftMap.{u, v, w} (comp g f) = comp (liftMap g) (liftMap f) := rfl

end Matrix
end Prototype.Universes

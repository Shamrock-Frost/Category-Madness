import Prototype.Universes.Matrix

/-!
# Reindexing matrices and lifting their object labels

Reindexing may change the object universe while leaving entry types unchanged.
Along `ULift.down` it admits an inverse, on both families and their maps.
Object-label lifting also commutes with the existing entry lift.

Cites: D-FD-01, D-CH-23, D-RT-27, AT-FD-1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Prototype.Universes.Matrix

universe u v w z u' u''

variable {A B : Type u} {A' B' : Type u'} {A'' B'' : Type u''}
variable {M N P : Matrix.{u, v} A B}

/-- Pull back the two labels of a family; no entries are lifted. -/
def reindex (f : A' → A) (g : B' → B) (M : Matrix.{u, v} A B) :
    Matrix.{u', v} A' B' :=
  fun a b => M (f a) (g b)

def reindexMap (f : A' → A) (g : B' → B) (α : Map M N) :
    Map (reindex f g M) (reindex f g N) :=
  fun a b x => α (f a) (g b) x

theorem reindex_id (M : Matrix.{u, v} A B) :
    reindex (fun a => a) (fun b => b) M = M := rfl

theorem reindex_comp (f : A' → A) (g : B' → B)
    (f' : A'' → A') (g' : B'' → B') (M : Matrix.{u, v} A B) :
    reindex f' g' (reindex f g M) =
      reindex (fun a => f (f' a)) (fun b => g (g' b)) M := rfl

theorem reindexMap_id (f : A' → A) (g : B' → B) (M : Matrix.{u, v} A B) :
    reindexMap f g (id M) = id (reindex f g M) := rfl

theorem reindexMap_comp (f : A' → A) (g : B' → B) (β : Map N P) (α : Map M N) :
    reindexMap f g (comp β α) = comp (reindexMap f g β) (reindexMap f g α) := rfl

/-- Raise the object-label universe, keeping each entry in its original universe. -/
def liftLabels (M : Matrix.{u, v} A B) :
    Matrix.{max u w, v} (ULift.{w} A) (ULift.{w} B) :=
  reindex ULift.down ULift.down M

/-- Restrict a family on specified lifted labels back to the original labels. -/
def lowerLabels (L : Matrix.{max u w, v} (ULift.{w} A) (ULift.{w} B)) :
    Matrix.{u, v} A B :=
  reindex ULift.up ULift.up L

theorem lowerLabels_liftLabels (M : Matrix.{u, v} A B) :
    lowerLabels (liftLabels.{u, v, w} M) = M := rfl

theorem liftLabels_lowerLabels
    (L : Matrix.{max u w, v} (ULift.{w} A) (ULift.{w} B)) :
    liftLabels (lowerLabels L) = L := by
  funext a b
  cases a
  cases b
  rfl

def liftLabelsMap (α : Map M N) :
    Map (liftLabels.{u, v, w} M) (liftLabels N) :=
  reindexMap ULift.down ULift.down α

def lowerLabelsMap (α : Map (liftLabels.{u, v, w} M) (liftLabels N)) : Map M N :=
  reindexMap ULift.up ULift.up α

theorem lowerLabelsMap_liftLabelsMap (α : Map M N) :
    lowerLabelsMap (liftLabelsMap.{u, v, w} α) = α := rfl

theorem liftLabelsMap_lowerLabelsMap
    (α : Map (liftLabels.{u, v, w} M) (liftLabels N)) :
    liftLabelsMap (lowerLabelsMap α) = α := by
  funext a b x
  cases a
  cases b
  rfl

theorem liftLabelsMap_id (M : Matrix.{u, v} A B) :
    liftLabelsMap.{u, v, w} (id M) = id (liftLabels M) :=
  reindexMap_id ULift.down ULift.down M

theorem liftLabelsMap_comp (β : Map N P) (α : Map M N) :
    liftLabelsMap.{u, v, w} (comp β α) =
      comp (liftLabelsMap β) (liftLabelsMap α) :=
  reindexMap_comp ULift.down ULift.down β α

/-- The two universe increases are independent even when all four levels differ. -/
theorem liftLabels_liftEntries (M : Matrix.{u, v} A B) :
    liftLabels.{u, max v z, w} (liftEntries.{u, v, z} M) =
      liftEntries.{max u w, v, z} (liftLabels.{u, v, w} M) := rfl

theorem liftLabelsMap_liftMap (α : Map M N) :
    liftLabelsMap.{u, max v z, w} (liftMap.{u, v, z} α) =
      liftMap.{max u w, v, z} (liftLabelsMap.{u, v, w} α) := rfl

end Prototype.Universes.Matrix

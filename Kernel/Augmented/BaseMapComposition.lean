import Kernel.Augmented.BaseMaps

/-! Identity and composition of maps of vertical/horizontal bases.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.BaseMap
universe u v h u' v' h' u'' v'' h'' u''' v''' h'''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {J : Type u'''} [Category.{v'''} J]
  {H : C → C → Type h} {K : D → D → Type h'} {L : E → E → Type h''}
  {N : J → J → Type h'''}

def id (H : C → C → Type h) : BaseMap H H where
  vertical := 𝟭 C
  horizontal j := j

def comp (F : BaseMap H K) (G : BaseMap K L) : BaseMap H L where
  vertical := F.vertical ⋙ G.vertical
  horizontal j := G.horizontal (F.horizontal j)

@[simp] theorem id_comp (F : BaseMap H K) : (id H).comp F = F := by cases F; rfl
@[simp] theorem comp_id (F : BaseMap H K) : F.comp (id K) = F := by cases F; rfl
@[simp] theorem comp_assoc (F : BaseMap H K) (G : BaseMap K L) (I : BaseMap L N) :
    (F.comp G).comp I = F.comp (G.comp I) := rfl

@[simp] theorem id_side (f : Side C) : (id H).side f = f := by cases f; rfl
@[simp] theorem comp_side (F : BaseMap H K) (G : BaseMap K L) (f : Side C) :
    (F.comp G).side f = G.side (F.side f) := rfl

@[simp] theorem id_path {a b : C} (p : HPath H a b) : (id H).path p = p := by
  induction p with
  | nil => rfl
  | cons p j ih => exact congrArg (fun p => p.cons j) ih

@[simp] theorem comp_path (F : BaseMap H K) (G : BaseMap K L) {a b : C} (p : HPath H a b) :
    (F.comp G).path p = G.path (F.path p) := by
  induction p with
  | nil => rfl
  | cons p j ih => exact congrArg (fun p => p.cons (G.horizontal (F.horizontal j))) ih

@[simp] theorem id_shortPath {a b : C} (p : ShortPath H a b) : (id H).shortPath p = p :=
  Subtype.ext (id_path p.val)

@[simp] theorem comp_shortPath (F : BaseMap H K) (G : BaseMap K L) {a b : C} (p : ShortPath H a b) :
    (F.comp G).shortPath p = G.shortPath (F.shortPath p) := Subtype.ext (comp_path F G p.val)

@[simp] theorem id_frame (b : CellBoundary C H) : (id H).frame b = b := by
  rcases b with ⟨f, g, b⟩
  exact Boundary.frame_eq (id_side f) (id_side g) (heq_of_eq (id_path b.input))
    (heq_of_eq (id_shortPath b.output))

@[simp] theorem comp_frame (F : BaseMap H K) (G : BaseMap K L) (b : CellBoundary C H) :
    (F.comp G).frame b = G.frame (F.frame b) := by
  rcases b with ⟨f, g, b⟩
  exact Boundary.frame_eq rfl rfl (heq_of_eq (comp_path F G b.input))
    (heq_of_eq (comp_shortPath F G b.output))

end Kernel.Augmented.BaseMap

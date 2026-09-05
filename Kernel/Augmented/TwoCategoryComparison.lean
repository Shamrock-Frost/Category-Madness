import Kernel.Augmented.FromTwoCategoryLaws
import Kernel.Augmented.VerticalTwoCategory
import Kernel.Augmented.CellMaps
import Mathlib.CategoryTheory.Equivalence

/-! Comparison maps for the no-horizontal augmented algebra and strict 2-categories.
Cites: D-KR-14, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Bicategory
namespace Kernel.Augmented
universe u v c

namespace FromTwoCategory
variable {C : Type u} [Bicategory.{c,v} C] [Bicategory.Strict C]

/-- A type copy keeps the recovered and original hom-category instances distinct. -/
def RecoveredHom (a b : C) := a ⟶ b

instance recoveredHomCategory (a b : C) : Category.{c} (RecoveredHom a b) :=
  Vertical.homCategory algebra a b

def toOriginalHom (a b : C) : RecoveredHom a b ⥤ (a ⟶ b) where
  obj f := f
  map φ := φ
  map_id _ := rfl
  map_comp φ ψ := verticalAlongRow_eq (a := a) (b := b) φ ψ

def fromOriginalHom (a b : C) : (a ⟶ b) ⥤ RecoveredHom a b where
  obj f := f
  map φ := φ
  map_id _ := rfl
  map_comp φ ψ := (verticalAlongRow_eq (a := a) (b := b) φ ψ).symm

@[simp] theorem toOriginalHom_fromOriginalHom (a b : C) :
    toOriginalHom a b ⋙ fromOriginalHom a b = 𝟭 (RecoveredHom a b) := rfl

@[simp] theorem fromOriginalHom_toOriginalHom (a b : C) :
    fromOriginalHom a b ⋙ toOriginalHom a b = 𝟭 (a ⟶ b) := rfl

/-- The hom categories are recovered by inverse functors that preserve every cell. -/
def homEquivalence (a b : C) : RecoveredHom a b ≌ (a ⟶ b) where
  functor := toOriginalHom a b
  inverse := fromOriginalHom a b
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by
    intro X
    exact @Category.id_comp (a ⟶ b) (Bicategory.homCategory a b) X X
      (@CategoryStruct.id (a ⟶ b) (Bicategory.homCategory a b).toCategoryStruct X)

end FromTwoCategory

namespace NoHorizontal
variable {C : Type u} [Category.{v} C]
  {G : CellGraph.{u,v,0,c} C (fun _ _ : C => Empty)} (A : Algebra G)

def reconstructedGraph : CellGraph.{u,v,0,c} C (fun _ _ : C => Empty) :=
  @FromTwoCategory.graph C (Vertical.bicategory A)

def reconstructedAlgebra : Algebra (reconstructedGraph A) :=
  @FromTwoCategory.algebra C (Vertical.bicategory A) (Vertical.bicategory_strict A)

/-- Reconstructing after extraction retains the entire family of incident cells. -/
def cellEquiv {f g : Side C} (b : Boundary (fun _ _ : C => Empty) f g) :
    (reconstructedGraph A).Cell b ≃ G.Cell b :=
  Boundary.emptyElim
    (fun {_ _} b => (reconstructedGraph A).Cell b ≃ G.Cell b)
    (fun _ _ => Equiv.refl _) b

def toOriginal : CellGraph.Map (reconstructedGraph A) G := ⟨fun {_ _} {b} φ => cellEquiv A b φ⟩
def fromOriginal : CellGraph.Map G (reconstructedGraph A) :=
  ⟨fun {_ _} {b} φ => (cellEquiv A b).symm φ⟩

@[simp] theorem toOriginal_fromOriginal {f g : Side C}
    {b : Boundary (fun _ _ : C => Empty) f g} (φ : G.Cell b) :
    (toOriginal A).cell ((fromOriginal A).cell φ) = φ := (cellEquiv A b).apply_symm_apply φ

@[simp] theorem fromOriginal_toOriginal {f g : Side C}
    {b : Boundary (fun _ _ : C => Empty) f g} (φ : (reconstructedGraph A).Cell b) :
    (fromOriginal A).cell ((toOriginal A).cell φ) = φ := (cellEquiv A b).symm_apply_apply φ

@[simp] theorem reconstructed_verticalIdentity {a b : C} (f : a ⟶ b) :
    (reconstructedAlgebra A).verticalIdentity f = A.verticalIdentity f := rfl

@[simp] theorem reconstructed_verticalAlongRow {a b : C} {f g h : a ⟶ b}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical g h)) :
    (reconstructedAlgebra A).verticalAlongRow (f := f) (g := g) (k := h) α β =
      A.verticalAlongRow α β := by
  let := Vertical.bicategory A
  let := Vertical.bicategory_strict A
  exact FromTwoCategory.verticalAlongRow_eq (a := a) (b := b) α β

theorem reconstructed_stack {a b d : C} {f g : a ⟶ b} {h k : b ⟶ d}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical h k)) :
    @FromTwoCategory.stack C (Vertical.bicategory A) a b d f g h k α β = A.verticalStack α β := by
  change A.verticalAlongRow (A.verticalStack α (A.verticalIdentity h))
    (A.verticalStack (A.verticalIdentity g) β) = A.verticalStack α β
  rw [Vertical.interchange, Vertical.alongRow_identity, Vertical.identity_alongRow]

@[simp] theorem reconstructed_verticalStack {a b d : C} {f g : a ⟶ b} {h k : b ⟶ d}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical h k)) :
    (reconstructedAlgebra A).verticalStack (f := f) (g := g) (h := h) (k := k) α β =
      A.verticalStack α β := by
  let := Vertical.bicategory A
  let := Vertical.bicategory_strict A
  exact (FromTwoCategory.verticalStack_eq (a := a) (b := b) (d := d) α β).trans
    (reconstructed_stack A α β)

theorem reconstructed_rowFold {a b : C} {f g : a ⟶ b} (r : Vertical.Row (G := G) f g) :
    @FromTwoCategory.rowFold C (Vertical.bicategory A) (Vertical.bicategory_strict A) a b f g r =
      Vertical.fold A r := by
  induction r with
  | nil => rfl
  | cons r φ ih => exact congrArg (fun x => A.verticalAlongRow x φ) ih

/-- Every nonempty substitution is recovered, not only the two binary compositions. -/
theorem reconstructed_substitute {a b d : C} {f g : a ⟶ b}
    (r : Vertical.Row (G := G) f g) (hr : 0 < r.length)
    {h k : b ⟶ d} (β : G.Cell (Boundary.vertical h k)) :
    Vertical.substitute (reconstructedAlgebra A).toOperations (h := h) (k := k) r hr β =
      Vertical.substitute A.toOperations r hr β := by
  let := Vertical.bicategory A
  let := Vertical.bicategory_strict A
  change Vertical.substitute FromTwoCategory.operations (h := h) (k := k) r hr β = _
  erw [FromTwoCategory.substitute_vertical, reconstructed_stack, reconstructed_rowFold]
  rw [Vertical.substitute_eq_stack_compose, Vertical.compose_eq_fold]

end NoHorizontal
end Kernel.Augmented

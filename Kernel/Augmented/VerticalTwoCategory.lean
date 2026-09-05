import Kernel.Augmented.Vertical
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-! The strict 2-category of vertical cells of an augmented algebra.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Vertical
universe u v h c
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} (A : Algebra G)

def ofEq {a b : C} {f g : a ⟶ b} (e : f = g) : Cell (G := G) f g :=
  @eqToHom (Hom G a b) (homCategory A a b).toCategoryStruct f g e

theorem stack_ofEq {a b d : C} {f f' : a ⟶ b} {g g' : b ⟶ d}
    (ef : f = f') (eg : g = g') :
    A.verticalStack (ofEq A ef) (ofEq A eg) =
      ofEq A (congrArg₂ (fun f g => f ≫ g) ef eg) := by
  cases ef; cases eg
  exact A.laws.verticalIdentity_stack _ _

theorem alongRow_ofEq {a b : C} {f g k : a ⟶ b} (ef : f = g) (eg : g = k) :
    A.verticalAlongRow (ofEq A ef) (ofEq A eg) = ofEq A (ef.trans eg) := by
  cases ef; cases eg
  exact identity_alongRow A _

/-- Whiskering, unitors and associators are built from the derived compositions. -/
@[instance_reducible] def bicategory : Bicategory.{c,v} C where
  toCategoryStruct := inferInstance
  homCategory := homCategory A
  whiskerLeft f _ _ η := A.verticalStack (A.verticalIdentity f) η
  whiskerRight η h := A.verticalStack η (A.verticalIdentity h)
  associator f g h := @eqToIso (Hom G _ _) (homCategory A _ _)
    _ _ (Category.assoc f g h)
  leftUnitor f := @eqToIso (Hom G _ _) (homCategory A _ _) _ _ (Category.id_comp f)
  rightUnitor f := @eqToIso (Hom G _ _) (homCategory A _ _) _ _ (Category.comp_id f)
  whiskerLeft_id := by
    intro a b d f g
    exact A.laws.verticalIdentity_stack f g
  whiskerLeft_comp := by
    intro a b d f g h i η θ
    change A.verticalStack (A.verticalIdentity f) (A.verticalAlongRow η θ) =
      A.verticalAlongRow (A.verticalStack (A.verticalIdentity f) η)
        (A.verticalStack (A.verticalIdentity f) θ)
    exact (by simpa only [identity_alongRow] using
      (interchange A (A.verticalIdentity f) (A.verticalIdentity f) η θ).symm)
  id_whiskerLeft := by
    intro a b f g η
    let := homCategory A a b
    exact (conj_eqToHom_iff_heq _ _ (Category.id_comp f) (Category.id_comp g)).mpr
      (stack_left_identity A η)
  comp_whiskerLeft := by
    intro a b d e f g h h' η
    let := homCategory A a e
    apply (conj_eqToHom_iff_heq _ _ (Category.assoc f g h) (Category.assoc f g h')).mpr
    rw [← A.laws.verticalIdentity_stack f g]
    exact stack_assoc A _ _ η
  id_whiskerRight := by
    intro a b d f g
    exact A.laws.verticalIdentity_stack f g
  comp_whiskerRight := by
    intro a b d f g h η θ i
    change A.verticalStack (A.verticalAlongRow η θ) (A.verticalIdentity i) =
      A.verticalAlongRow (A.verticalStack η (A.verticalIdentity i))
        (A.verticalStack θ (A.verticalIdentity i))
    exact (by simpa only [identity_alongRow] using
      (interchange A η θ (A.verticalIdentity i) (A.verticalIdentity i)).symm)
  whiskerRight_id := by
    intro a b f g η
    let := homCategory A a b
    exact (conj_eqToHom_iff_heq _ _ (Category.comp_id f) (Category.comp_id g)).mpr
      (stack_right_identity A η)
  whiskerRight_comp := by
    intro a b d e f f' η g h
    let := homCategory A a e
    apply (conj_eqToHom_iff_heq _ _ (Category.assoc f g h).symm
      (Category.assoc f' g h).symm).mpr
    rw [← A.laws.verticalIdentity_stack g h]
    exact (stack_assoc A η _ _).symm
  whisker_assoc := by
    intro a b d e f g g' η h
    let := homCategory A a e
    exact (conj_eqToHom_iff_heq _ _ (Category.assoc f g h) (Category.assoc f g' h)).mpr
      (stack_assoc A _ η _)
  whisker_exchange := by
    intro a b d f g h i η θ
    change A.verticalAlongRow (A.verticalStack (A.verticalIdentity f) θ)
      (A.verticalStack η (A.verticalIdentity i)) =
      A.verticalAlongRow (A.verticalStack η (A.verticalIdentity h))
        (A.verticalStack (A.verticalIdentity g) θ)
    rw [interchange, interchange, identity_alongRow, alongRow_identity,
      alongRow_identity, identity_alongRow]
  pentagon := by
    intro a b d e z f g h i
    let := homCategory A a z
    change A.verticalAlongRow
      (A.verticalStack (ofEq A (Category.assoc f g h)) (ofEq A (rfl : i = i)))
      (A.verticalAlongRow (ofEq A (Category.assoc f (g ≫ h) i))
        (A.verticalStack (ofEq A (rfl : f = f)) (ofEq A (Category.assoc g h i)))) =
      A.verticalAlongRow (ofEq A (Category.assoc (f ≫ g) h i)) (ofEq A (Category.assoc f g (h ≫ i)))
    rw [stack_ofEq, stack_ofEq]
    simp only [alongRow_ofEq]
  triangle := by
    intro a b d f g
    let := homCategory A a d
    change A.verticalAlongRow (ofEq A (Category.assoc f (𝟙 b) g))
      (A.verticalStack (ofEq A (rfl : f = f)) (ofEq A (Category.id_comp g))) =
      A.verticalStack (ofEq A (Category.comp_id f)) (ofEq A (rfl : g = g))
    rw [stack_ofEq, stack_ofEq]
    simp only [alongRow_ofEq]

theorem bicategory_strict : @Bicategory.Strict C (bicategory A) := by
  let := bicategory A
  exact {
    id_comp := Category.id_comp
    comp_id := Category.comp_id
    assoc := Category.assoc
    leftUnitor_eqToIso _ := rfl
    rightUnitor_eqToIso _ := rfl
    associator_eqToIso _ _ _ := rfl
  }

end Kernel.Augmented.Vertical

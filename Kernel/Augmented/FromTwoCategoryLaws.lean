import Kernel.Augmented.FromTwoCategoryAlgebra
import Kernel.Augmented.NoHorizontalNested

/-! The augmented algebra laws for a supplied strict 2-category.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Bicategory
namespace Kernel.Augmented.FromTwoCategory
universe u v w
variable {C : Type u} [Bicategory.{w,v} C] [Bicategory.Strict C]

@[simp] theorem verticalStack_eq {a b d : C} {f g : a ⟶ b} {h k : b ⟶ d}
    (α : Cell f g) (β : Cell h k) : operations.verticalStack α β = stack α β := by
  change Vertical.substitute operations
    ((.nil : Vertical.Row (G := graph C) f f).cons α) (Nat.zero_lt_succ 0) β = _
  erw [substitute_vertical, rowFold_single]

@[simp] theorem verticalAlongRow_eq {a b : C} {f g h : a ⟶ b}
    (α : Cell f g) (β : Cell g h) : operations.verticalAlongRow α β = alongRow α β := by
  apply eq_of_heq
  apply (Vertical.compose_heq operations
    (((.nil : Vertical.Row (G := graph C) f f).cons α).cons β) (Nat.zero_lt_succ 1)).trans
  erw [substitute_vertical, rowFold_cons, rowFold_single]
  exact stack_identity_object _

theorem operations_leftUnit {f g : Side C} {b : Boundary (fun _ _ : C => Empty) f g}
    (φ : (graph C).Cell b) :
    CellGraph.transport (Operations.leftUnit_boundary φ) (operations.leftUnitComposite φ) = φ := by
  induction b using Boundary.emptyElim with
  | hv f g =>
    apply (CellGraph.transport_eq_iff_heq _ _ _).mpr
    change HEq (operations.verticalStack φ (identity (𝟙 _))) φ
    rw [verticalStack_eq]
    exact stack_identity_object φ

theorem operations_rightUnit {f g : Side C} {b : Boundary (fun _ _ : C => Empty) f g}
    (φ : (graph C).Cell b) :
    CellGraph.transport (operations.rightUnit_boundary b) (operations.rightUnitComposite φ) = φ := by
  induction b using Boundary.emptyElim with
  | hv f g =>
    apply (CellGraph.transport_eq_iff_heq _ _ _).mpr
    change HEq (operations.verticalStack (identity (𝟙 _)) φ) φ
    rw [verticalStack_eq]
    exact identity_stack φ

/-- The raw incident operation agrees with the vertical formula through the shared transport. -/
theorem substitute_embed {a b d : C} {f g : a ⟶ b}
    (p : Vertical.Row (G := graph C) f g) (hp : 0 < p.length) (h k : b ⟶ d)
    (β : (graph C).Cell (CellGraph.Row.outerBoundary (Vertical.Row.nonempty p hp)
      h k (ShortPath.empty d))) :
    HEq (operations.substitute (Vertical.Row.nonempty p hp) h k (ShortPath.empty d) β)
      (stack (rowFold p) (CellGraph.castInput (G := graph C)
        (f := ⟨b, d, h⟩) (g := ⟨b, d, k⟩) (L := ShortPath.empty d)
        (Vertical.Row.embed_output p) β)) := by
  let β' : Cell h k := CellGraph.castInput (G := graph C)
    (f := ⟨b, d, h⟩) (g := ⟨b, d, k⟩) (L := ShortPath.empty d)
    (Vertical.Row.embed_output p) β
  have e : HEq (Vertical.substitute operations p hp β')
      (operations.substitute (Vertical.Row.nonempty p hp) h k (ShortPath.empty d) β) := by
    apply (Vertical.substitute_heq_raw _ _ _ _).trans
    exact operations.substitute_heq rfl rfl (HEq.refl _) (HEq.refl _) (HEq.refl _) rfl
      ((CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _))
  exact e.symm.trans (heq_of_eq (substitute_vertical p hp β'))

/-- Normalize one substitution, including its dependent outer-cell input. -/
theorem substitute_as_stack {a b d : C} {f g : a ⟶ b}
    (r : (graph C).NonemptyRow ⟨a, b, f⟩ ⟨a, b, g⟩)
    (p : Vertical.Row (G := graph C) f g) (hp : 0 < p.length)
    (er : HEq r.val p.embed) (h k : b ⟶ d)
    (β : (graph C).Cell (CellGraph.Row.outerBoundary r h k (ShortPath.empty d)))
    (β' : Cell h k) (eβ : HEq β β') :
    HEq (operations.substitute r h k (ShortPath.empty d) β) (stack (rowFold p) β') := by
  have e := operations.substitute_heq (r := r) (r' := Vertical.Row.nonempty p hp)
    rfl rfl er (HEq.refl h) (HEq.refl k) rfl
    (eβ.trans (CellGraph.castInput_heq (Vertical.Row.embed_output p).symm β').symm)
  exact e.trans ((Vertical.substitute_heq_raw operations p hp β').symm.trans
    (heq_of_eq (substitute_vertical p hp β')))

theorem operations_insertion {f g k : Side C} (p : (graph C).Row f g)
    (q : (graph C).Row g k) (hn : 0 < (p.comp q).length)
    {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b) (L : ShortPath (fun _ _ : C => Empty) a b)
    (ψ : (graph C).Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    CellGraph.transport (operations.inserted_boundary p q hn h l L)
      (operations.insertedComposite p q hn h l L ψ) =
        operations.substitute ⟨p.comp q, hn⟩ h l L ψ := by
  rcases NoHorizontal.rowView p with ⟨x, y, f', g', p', hf, hg, ep⟩
  cases hf; cases hg
  have ep' : p = p'.embed := eq_of_heq ep
  subst p
  rcases NoHorizontal.rowViewFrom q with ⟨k', q', hk, eq⟩
  cases hk
  have eq' : q = q'.embed := eq_of_heq eq
  subst q
  rcases L with ⟨L, hL⟩
  cases L with
  | cons _ edge => exact Empty.elim edge
  | nil =>
    apply (CellGraph.transport_eq_iff_heq _ _ _).mpr
    have hout : CellGraph.Row.output (p'.embed.comp q'.embed) = .nil := by
      rw [CellGraph.Row.output_comp, Vertical.Row.embed_output, Vertical.Row.embed_output]
      rfl
    let ψ' : Cell h l := CellGraph.castInput (G := graph C)
      (f := ⟨y, a, h⟩) (g := ⟨y, a, l⟩) (L := ShortPath.empty a) hout ψ
    have hpq : 0 < (p'.comp q').length := by
      have en := congrArg (Quiver.Path.length (V := (graph C).Vertex))
        (Vertical.Row.embed_comp p' q')
      rw [Vertical.Row.embed_length] at en
      exact lt_of_lt_of_eq hn en.symm
    have hpi : 0 < ((p'.cons (identity g')).comp q').length := by
      rw [Quiver.Path.length_comp]
      exact Nat.add_pos_left (Nat.zero_lt_succ _) _
    have el := substitute_as_stack (operations.insertedRow p'.embed q'.embed)
      ((p'.cons (identity g')).comp q') hpi
      (heq_of_eq (Vertical.Row.embed_comp (p'.cons (identity g')) q').symm) h l
      (CellGraph.castInput (operations.insertedRow_output p'.embed q'.embed).symm ψ)
      ψ' ((CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _).symm)
    have er := substitute_as_stack ⟨p'.embed.comp q'.embed, hn⟩ (p'.comp q') hpq
      (heq_of_eq (Vertical.Row.embed_comp p' q').symm) h l ψ ψ'
      (CellGraph.castInput_heq _ _).symm
    erw [rowFold_comp, rowFold_cons, alongRow_identity, ← rowFold_comp] at el
    exact el.trans er.symm

/-- Folding a band of substitutions distributes over its two rows by interchange. -/
theorem rowFold_composite {a b d : C}
    {s t : Vertical.TwoBand.Vertex (graph C) a b d} (r : Vertical.TwoBand.Row s t) :
    rowFold (Vertical.TwoBand.composite operations r) =
      stack (rowFold (Vertical.TwoBand.inner r)) (rowFold (Vertical.TwoBand.outer r)) := by
  induction r with
  | nil => exact (stack_identity _ _).symm
  | cons r e ih =>
    change alongRow (rowFold (Vertical.TwoBand.composite operations r))
      (Vertical.substitute operations e.inner e.nonempty e.outer) =
      stack (rowFold ((Vertical.TwoBand.inner r).comp e.inner))
        (alongRow (rowFold (Vertical.TwoBand.outer r)) e.outer)
    erw [ih, substitute_vertical, rowFold_comp]
    exact interchange _ _ _ _

theorem operations_assoc {s t : Nested.Side C} (r : Nested.NonemptyRow (graph C) s t)
    {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath (fun _ _ : C => Empty) a b)
    (χ : (graph C).Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    CellGraph.transport (operations.assoc_boundary r p q L) (operations.assocLeft r p q L χ) =
      operations.assocRight r p q L χ := by
  rcases r with ⟨r, hn⟩
  rcases NoHorizontal.nestedViewFrom r with ⟨t', r', ht, he⟩
  cases ht
  have er : r = Vertical.TwoBand.embed r' := eq_of_heq he
  subst r
  rcases L with ⟨L, hL⟩
  cases L with
  | cons _ edge => exact Empty.elim edge
  | nil =>
    apply (CellGraph.transport_eq_iff_heq _ _ _).mpr
    let rr : Nested.NonemptyRow (graph C) s (Vertical.TwoBand.side t') :=
      ⟨Vertical.TwoBand.embed r', hn⟩
    have hi : 0 < (Vertical.TwoBand.inner r').length := by
      have hi := Nat.lt_of_lt_of_le hn (Nested.Row.length_le_inner (Vertical.TwoBand.embed r'))
      erw [Vertical.TwoBand.inner_embed, Vertical.Row.embed_length] at hi
      exact hi
    have ho : 0 < (Vertical.TwoBand.outer r').length := by
      have ho := rr.outer.property
      change 0 < (Nested.Row.outer (Vertical.TwoBand.embed r')).length at ho
      erw [Vertical.TwoBand.outer_embed, Vertical.Row.embed_length] at ho
      exact ho
    have hc : 0 < (Vertical.TwoBand.composite operations r').length := by
      have hc := (rr.composite operations).property
      change 0 < (Nested.Row.composite operations (Vertical.TwoBand.embed r')).length at hc
      erw [Vertical.TwoBand.composite_embed, Vertical.Row.embed_length] at hc
      exact hc
    have hout : CellGraph.Row.output rr.outer.val = .nil := by
      change CellGraph.Row.output (Nested.Row.outer (Vertical.TwoBand.embed r')) = .nil
      erw [Vertical.TwoBand.outer_embed, Vertical.Row.embed_output]
      rfl
    let χ' : Cell p q := CellGraph.castInput (G := graph C)
      (f := ⟨s.bottom, a, p⟩) (g := ⟨s.bottom, a, q⟩) (L := ShortPath.empty a) hout χ
    have el := substitute_as_stack (rr.composite operations)
      (Vertical.TwoBand.composite operations r') hc
      (heq_of_eq (Vertical.TwoBand.composite_embed operations r')) p q
      (CellGraph.castInput (Nested.Row.composite_output operations rr.val).symm χ) χ'
      ((CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _).symm)
    have eo := substitute_as_stack rr.outer (Vertical.TwoBand.outer r') ho
      (heq_of_eq (Vertical.TwoBand.outer_embed r')) p q χ χ' (CellGraph.castInput_heq _ _).symm
    have ei := substitute_as_stack rr.inner (Vertical.TwoBand.inner r') hi
      (heq_of_eq (Vertical.TwoBand.inner_embed r')) (s.lower ≫ p) (t'.2 ≫ q)
      (CellGraph.castInput (Nested.Row.inner_output rr.val).symm
        (operations.substitute rr.outer p q (ShortPath.empty a) χ))
      (stack (rowFold (Vertical.TwoBand.outer r')) χ')
      ((CellGraph.castInput_heq _ _).trans eo)
    erw [rowFold_composite] at el
    exact el.trans ((stack_assoc _ _ _).trans ei.symm)

/-- Every supplied strict 2-category gives a lawful augmented algebra with no horizontal edges. -/
def algebra : Algebra (graph C) where
  toOperations := operations
  laws := {
    verticalIdentity_stack := by intro a b d f g; exact (verticalStack_eq _ _).trans (stack_identity f g)
    leftUnit := operations_leftUnit
    rightUnit := operations_rightUnit
    insertion := operations_insertion
    assoc := operations_assoc
  }

end Kernel.Augmented.FromTwoCategory

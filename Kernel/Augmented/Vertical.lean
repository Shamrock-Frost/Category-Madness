import Kernel.Augmented.ComparisonTransport

/-! The vertical cells and their operations, derived from augmented substitution.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Vertical
universe u v h c
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

abbrev Cell {a b : C} (f g : a ⟶ b) := G.Cell (Boundary.vertical f g)

/-- The objects of a vertical hom category, with a separate quiver instance. -/
@[reducible] def Hom (_G : CellGraph.{u,v,h,c} C H) (a b : C) := a ⟶ b

instance (a b : C) : Quiver (Hom G a b) where
  Hom f g := Cell (G := G) f g

abbrev Row {a b : C} (f g : a ⟶ b) := Quiver.Path (V := Hom G a b) f g

namespace Row

def embed {a b : C} {f : a ⟶ b} : {g : a ⟶ b} → Row (G := G) f g →
    G.Row ⟨a, b, f⟩ ⟨a, b, g⟩
  | _, .nil => .nil
  | _, .cons r φ => (embed r).cons ⟨Boundary.vertical _ _, φ⟩

@[simp] theorem embed_length {a b : C} {f g : a ⟶ b} (r : Row (G := G) f g) :
    (embed r).length = r.length := by
  induction r with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

@[simp] theorem embed_input {a b : C} {f g : a ⟶ b} (r : Row (G := G) f g) :
    CellGraph.Row.input (embed r) = .nil := by
  induction r with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem embed_output {a b : C} {f g : a ⟶ b} (r : Row (G := G) f g) :
    CellGraph.Row.output (embed r) = .nil := by
  induction r with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem embed_comp {a b : C} {f g k : a ⟶ b}
    (p : Row (G := G) f g) (q : Row (G := G) g k) :
    embed (p.comp q) = (embed p).comp (embed q) := by
  induction q with
  | nil => rfl
  | cons q φ ih =>
    change (embed (p.comp q)).cons _ = ((embed p).comp (embed q)).cons _
    rw [ih]

def nonempty {a b : C} {f g : a ⟶ b} (r : Row (G := G) f g) (hr : 0 < r.length) :
    G.NonemptyRow ⟨a, b, f⟩ ⟨a, b, g⟩ := ⟨embed r, by simpa using hr⟩

theorem cons_heq {a b : C} {f g k f' g' k' : a ⟶ b}
    {r : Row (G := G) f g} {r' : Row (G := G) f' g'}
    {φ : Cell (G := G) g k} {φ' : Cell (G := G) g' k'}
    (hf : f = f') (hg : g = g') (hk : k = k')
    (hr : HEq r r') (hφ : HEq φ φ') : HEq (r.cons φ) (r'.cons φ') := by
  cases hf; cases hg; cases hk
  cases eq_of_heq hr; cases eq_of_heq hφ
  rfl

theorem nil_heq {a b : C} {f g : a ⟶ b} (e : f = g) :
    HEq (.nil : Row (G := G) f f) (.nil : Row (G := G) g g) := by cases e; rfl

end Row

variable (O : Operations G)

/-- Substitution of a vertical row into a vertical cell. -/
def substitute {a b d : C} {f g : a ⟶ b} (r : Row (G := G) f g)
    (hr : 0 < r.length) {h k : b ⟶ d} (β : Cell (G := G) h k) :
    Cell (G := G) (f ≫ h) (g ≫ k) :=
  CellGraph.castInput (Row.embed_input r)
    (O.substitute (Row.nonempty r hr) h k (ShortPath.empty d)
      (CellGraph.castInput (Row.embed_output r).symm β))

theorem substitute_heq_raw {a b d : C} {f g : a ⟶ b} (r : Row (G := G) f g)
    (hr : 0 < r.length) {h k : b ⟶ d} (β : Cell (G := G) h k) :
    HEq (substitute O r hr β)
      (O.substitute (Row.nonempty r hr) h k (ShortPath.empty d)
        (CellGraph.castInput (Row.embed_output r).symm β)) :=
  CellGraph.castInput_heq _ _

theorem outer_boundary {a b d : C} {f g : a ⟶ b} (r : Row (G := G) f g)
    (hr : 0 < r.length) (h k : b ⟶ d) :
    CellGraph.Row.outerBoundary (Row.nonempty r hr) h k (ShortPath.empty d) =
      Boundary.vertical h k := by
  simp only [CellGraph.Row.outerBoundary, Row.nonempty, Row.embed_output, Boundary.vertical]

theorem composite_boundary {a b d : C} {f g : a ⟶ b} (r : Row (G := G) f g)
    (hr : 0 < r.length) (h k : b ⟶ d) :
    CellGraph.Row.compositeBoundary (Row.nonempty r hr) h k (ShortPath.empty d) =
      Boundary.vertical (f ≫ h) (g ≫ k) := by
  simp only [CellGraph.Row.compositeBoundary, Row.nonempty, Row.embed_input, Boundary.vertical]
  rfl

def step {a b d : C} {f g : a ⟶ b} (r : Row (G := G) f g)
    (hr : 0 < r.length) {h k : b ⟶ d} (β : Cell (G := G) h k) :
    Nested.Step G ⟨⟨a, b, f⟩, d, h⟩ ⟨⟨a, b, g⟩, d, k⟩ :=
  ⟨Row.nonempty r hr, ShortPath.empty d,
    CellGraph.castInput (Row.embed_output r).symm β⟩

/-- Compose a nonempty row of vertical cells along its common pair of objects. -/
def compose {a b : C} {f g : a ⟶ b} (r : Row (G := G) f g) (hr : 0 < r.length) :
    Cell (G := G) f g :=
  cast (congrArg₂ (fun f g : a ⟶ b => Cell (G := G) f g)
    (Category.comp_id f) (Category.comp_id g))
    (substitute O r hr (O.verticalIdentity (𝟙 b)))

theorem stack_congr {a b d : C} {f g f' g' : a ⟶ b} {h k h' k' : b ⟶ d}
    {α : Cell (G := G) f g} {α' : Cell (G := G) f' g'}
    {β : Cell (G := G) h k} {β' : Cell (G := G) h' k'}
    (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (ha : HEq α α') (hb : HEq β β') :
    HEq (O.verticalStack α β) (O.verticalStack α' β') := by
  cases hf; cases hg; cases hh; cases hk
  cases eq_of_heq ha; cases eq_of_heq hb
  rfl

theorem substitute_congr {a b d : C} {f g f' g' : a ⟶ b} {h k h' k' : b ⟶ d}
    {r : Row (G := G) f g} {r' : Row (G := G) f' g'}
    (hr : 0 < r.length) (hr' : 0 < r'.length)
    {β : Cell (G := G) h k} {β' : Cell (G := G) h' k'}
    (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (er : HEq r r') (eb : HEq β β') :
    HEq (substitute O r hr β) (substitute O r' hr' β') := by
  cases hf; cases hg; cases hh; cases hk
  cases eq_of_heq er; cases eq_of_heq eb
  rfl

theorem compose_heq {a b : C} {f g : a ⟶ b} (r : Row (G := G) f g)
    (hr : 0 < r.length) :
    HEq (compose O r hr) (substitute O r hr (O.verticalIdentity (𝟙 b))) := cast_heq _ _

variable (A : Algebra G)

theorem stack_right_identity {a b : C} {f g : a ⟶ b} (α : Cell (G := G) f g) :
    HEq (A.verticalStack α (A.verticalIdentity (𝟙 b))) α := by
  exact A.laws.leftUnit_heq α

theorem stack_left_identity {a b : C} {f g : a ⟶ b} (α : Cell (G := G) f g) :
    HEq (A.verticalStack (A.verticalIdentity (𝟙 a)) α) α := by
  exact A.laws.rightUnit_heq α

@[simp] theorem compose_single {a b : C} {f g : a ⟶ b} (α : Cell (G := G) f g) :
    compose A.toOperations (Quiver.Path.cons .nil α) (Nat.zero_lt_succ _) = α := by
  apply eq_of_heq
  exact (compose_heq _ _ _).trans (stack_right_identity A α)

theorem compose_pair {a b : C} {f g k : a ⟶ b}
    (α : Cell (G := G) f g) (β : Cell (G := G) g k) :
    compose O (((.nil : Row (G := G) f f).cons α).cons β) (Nat.zero_lt_succ _) =
      O.verticalAlongRow α β := rfl

/-- The singleton nested row gives associativity of vertical stacking. -/
theorem stack_assoc {a b d e : C} {f f' : a ⟶ b} {g g' : b ⟶ d} {h h' : d ⟶ e}
    (α : Cell (G := G) f f') (β : Cell (G := G) g g') (γ : Cell (G := G) h h') :
    HEq (A.verticalStack (A.verticalStack α β) γ)
      (A.verticalStack α (A.verticalStack β γ)) := by
  let s : Nested.Side C := ⟨⟨a, b, f⟩, d, g⟩
  let t : Nested.Side C := ⟨⟨a, b, f'⟩, d, g'⟩
  let step : Nested.Step G s t := ⟨CellGraph.Row.single α, ShortPath.empty d, β⟩
  exact A.laws.assoc_heq ⟨Quiver.Path.cons .nil step, Nat.zero_lt_succ _⟩ h h'
    (ShortPath.empty e) γ

theorem identity_alongRow {a b : C} {f g : a ⟶ b} (α : Cell (G := G) f g) :
    A.verticalAlongRow (A.verticalIdentity f) α = α := by
  rw [← compose_pair]
  apply eq_of_heq
  apply (compose_heq A.toOperations
    (((.nil : Row (G := G) f f).cons (A.verticalIdentity f)).cons α) (Nat.zero_lt_succ 1)).trans
  exact (A.laws.insertion_heq .nil (CellGraph.Row.single α).val (Nat.zero_lt_succ _)
    (𝟙 b) (𝟙 b) (ShortPath.empty b) (A.verticalIdentity (𝟙 b))).trans
      (A.laws.leftUnit_heq α)

theorem alongRow_identity {a b : C} {f g : a ⟶ b} (α : Cell (G := G) f g) :
    A.verticalAlongRow α (A.verticalIdentity g) = α := by
  rw [← compose_pair]
  apply eq_of_heq
  apply (compose_heq A.toOperations
    (((.nil : Row (G := G) f f).cons α).cons (A.verticalIdentity g)) (Nat.zero_lt_succ 1)).trans
  exact (A.laws.insertion_heq (CellGraph.Row.single α).val .nil (Nat.zero_lt_succ _)
    (𝟙 b) (𝟙 b) (ShortPath.empty b) (A.verticalIdentity (𝟙 b))).trans
      (A.laws.leftUnit_heq α)

/-- Two incident blocks can be evaluated before or after their outer row. -/
theorem substitute_two_blocks {a b d e : C} {f₀ f₁ f₂ : a ⟶ b}
    (p : Row (G := G) f₀ f₁) (q : Row (G := G) f₁ f₂)
    (hp : 0 < p.length) (hq : 0 < q.length)
    {g₀ g₁ g₂ : b ⟶ d} (β : Cell (G := G) g₀ g₁) (β' : Cell (G := G) g₁ g₂)
    {h k : d ⟶ e} (γ : Cell (G := G) h k) :
    HEq (substitute A.toOperations
      (((.nil : Row (G := G) (f₀ ≫ g₀) (f₀ ≫ g₀)).cons
        (substitute A.toOperations p hp β)).cons (substitute A.toOperations q hq β'))
      (Nat.zero_lt_succ _) γ)
      (substitute A.toOperations (p.comp q)
        (by rw [Quiver.Path.length_comp (V := Hom G a b)]; exact Nat.add_pos_left hp _)
        (substitute A.toOperations
          (((.nil : Row (G := G) g₀ g₀).cons β).cons β') (Nat.zero_lt_succ _) γ)) := by
  let r : Nested.NonemptyRow G ⟨⟨a, b, f₀⟩, d, g₀⟩ ⟨⟨a, b, f₂⟩, d, g₂⟩ :=
    ⟨((Quiver.Path.cons (V := Nested.Vertex G) .nil (step p hp β)).cons (step q hq β')), Nat.zero_lt_succ _⟩
  have E := A.laws.assoc_heq r h k (ShortPath.empty e) γ
  let ps : Row (G := G) (f₀ ≫ g₀) (f₂ ≫ g₂) :=
    ((.nil : Row (G := G) (f₀ ≫ g₀) (f₀ ≫ g₀)).cons
      (substitute A.toOperations p hp β)).cons (substitute A.toOperations q hq β')
  let bs : Row (G := G) g₀ g₂ := ((.nil : Row (G := G) g₀ g₀).cons β).cons β'
  have hc : HEq (Row.embed ps) (Nested.Row.composite A.toOperations r.val) := by
    apply CellGraph.Row.cons_heq rfl rfl rfl
    · apply CellGraph.Row.cons_heq rfl rfl rfl (HEq.refl _)
      · exact heq_of_eq (composite_boundary p hp g₀ g₁).symm
      · exact substitute_heq_raw A.toOperations p hp β
    · exact heq_of_eq (composite_boundary q hq g₁ g₂).symm
    · exact substitute_heq_raw A.toOperations q hq β'
  have hb : HEq (Row.embed bs) (Nested.Row.outer r.val) := by
    apply CellGraph.Row.cons_heq rfl rfl rfl
    · apply CellGraph.Row.cons_heq rfl rfl rfl (HEq.refl _)
      · exact heq_of_eq (outer_boundary p hp g₀ g₁).symm
      · exact (CellGraph.castInput_heq (Row.embed_output p).symm β).symm
    · exact heq_of_eq (outer_boundary q hq g₁ g₂).symm
    · exact (CellGraph.castInput_heq (Row.embed_output q).symm β').symm
  have hi : (Row.embed (p.comp q)) = (Nested.Row.inner r.val) := by
    change Row.embed (p.comp q) = (Quiver.Path.nil.comp (Row.embed p)).comp (Row.embed q)
    exact (Row.embed_comp p q).trans
      (congrArg (fun t : G.Row ⟨a, b, f₀⟩ ⟨a, b, f₁⟩ => t.comp (Row.embed q))
        (Quiver.Path.nil_comp (V := G.Vertex) (Row.embed p))).symm
  have houter : HEq (substitute A.toOperations bs (Nat.zero_lt_succ _) γ)
      (A.substitute r.outer h k (ShortPath.empty e) γ) := by
    apply (substitute_heq_raw _ _ _ _).trans
    exact A.toOperations.substitute_heq (r' := r.outer) rfl rfl hb (HEq.refl _) (HEq.refl _) rfl
      (CellGraph.castInput_heq _ _)
  apply (substitute_heq_raw _ _ _ _).trans
  apply (A.toOperations.substitute_heq (r' := r.composite A.toOperations) rfl rfl hc (HEq.refl _) (HEq.refl _) rfl
    ((CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _).symm)).trans
  apply E.trans
  apply HEq.symm
  apply (substitute_heq_raw _ _ _ _).trans
  exact A.toOperations.substitute_heq (r' := r.inner) rfl rfl (heq_of_eq hi) (HEq.refl _) (HEq.refl _) rfl
    ((CellGraph.castInput_heq _ _).trans (houter.trans (CellGraph.castInput_heq _ _).symm))

/-- Associativity for an arbitrary inner row and a single outer cell. -/
theorem substitute_one_block {a b d e : C} {f f' : a ⟶ b}
    (p : Row (G := G) f f') (hp : 0 < p.length)
    {g g' : b ⟶ d} (β : Cell (G := G) g g')
    {h h' : d ⟶ e} (γ : Cell (G := G) h h') :
    HEq (A.verticalStack (substitute A.toOperations p hp β) γ)
      (substitute A.toOperations p hp (A.verticalStack β γ)) := by
  let r : Nested.NonemptyRow G ⟨⟨a, b, f⟩, d, g⟩ ⟨⟨a, b, f'⟩, d, g'⟩ :=
    ⟨Quiver.Path.cons (V := Nested.Vertex G) .nil (step p hp β), Nat.zero_lt_succ _⟩
  have E := A.laws.assoc_heq r h h' (ShortPath.empty e) γ
  have hc : HEq (CellGraph.Row.single (substitute A.toOperations p hp β)).val
      (Nested.Row.composite A.toOperations r.val) :=
    CellGraph.Row.cons_heq rfl rfl rfl (HEq.refl _)
      (heq_of_eq (composite_boundary p hp g g').symm)
      (substitute_heq_raw A.toOperations p hp β)
  have hb : HEq (CellGraph.Row.single β).val (Nested.Row.outer r.val) :=
    CellGraph.Row.cons_heq rfl rfl rfl (HEq.refl _)
      (heq_of_eq (outer_boundary p hp g g').symm)
      (CellGraph.castInput_heq (Row.embed_output p).symm β).symm
  have hi : (Row.embed p) = (Nested.Row.inner r.val) :=
    (Quiver.Path.nil_comp (V := G.Vertex) (Row.embed p)).symm
  have houter : HEq (A.verticalStack β γ)
      (A.substitute r.outer h h' (ShortPath.empty e) γ) :=
    A.toOperations.substitute_heq (r' := r.outer) rfl rfl hb
      (HEq.refl _) (HEq.refl _) rfl (HEq.refl _)
  apply (A.toOperations.substitute_heq (r' := r.composite A.toOperations) rfl rfl hc
    (HEq.refl _) (HEq.refl _) rfl (CellGraph.castInput_heq _ γ).symm).trans
  apply E.trans
  apply HEq.symm
  apply (substitute_heq_raw _ _ _ _).trans
  exact A.toOperations.substitute_heq (r' := r.inner) rfl rfl (heq_of_eq hi)
    (HEq.refl _) (HEq.refl _) rfl
    ((CellGraph.castInput_heq _ _).trans (houter.trans (CellGraph.castInput_heq _ _).symm))

/-- Every vertical substitution is row composition followed by stacking. -/
theorem substitute_eq_stack_compose {a b d : C} {f f' : a ⟶ b}
    (p : Row (G := G) f f') (hp : 0 < p.length)
    {g g' : b ⟶ d} (β : Cell (G := G) g g') :
    substitute A.toOperations p hp β = A.verticalStack (compose A.toOperations p hp) β := by
  have E := substitute_one_block A p hp (A.verticalIdentity (𝟙 b)) β
  have hl := stack_congr A.toOperations (Category.comp_id f) (Category.comp_id f') rfl rfl
    (compose_heq A.toOperations p hp).symm (HEq.refl β)
  have hr := substitute_congr A.toOperations hp hp rfl rfl
    (Category.id_comp g) (Category.id_comp g') (HEq.refl p) (stack_left_identity A β)
  exact eq_of_heq (hr.symm.trans (E.symm.trans hl))

/-- Concatenating nonempty rows agrees with composing their individual composites. -/
theorem compose_comp {a b : C} {f₀ f₁ f₂ : a ⟶ b}
    (p : Row (G := G) f₀ f₁) (q : Row (G := G) f₁ f₂)
    (hp : 0 < p.length) (hq : 0 < q.length) :
    A.verticalAlongRow (compose A.toOperations p hp) (compose A.toOperations q hq) =
      compose A.toOperations (p.comp q)
        (by rw [Quiver.Path.length_comp (V := Hom G a b)]; exact Nat.add_pos_left hp _) := by
  have E := substitute_two_blocks A p q hp hq
    (A.verticalIdentity (𝟙 b)) (A.verticalIdentity (𝟙 b)) (A.verticalIdentity (𝟙 b))
  have hrow : HEq
      (((.nil : Row (G := G) (f₀ ≫ 𝟙 b) (f₀ ≫ 𝟙 b)).cons
        (substitute A.toOperations p hp (A.verticalIdentity (𝟙 b)))).cons
        (substitute A.toOperations q hq (A.verticalIdentity (𝟙 b))))
      (((.nil : Row (G := G) f₀ f₀).cons (compose A.toOperations p hp)).cons
        (compose A.toOperations q hq)) :=
    Row.cons_heq (Category.comp_id _) (Category.comp_id _) (Category.comp_id _)
      (Row.cons_heq (Category.comp_id _) (Category.comp_id _) (Category.comp_id _)
        (Row.nil_heq (Category.comp_id _)) (compose_heq _ _ _).symm)
      (compose_heq _ _ _).symm
  have hl := substitute_congr A.toOperations
    (r := (((.nil : Row (G := G) (f₀ ≫ 𝟙 b) (f₀ ≫ 𝟙 b)).cons
      (substitute A.toOperations p hp (A.verticalIdentity (𝟙 b)))).cons
      (substitute A.toOperations q hq (A.verticalIdentity (𝟙 b)))))
    (r' := (((.nil : Row (G := G) f₀ f₀).cons (compose A.toOperations p hp)).cons
      (compose A.toOperations q hq)))
    (Nat.zero_lt_succ 1) (Nat.zero_lt_succ 1)
    (Category.comp_id f₀) (Category.comp_id f₂) rfl rfl hrow
    (HEq.refl (A.verticalIdentity (𝟙 b)))
  have hid : HEq (substitute A.toOperations
      (((.nil : Row (G := G) (𝟙 b) (𝟙 b)).cons (A.verticalIdentity (𝟙 b))).cons
        (A.verticalIdentity (𝟙 b))) (Nat.zero_lt_succ 1) (A.verticalIdentity (𝟙 b)))
      (A.verticalIdentity (𝟙 b)) :=
    (compose_heq _ _ _).symm.trans
      (heq_of_eq ((compose_pair _ _ _).trans (identity_alongRow A _)))
  have hpq : 0 < (p.comp q).length := by
    rw [Quiver.Path.length_comp (V := Hom G a b)]
    exact Nat.add_pos_left hp _
  have hr := substitute_congr A.toOperations hpq hpq rfl rfl
    (Category.id_comp (𝟙 b)) (Category.id_comp (𝟙 b)) (HEq.refl (p.comp q)) hid
  apply eq_of_heq
  rw [← compose_pair]
  exact (compose_heq _ _ _).trans (hl.symm.trans (E.trans (hr.trans (compose_heq _ _ _).symm)))

theorem alongRow_assoc {a b : C} {f₀ f₁ f₂ f₃ : a ⟶ b}
    (α : Cell (G := G) f₀ f₁) (β : Cell (G := G) f₁ f₂) (γ : Cell (G := G) f₂ f₃) :
    A.verticalAlongRow (A.verticalAlongRow α β) γ =
      A.verticalAlongRow α (A.verticalAlongRow β γ) := by
  have hl := compose_comp A (((.nil : Row (G := G) f₀ f₀).cons α).cons β)
    ((.nil : Row (G := G) f₂ f₂).cons γ) (Nat.zero_lt_succ 1) (Nat.zero_lt_succ 0)
  have hr := compose_comp A ((.nil : Row (G := G) f₀ f₀).cons α)
    (((.nil : Row (G := G) f₁ f₁).cons β).cons γ) (Nat.zero_lt_succ 0) (Nat.zero_lt_succ 1)
  simpa only [compose_pair, compose_single] using hl.trans hr.symm

/-- The two compositions satisfy the middle-four interchange law. -/
theorem interchange {a b d : C} {f₀ f₁ f₂ : a ⟶ b} {g₀ g₁ g₂ : b ⟶ d}
    (α : Cell (G := G) f₀ f₁) (α' : Cell (G := G) f₁ f₂)
    (β : Cell (G := G) g₀ g₁) (β' : Cell (G := G) g₁ g₂) :
    A.verticalAlongRow (A.verticalStack α β) (A.verticalStack α' β') =
      A.verticalStack (A.verticalAlongRow α α') (A.verticalAlongRow β β') := by
  let p : Row (G := G) f₀ f₁ := .cons .nil α
  let q : Row (G := G) f₁ f₂ := .cons .nil α'
  let bs : Row (G := G) g₀ g₂ := ((.nil : Row (G := G) g₀ g₀).cons β).cons β'
  have E := substitute_two_blocks A p q (Nat.zero_lt_succ 0) (Nat.zero_lt_succ 0)
    β β' (A.verticalIdentity (𝟙 d))
  have hβ : HEq (substitute A.toOperations bs (Nat.zero_lt_succ 1)
      (A.verticalIdentity (𝟙 d))) (A.verticalAlongRow β β') :=
    (compose_heq _ _ _).symm
  have hr := substitute_congr A.toOperations (r := p.comp q) (r' := p.comp q)
    (Nat.zero_lt_succ 1) (Nat.zero_lt_succ 1) rfl rfl
    (Category.comp_id g₀) (Category.comp_id g₂) (HEq.refl (p.comp q)) hβ
  apply eq_of_heq
  rw [← compose_pair A.toOperations (A.verticalStack α β) (A.verticalStack α' β')]
  exact (compose_heq _ _ _).trans (E.trans (hr.trans
    (heq_of_eq (substitute_eq_stack_compose A (p.comp q) (Nat.zero_lt_succ 1)
      (A.verticalAlongRow β β')))))

/-- Every augmented algebra has actual categories of vertical arrows and cells. -/
@[instance_reducible] def homCategory (a b : C) : Category.{c} (Hom G a b) where
  Hom f g := Cell (G := G) f g
  id f := A.verticalIdentity f
  comp α β := A.verticalAlongRow α β
  id_comp := identity_alongRow A
  comp_id := alongRow_identity A
  assoc := alongRow_assoc A

end Kernel.Augmented.Vertical

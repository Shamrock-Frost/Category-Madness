import Kernel.Augmented.NestedRows

/-! Set-level augmented VDC equations on the incident operation data.
Reference: Koudenburg, arXiv:1910.11189v4, Definition 1.2.
Cites: D-KR-18, D-RT-30, D-TL-21, AT-FD-7.

Equation instances retain every incident path and vertical side. Each equation uses the central cell transport along a proved equality of
complete boundaries. Boundary proofs are independent of the algebra laws. This is
an algebra presentation, not a free/arity or nerve theorem.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c


namespace Operations
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def leftUnitComposite (O : Operations G) {f g : Side C} {b : Boundary H f g}
    (φ : G.Cell b) : G.Cell (CellGraph.Row.compositeBoundary (CellGraph.Row.single φ)
      (𝟙 f.target) (𝟙 g.target) b.output) :=
  O.substitute (CellGraph.Row.single φ) (𝟙 f.target) (𝟙 g.target) b.output
    (CellGraph.castInput (CellGraph.Row.output_single φ).symm (O.shortIdentity b.output))

def rightUnitComposite (O : Operations G) {f g : Side C} {b : Boundary H f g}
    (φ : G.Cell b) : G.Cell (CellGraph.Row.compositeBoundary (O.identityRow b.input)
      f.arrow g.arrow b.output) :=
  O.substitute (O.identityRow b.input) f.arrow g.arrow b.output
    (CellGraph.castInput (O.identityRow_output b.input).symm φ)

def insertedComposite (O : Operations G) {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) (hn : 0 < (p.comp q).length)
    {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    G.Cell (CellGraph.Row.compositeBoundary (O.insertedRow p q) h l L) :=
  O.substitute (O.insertedRow p q) h l L
    (CellGraph.castInput (O.insertedRow_output p q).symm ψ)

def assocLeft (O : Operations G) {s t : Nested.Side C} (r : Nested.NonemptyRow G s t)
    {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath H a b)
    (χ : G.Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    G.Cell (CellGraph.Row.compositeBoundary (r.composite O) p q L) :=
  O.substitute (r.composite O) p q L
    (CellGraph.castInput (Nested.Row.composite_output O r.val).symm χ)

def assocRight (O : Operations G) {s t : Nested.Side C} (r : Nested.NonemptyRow G s t)
    {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath H a b)
    (χ : G.Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    G.Cell (CellGraph.Row.compositeBoundary r.inner (s.lower ≫ p) (t.lower ≫ q) L) :=
  O.substitute r.inner (s.lower ≫ p) (t.lower ≫ q) L
    (CellGraph.castInput (Nested.Row.inner_output r.val).symm
      (O.substitute r.outer p q L χ))

theorem leftUnit_boundary {f g : Side C} {b : Boundary H f g}
    (φ : G.Cell b) :
    (CellGraph.Row.compositeBoundary (CellGraph.Row.single φ)
      (𝟙 f.target) (𝟙 g.target) b.output).frame = b.frame :=
  Boundary.frame_eq (Side.post_id f) (Side.post_id g)
    (heq_of_eq (CellGraph.Row.input_single φ)) (HEq.refl _)

theorem rightUnit_boundary (O : Operations G) {f g : Side C} (b : Boundary H f g) :
    (CellGraph.Row.compositeBoundary (O.identityRow b.input)
      f.arrow g.arrow b.output).frame = b.frame := by
  refine Boundary.frame_eq (b := CellGraph.Row.compositeBoundary (O.identityRow b.input)
    f.arrow g.arrow b.output) (b' := b) ?_ ?_
    (heq_of_eq (O.identityRow_input b.input)) (HEq.refl _)
  · cases f
    simp [Side.post]
  · cases g
    simp [Side.post]

theorem inserted_boundary (O : Operations G) {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) (hn : 0 < (p.comp q).length)
    {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b) (L : ShortPath H a b) :
    (CellGraph.Row.compositeBoundary (O.insertedRow p q) h l L).frame =
      (CellGraph.Row.compositeBoundary ⟨p.comp q, hn⟩ h l L).frame :=
  Boundary.frame_eq rfl rfl (heq_of_eq (O.insertedRow_input p q)) (HEq.refl _)

theorem assoc_boundary (O : Operations G) {s t : Nested.Side C}
    (r : Nested.NonemptyRow G s t) {a b : C}
    (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath H a b) :
    (CellGraph.Row.compositeBoundary (r.composite O) p q L).frame =
      (CellGraph.Row.compositeBoundary r.inner (s.lower ≫ p) (t.lower ≫ q) L).frame :=
  Boundary.frame_eq (Side.post_assoc s.upper s.lower p) (Side.post_assoc t.upper t.lower q)
    (heq_of_eq (Nested.Row.composite_input O r.val)) (HEq.refl _)

end Operations

/-- Definition 1.2's equation families, over the explicitly incident domains. -/
class Laws {C : Type u} [Category.{v} C] {H : C → C → Type h}
    {G : CellGraph.{u,v,h,c} C H} (O : Operations G) : Prop where
  verticalIdentity_stack : ∀ {a b d : C} (f : a ⟶ b) (g : b ⟶ d),
    O.verticalStack (O.verticalIdentity f) (O.verticalIdentity g) = O.verticalIdentity (f ≫ g)
  leftUnit : ∀ {f g : Side C} {b : Boundary H f g} (φ : G.Cell b),
    CellGraph.transport (Operations.leftUnit_boundary φ) (O.leftUnitComposite φ) = φ
  rightUnit : ∀ {f g : Side C} {b : Boundary H f g} (φ : G.Cell b),
    CellGraph.transport (O.rightUnit_boundary b) (O.rightUnitComposite φ) = φ
  insertion : ∀ {f g k : Side C} (p : G.Row f g) (q : G.Row g k)
    (hn : 0 < (p.comp q).length) {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b)
    (L : ShortPath H a b) (ψ : G.Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)),
    CellGraph.transport (O.inserted_boundary p q hn h l L)
      (O.insertedComposite p q hn h l L ψ) = O.substitute ⟨p.comp q, hn⟩ h l L ψ
  assoc : ∀ {s t : Nested.Side C} (r : Nested.NonemptyRow G s t)
    {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b) (L : ShortPath H a b)
    (χ : G.Cell (CellGraph.Row.outerBoundary r.outer p q L)),
    CellGraph.transport (O.assoc_boundary r p q L) (O.assocLeft r p q L χ) =
      O.assocRight r p q L χ

/-- Set-level augmented operation data satisfying all the displayed equation families. -/
structure Algebra {C : Type u} [Category.{v} C] {H : C → C → Type h}
    (G : CellGraph.{u,v,h,c} C H) extends Operations G where
  laws : Laws toOperations

end Kernel.Augmented

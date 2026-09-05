import Kernel.Augmented.NoHorizontalRows

/-! Two-band vertical rows and their exact incident-row presentation.
Cites: D-KR-18, D-RT-30, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

namespace Vertical.TwoBand
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def Vertex (_G : CellGraph.{u,v,h,c} C H) (a b d : C) := (a ⟶ b) × (b ⟶ d)

structure Step {a b d : C} (s t : Vertex G a b d) where
  inner : Vertical.Row (G := G) s.1 t.1
  nonempty : 0 < inner.length
  outer : Vertical.Cell (G := G) s.2 t.2

instance {a b d : C} : Quiver (Vertex G a b d) where
  Hom s t := Step s t

abbrev Row {a b d : C} (s t : Vertex G a b d) := Quiver.Path s t

def side {a b d : C} (s : Vertex G a b d) : Nested.Side C := ⟨⟨a, b, s.1⟩, d, s.2⟩

def embed {a b d : C} {s : Vertex G a b d} : {t : Vertex G a b d} →
    Row s t → Nested.Row G (side s) (side t)
  | _, .nil => .nil
  | _, .cons r e => (embed r).cons (Vertical.step e.inner e.nonempty e.outer)

def inner {a b d : C} {s : Vertex G a b d} : {t : Vertex G a b d} →
    Row s t → Vertical.Row (G := G) s.1 t.1
  | _, .nil => .nil
  | _, .cons r e => (inner r).comp e.inner

def outer {a b d : C} {s : Vertex G a b d} : {t : Vertex G a b d} →
    Row s t → Vertical.Row (G := G) s.2 t.2
  | _, .nil => .nil
  | _, .cons r e => (outer r).cons e.outer

def composite (O : Operations G) {a b d : C} {s : Vertex G a b d} :
    {t : Vertex G a b d} → Row s t → Vertical.Row (G := G) (s.1 ≫ s.2) (t.1 ≫ t.2)
  | _, .nil => .nil
  | _, .cons r e => (composite O r).cons (Vertical.substitute O e.inner e.nonempty e.outer)

@[simp] theorem embed_length {a b d : C} {s t : Vertex G a b d} (r : Row s t) :
    (embed r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

@[simp] theorem inner_embed {a b d : C} {s t : Vertex G a b d} (r : Row s t) :
    Nested.Row.inner (embed r) = (inner r).embed := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (Nested.Row.inner (embed r)).comp e.inner.embed =
      Vertical.Row.embed ((inner r).comp e.inner)
    rw [ih, Vertical.Row.embed_comp]
    rfl

@[simp] theorem outer_embed {a b d : C} {s t : Vertex G a b d} (r : Row s t) :
    Nested.Row.outer (embed r) = (outer r).embed := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    apply eq_of_heq
    exact CellGraph.Row.cons_heq rfl rfl rfl (heq_of_eq ih)
      (heq_of_eq (Vertical.outer_boundary e.inner e.nonempty _ _))
      (CellGraph.castInput_heq (Vertical.Row.embed_output e.inner).symm e.outer)

@[simp] theorem composite_embed (O : Operations G) {a b d : C}
    {s t : Vertex G a b d} (r : Row s t) :
    Nested.Row.composite O (embed r) = (composite O r).embed := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    apply eq_of_heq
    exact CellGraph.Row.cons_heq rfl rfl rfl (heq_of_eq ih)
      (heq_of_eq (Vertical.composite_boundary e.inner e.nonempty _ _))
      (Vertical.substitute_heq_raw O _ _ _).symm

end Vertical.TwoBand

namespace NoHorizontal
variable {C : Type u} [Category.{v} C]
  {G : CellGraph.{u,v,0,c} C (fun _ _ : C => Empty)}
open Vertical.TwoBand

structure NestedViewFrom (s : Nested.Side C) {t : Nested.Side C} (r : Nested.Row G s t) where
  right : Vertex G s.upper.source s.upper.target s.bottom
  row : Row (⟨s.upper.arrow, s.lower⟩ : Vertex G s.upper.source s.upper.target s.bottom) right
  right_eq : t = side right
  embed_heq : HEq r (embed row)

def nestedViewFrom {s : Nested.Side C} : {t : Nested.Side C} →
    (r : Nested.Row G s t) → NestedViewFrom s r
  | _, .nil => ⟨⟨s.upper.arrow, s.lower⟩, .nil, rfl, HEq.refl _⟩
  | t, .cons r e => by
    rcases nestedViewFrom r with ⟨q, r', ht, hr⟩
    cases ht
    rcases t with ⟨t, d, k⟩
    rcases e with ⟨⟨p, hp⟩, ⟨L, hL⟩, β⟩
    rcases rowViewFrom p with ⟨f, p', hf, he⟩
    cases hf
    have ep : p = p'.embed := eq_of_heq he
    subst p
    cases L with
    | cons _ edge => exact Empty.elim edge
    | nil =>
      have hp' : 0 < p'.length := by simpa only [Vertical.Row.embed_length] using hp
      let β' : Vertical.Cell (G := G) q.2 k :=
        CellGraph.castInput (G := G) (f := ⟨s.upper.target, s.bottom, q.2⟩)
          (g := ⟨s.upper.target, s.bottom, k⟩) (L := ShortPath.empty s.bottom)
          (Vertical.Row.embed_output p') β
      refine ⟨⟨f, k⟩, r'.cons ⟨p', hp', β'⟩, rfl, ?_⟩
      have er : r = embed r' := eq_of_heq hr
      subst r
      apply heq_of_eq
      change Quiver.Path.cons (V := Nested.Vertex G) (embed r') _ =
        Quiver.Path.cons (V := Nested.Vertex G) (embed r') _
      congr 1
      unfold Vertical.step β'
      erw [CellGraph.castInput_trans]
      rfl
      all_goals exact Vertical.Row.embed_output p'

end NoHorizontal
end Kernel.Augmented

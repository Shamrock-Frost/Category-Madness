import Mathlib.Combinatorics.Quiver.Path
import Mathlib.CategoryTheory.Category.Basic

/-! Generating incidence data for set-level augmented virtual double categories.
Reference: Koudenburg, arXiv:1910.11189v4, Definition 1.2.
Cites: D-KR-18, D-RT-30, D-TL-21, AT-FD-7.

Only the incidence signature is defined here. In particular, a bare vertical
quiver suffices; category operations, cell substitution and its equations are
additional structure. No row encoding is asserted to be a canonical arity.
-/

open CategoryTheory

namespace Kernel.Augmented
universe u v h c w

-- A type synonym keeps the two quiver instances distinct during elaboration.
def Horizontal {C : Type u} (_H : C → C → Type h) := C

instance {C : Type u} (H : C → C → Type h) : Quiver (Horizontal H) where
  Hom a b := H a b

/-- Paths in the horizontal graph, independent of the vertical quiver. -/
abbrev HPath {C : Type u} (H : C → C → Type h) (a b : C) :=
  Quiver.Path (V := Horizontal H) a b

namespace HPath
variable {C : Type u} {H : C → C → Type h} {a b : C}

def single (j : H a b) : HPath H a b := .cons .nil j

@[simp] theorem length_single (j : H a b) : (single j).length = 1 := rfl
end HPath

/-- A horizontal target is a full incident path of length zero or one. -/
abbrev ShortPath {C : Type u} (H : C → C → Type h) (a b : C) :=
  { p : HPath H a b // p.length ≤ 1 }

namespace ShortPath
variable {C : Type u} {H : C → C → Type h} {a b : C}

def empty (a : C) : ShortPath H a a := ⟨.nil, Nat.zero_le _⟩

def single (j : H a b) : ShortPath H a b := ⟨HPath.single j, Nat.le_refl _⟩

/-- Empty targets identify their endpoint objects; a Boolean flag alone does not. -/
theorem endpoints_eq (p : ShortPath H a b) (hp : p.val.length = 0) : a = b :=
  Quiver.Path.eq_of_length_zero (V := Horizontal H) p.val hp

/-- Dependent elimination into either incident form, including data-valued motives. -/
def elim (P : {a b : C} → ShortPath H a b → Sort w)
    (hnil : ∀ a, P (empty a)) (hone : ∀ {a b} (j : H a b), P (single j))
    {a b : C} (p : ShortPath H a b) : P p := by
  rcases p with ⟨p, hp⟩
  cases p with
  | nil => exact hnil a
  | @cons b d p j =>
    have hz : Quiver.Path.length (V := Horizontal H) p = 0 := by
      change Quiver.Path.length (V := Horizontal H) p + 1 ≤ 1 at hp
      omega
    obtain rfl := Quiver.Path.eq_of_length_zero (V := Horizontal H) p hz
    have he := Quiver.Path.eq_nil_of_length_zero (V := Horizontal H) p hz
    subst p
    exact hone j

/-- There are precisely the two incident forms specified in Definition 1.2. -/
theorem cases_on (P : {a b : C} → ShortPath H a b → Prop)
    (hnil : ∀ a, P (empty a)) (hone : ∀ {a b} (j : H a b), P (single j))
    {a b : C} (p : ShortPath H a b) : P p := elim P hnil hone p
end ShortPath

/-- A row endpoint remembers the complete vertical arrow, not just its objects. -/
structure Side (C : Type u) [Quiver.{v} C] where
  source : C
  target : C
  arrow : source ⟶ target

/-- Ordered horizontal input and a zero/one-output path with all four incidences. -/
structure Boundary {C : Type u} [Quiver.{v} C] (H : C → C → Type h)
    (left right : Side C) where
  input : HPath H left.source right.source
  output : ShortPath H left.target right.target

namespace Boundary
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {left right : Side C}

def arity (b : Boundary H left right) : ℕ × ℕ := (b.input.length, b.output.val.length)

theorem output_le_one (b : Boundary H left right) : b.arity.2 ≤ 1 := b.output.property

/-- A vertical cell is exactly an empty/empty boundary between parallel arrows. -/
def vertical {a b : C} (f g : a ⟶ b) :
    Boundary H ⟨a, b, f⟩ ⟨a, b, g⟩ := ⟨.nil, ShortPath.empty b⟩

@[simp] theorem vertical_arity {a b : C} (f g : a ⟶ b) :
    (vertical (H := H) f g).arity = (0, 0) := rfl

theorem vertical_parallel (b : Boundary H left right) (hb : b.arity = (0, 0)) :
    left.source = right.source ∧ left.target = right.target := by
  exact ⟨Quiver.Path.eq_of_length_zero (V := Horizontal H) b.input (congrArg Prod.fst hb),
    Quiver.Path.eq_of_length_zero (V := Horizontal H) b.output.val (congrArg Prod.snd hb)⟩

end Boundary

namespace Boundary
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}

/-- Bundle the sides too when comparing dependent boundaries. -/
def frame {f g : Side C} (b : Boundary H f g) :
    Σ f : Side C, Σ g : Side C, Boundary H f g := ⟨f, g, b⟩

theorem frame_eq {f g f' g' : Side C} {b : Boundary H f g} {b' : Boundary H f' g'}
    (hf : f = f') (hg : g = g') (hi : HEq b.input b'.input)
    (ho : HEq b.output b'.output) : b.frame = b'.frame := by
  cases hf
  cases hg
  cases b
  cases b'
  cases eq_of_heq hi
  cases eq_of_heq ho
  rfl
end Boundary

/-- Cell generators indexed by their full boundary; no cell equations are assumed. -/
structure CellGraph (C : Type u) [Quiver.{v} C] (H : C → C → Type h) where
  Cell : {left right : Side C} → Boundary H left right → Type c

namespace CellGraph
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}

def Vertex (_G : CellGraph.{u,v,h,c} C H) := Side C

instance quiver (G : CellGraph.{u,v,h,c} C H) : Quiver G.Vertex where
  Hom left right := Σ b : Boundary H left right, G.Cell b

/-- Paths of generators share the entire intermediate vertical side by construction. -/
abbrev Row (G : CellGraph.{u,v,h,c} C H) (left right : Side C) :=
  Quiver.Path (V := G.Vertex) left right

/-- Substitution uses a positive number of cells, even for empty horizontal input. -/
abbrev NonemptyRow (G : CellGraph.{u,v,h,c} C H) (left right : Side C) :=
  { r : G.Row left right // 0 < r.length }

end CellGraph
end Kernel.Augmented

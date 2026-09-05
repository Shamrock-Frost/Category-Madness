import Kernel.Augmented.Rows

/-! Primitive operations with their full incidence types.
Reference: Koudenburg, arXiv:1910.11189v4, Definition 1.2.
Cites: D-KR-18, D-RT-30, AT-FD-7.

This record is operation data, not an augmented-VDC algebra: the complete
associativity and identity-insertion equations remain to be formalized.
No free monad, canonical arity, or nerve theorem is inferred from it.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c

namespace Boundary
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}

def horizontalIdentity {a b : C} (J : H a b) :
    Boundary H ⟨a, a, 𝟙 a⟩ ⟨b, b, 𝟙 b⟩ :=
  ⟨HPath.single J, ShortPath.single J⟩
end Boundary

structure Operations {C : Type u} [Category.{v} C] {H : C → C → Type h}
    (G : CellGraph.{u,v,h,c} C H) where
  horizontalIdentity : {a b : C} → (J : H a b) → G.Cell (Boundary.horizontalIdentity J)
  verticalIdentity : {a b : C} → (f : a ⟶ b) → G.Cell (Boundary.vertical f f)
  substitute : {f g : Side C} → (r : G.NonemptyRow f g) →
    {a b : C} → (h : f.target ⟶ a) → (k : g.target ⟶ b) → (L : ShortPath H a b) →
    G.Cell (CellGraph.Row.outerBoundary r h k L) →
    G.Cell (CellGraph.Row.compositeBoundary r h k L)

namespace Operations
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

/-- Stacking two (0,0)-cells is a special case of nonempty-row substitution. -/
def verticalStack (O : Operations G) {a b d : C} {f g : a ⟶ b} {h k : b ⟶ d}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical h k)) :
    G.Cell (Boundary.vertical (f ≫ h) (g ≫ k)) :=
  O.substitute (CellGraph.Row.single α) h k (ShortPath.empty d) β

/-- Along-row composition of (0,0)-cells substitutes into the identity of an object.
This is the other vertical-cell composition; its laws require the algebra equations. -/
def verticalAlongRow (O : Operations G) {a b : C} {f g k : a ⟶ b}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical g k)) :
    G.Cell (Boundary.vertical f k) := by
  let r : G.NonemptyRow ⟨a, b, f⟩ ⟨a, b, k⟩ :=
    ⟨((Quiver.Path.nil : G.Row ⟨a, b, f⟩ ⟨a, b, f⟩).cons
      ⟨Boundary.vertical f g, α⟩).cons ⟨Boundary.vertical g k, β⟩, Nat.zero_lt_succ _⟩
  have value : G.Cell (Boundary.vertical (f ≫ 𝟙 b) (k ≫ 𝟙 b)) :=
    O.substitute r (𝟙 b) (𝟙 b) (ShortPath.empty b) (O.verticalIdentity (𝟙 b))
  exact (congrArg₂ (fun (s t : a ⟶ b) => G.Cell (Boundary.vertical s t))
    (Category.comp_id f) (Category.comp_id k)).mp value

end Operations
end Kernel.Augmented

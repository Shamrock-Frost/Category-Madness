import Kernel.Augmented.Incidence

/-! Transport cells along equality of their complete incident boundaries.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c w

namespace CellGraph
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H}

def family (G : CellGraph.{u,v,h,c} C H)
    (b : Σ f : Side C, Σ g : Side C, Boundary H f g) : Type c := G.Cell b.2.2

def transport {f g f' g' : Side C} {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) (φ : G.Cell b) : G.Cell b' :=
  cast (congrArg G.family e) φ

theorem transport_heq {f g f' g' : Side C} {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) (φ : G.Cell b) : HEq (transport e φ) φ := cast_heq _ _

@[simp] theorem transport_refl {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) :
    transport rfl φ = φ := rfl

@[simp] theorem transport_trans {f g f' g' f'' g'' : Side C}
    {b : Boundary H f g} {b' : Boundary H f' g'} {b'' : Boundary H f'' g''}
    (e : b.frame = b'.frame) (e' : b'.frame = b''.frame) (φ : G.Cell b) :
    transport e' (transport e φ) = transport (e.trans e') φ := by
  exact eq_of_heq ((transport_heq e' _).trans
    ((transport_heq e φ).trans (transport_heq (e.trans e') φ).symm))

@[simp] theorem transport_symm {f g f' g' : Side C}
    {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) (φ : G.Cell b) : transport e.symm (transport e φ) = φ := by
  rw [transport_trans]
  rfl

/-- Heterogeneous equality is confined to comparison adapters; an equation here
also requires equality of the complete boundaries. -/
theorem transport_eq_iff_heq {f g f' g' : Side C}
    {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) (φ : G.Cell b) (ψ : G.Cell b') :
    transport e φ = ψ ↔ HEq φ ψ := by
  constructor
  · intro h
    exact (transport_heq e φ).symm.trans (heq_of_eq h)
  · intro h
    exact eq_of_heq ((transport_heq e φ).trans h)

theorem transport_injective {f g f' g' : Side C}
    {b : Boundary H f g} {b' : Boundary H f' g'} (e : b.frame = b'.frame) :
    Function.Injective (transport (G := G) e) := by
  intro φ ψ h
  have hh := congrArg (transport e.symm) h
  simpa only [transport_symm] using hh


end CellGraph

namespace CellGraph
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {f g : Side C}

/-- Transport only the input path, keeping all other incidence fixed. -/
def castInput {J K : HPath H f.source g.source} {L : ShortPath H f.target g.target}
    (e : J = K) (φ : G.Cell (⟨J, L⟩ : Boundary H f g)) :
    G.Cell (⟨K, L⟩ : Boundary H f g) :=
  transport (congrArg (fun p => (⟨p, L⟩ : Boundary H f g).frame) e) φ

@[simp] theorem castInput_refl {b : Boundary H f g} (φ : G.Cell b) :
    castInput rfl φ = φ := rfl

theorem castInput_heq {J K : HPath H f.source g.source}
    {L : ShortPath H f.target g.target} (e : J = K)
    (φ : G.Cell (⟨J, L⟩ : Boundary H f g)) : HEq (castInput e φ) φ := by
  cases e
  rfl

theorem castInput_eq_transport {J K : HPath H f.source g.source}
    {L : ShortPath H f.target g.target} (e : J = K)
    (φ : G.Cell (⟨J, L⟩ : Boundary H f g)) :
    castInput e φ = transport (congrArg (fun p => (⟨p, L⟩ : Boundary H f g).frame) e) φ := by
  cases e
  rfl

@[simp] theorem castInput_trans {J K M : HPath H f.source g.source}
    {L : ShortPath H f.target g.target} (e : J = K) (e' : K = M)
    (φ : G.Cell (⟨J, L⟩ : Boundary H f g)) :
    castInput e' (castInput e φ) = castInput (e.trans e') φ := by
  cases e; cases e'
  rfl
end CellGraph

namespace Boundary
variable {C : Type u} [Quiver.{v} C]

/-- Every boundary over the empty horizontal graph is a vertical boundary. -/
def emptyElim
    (P : {f g : Side C} → Boundary (fun _ _ : C => Empty) f g → Sort w)
    (hv : ∀ {a b : C} (f g : a ⟶ b), P (Boundary.vertical f g))
    {f g : Side C} (b : Boundary (fun _ _ : C => Empty) f g) : P b := by
  rcases f with ⟨a, b, f⟩
  rcases g with ⟨a', b', g⟩
  rcases b with ⟨input, output⟩
  cases input with
  | cons _ e => exact Empty.elim e
  | nil =>
    rcases output with ⟨output, _⟩
    cases output with
    | cons _ e => exact Empty.elim e
    | nil => exact hv f g

end Boundary
end Kernel.Augmented

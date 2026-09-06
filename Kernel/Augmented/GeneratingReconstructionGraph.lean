import Kernel.Augmented.GeneratingAssociativityLaw

/-! The reconstructed augmented algebra has exactly the original generating incidence graph.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory Opposite
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Kernel.Augmented.GeneratingMonadAlgebra
universe w
open Generating
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

def reconstructionEvaluation : A.A.freeObject ⟶ reconstructed A := evaluationOperations A

/-- The original generators embedded into their reconstructed incidence fibres. -/
def reconstructionUnit : A.A ⟶ BundledAlgebra.forget.obj (reconstructed A) :=
  Graph.restrictMap (reconstructionEvaluation A)

theorem reconstructionUnit_object (a : A.A.Object) : Graph.mapObject (reconstructionUnit A) a = a := rfl

theorem reconstructionUnit_vertical (e : A.A.Vertical) :
    Graph.mapVertical (reconstructionUnit A) e = A.A.verticalPack e := by
  change FinPath.mapEdge (evaluationBase A).vertical.toPrefunctor
    (FinPath.mapEdge (Paths.of A.A.Objects) (A.A.verticalPack e)) = _
  change (⟨_, _, evalPath A (A.A.verticalPack e).2.2.toPath⟩ : FinPath.Edge (Vertical A)) = _
  rw [evalPath_single]
  rfl

theorem reconstructionUnit_horizontal (j : A.A.Horizontal) :
    Graph.mapHorizontal (reconstructionUnit A) j = A.A.horizontalPack j := rfl

theorem reconstructionUnit_cell {n ε} (x : A.A.Cell n ε) :
    (Graph.mapCell (reconstructionUnit A) x).val = CellGraph.pack (G := cells A) (A.A.generator x) :=
  (Graph.restrictMap_generator (reconstructionEvaluation A) x).trans (evaluationCells_generator A x)

private theorem reconstructionUnit_cell_bijective (n : ℕ) (ε : Bool) :
    Function.Bijective (Graph.mapCell (reconstructionUnit A) (n := n) (ε := ε)) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    rw [reconstructionUnit_cell, reconstructionUnit_cell] at he
    have hraw := congrArg (fun x : (cells A).Total => x.2.val) he
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hraw).2)).2
  · rintro ⟨⟨⟨f, g, b⟩, ⟨⟨m, δ, x⟩, e⟩⟩, har⟩
    have ha : (m, δ.toNat) = (n, ε.toNat) :=
      (A.A.boundary_arity x).symm.trans ((congrArg (fun b => b.2.2.arity) e).trans har)
    have hm := congrArg Prod.fst ha
    have hd : δ = ε := by
      have h := congrArg Prod.snd ha
      cases δ <;> cases ε <;> simp_all
    cases hm; cases hd
    refine ⟨x, Subtype.ext ?_⟩
    exact (reconstructionUnit_cell A x).trans
      (pack_cell_generator A (⟨⟨n, ε, x⟩, e⟩ : (cells A).Cell b)).symm

theorem reconstructionUnit_bijective (s : Shape) :
    Function.Bijective ((reconstructionUnit A).app (op s)) := by
  cases s with
  | point => exact Function.bijective_id
  | vertical =>
    change Function.Bijective (Graph.mapVertical (reconstructionUnit A))
    constructor
    · intro e e' h
      rw [reconstructionUnit_vertical, reconstructionUnit_vertical] at h
      exact congrArg (fun x => x.2.2.val) h
    · rintro ⟨a, b, e⟩
      exact ⟨e.val, (reconstructionUnit_vertical A e.val).trans (A.A.verticalPack_fiber e).symm⟩
  | horizontal =>
    change Function.Bijective (Graph.mapHorizontal (reconstructionUnit A))
    constructor
    · intro e e' h
      rw [reconstructionUnit_horizontal, reconstructionUnit_horizontal] at h
      exact congrArg (fun x => x.2.2.val) h
    · rintro ⟨a, b, e⟩
      exact ⟨e.val, (reconstructionUnit_horizontal A e.val).trans (A.A.horizontalPack_fiber e).symm⟩
  | cell n ε => exact reconstructionUnit_cell_bijective A n ε

instance : IsIso (reconstructionUnit A) := by
  have : ∀ s, IsIso ((Graph.presheafFunctor.map (reconstructionUnit A)).app s) := fun s =>
    (isIso_iff_bijective _).mpr (reconstructionUnit_bijective A s.unop)
  have : IsIso (Graph.presheafFunctor.map (reconstructionUnit A)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso (reconstructionUnit A) Graph.presheafFunctor

def reconstructionGraphIso : A.A ≅ BundledAlgebra.forget.obj (reconstructed A) := asIso (reconstructionUnit A)

end Kernel.Augmented.GeneratingMonadAlgebra

import Kernel.Augmented.Rows
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! The ordinary-active-chain obstruction to augmented empty outputs.
Cites: D-KR-18, D-TL-21, AT-FD-7.
This endpoint condition describes ordinary active simplex maps only.
-/

open CategoryTheory Simplicial
namespace Kernel.Augmented.Simplex
universe u v h c

def IsActive {a b : SimplexCategory} (f : a ⟶ b) : Prop :=
  f.toOrderHom 0 = 0 ∧ f.toOrderHom (Fin.last a.len) = Fin.last b.len

theorem active_from_zero_target_zero {n : ℕ} (f : ⦋0⦌ ⟶ ⦋n⦌) (hf : IsActive f) :
    n = 0 := by
  have h : (0 : Fin (n + 1)) = Fin.last n := hf.1.symm.trans hf.2
  exact (congrArg Fin.val h).symm

theorem no_active_zero_to_one (f : ⦋0⦌ ⟶ ⦋1⦌) : ¬ IsActive f := by
  intro hf
  have := active_from_zero_target_zero f hf
  contradiction

/-- Nullary inputs do admit the opposite direction; the obstruction is asymmetric. -/
theorem active_to_zero {n : ℕ} (f : ⦋n⦌ ⟶ ⦋0⦌) : IsActive f :=
  ⟨@Subsingleton.elim (Fin 1) inferInstance _ _,
    @Subsingleton.elim (Fin 1) inferInstance _ _⟩

/-- Any incident row with positive input and no output obstructs this encoding. -/
theorem no_active_encoding {C : Type u} [Quiver.{v} C] {H : C → C → Type h}
    {G : CellGraph.{u,v,h,c} C H} {f g : Side C} (r : G.NonemptyRow f g)
    (hin : 0 < (CellGraph.Row.input r.val).length)
    (hout : (CellGraph.Row.output r.val).length = 0)
    (α : ⦋(CellGraph.Row.output r.val).length⦌ ⟶ ⦋(CellGraph.Row.input r.val).length⦌) :
    ¬ IsActive α := by
  generalize hn : (CellGraph.Row.input r.val).length = n at hin α
  generalize hm : (CellGraph.Row.output r.val).length = m at hout α
  cases hout
  intro hα
  have hz := active_from_zero_target_zero α hα
  omega

end Kernel.Augmented.Simplex

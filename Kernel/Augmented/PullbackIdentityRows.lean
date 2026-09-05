import Kernel.Augmented.PullbackOperations
import Kernel.Augmented.ComparisonTransport

/-! Internal comparison of identity rows under change of base.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h u' v' h' c

namespace Boundary
variable {C : Type u} [Quiver.{v} C] {H : C → C → Type h}

theorem heq_of_frame_eq {f g f' g' : Side C} {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) : HEq b b' := by
  have hf : f = f' := congrArg Sigma.fst e
  cases hf
  have ep : (⟨g, b⟩ : Σ g : Side C, Boundary H f g) = ⟨g', b'⟩ := eq_of_heq (Sigma.mk.inj e).2
  exact (Sigma.mk.inj ep).2

end Boundary
namespace BaseMap
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {H : C → C → Type h} {K : D → D → Type h'}
  (F : BaseMap H K) {G : CellGraph.{u',v',h',c} D K} (O : Operations G)

theorem pullback_shortIdentity {a b : C} (p : ShortPath H a b) :
    HEq ((F.pullbackOperations O).shortIdentity p) (O.shortIdentity (F.shortPath p)) := by
  apply ShortPath.cases_on (fun {_ _} p =>
    HEq ((F.pullbackOperations O).shortIdentity p) (O.shortIdentity (F.shortPath p)))
  · intro a
    change HEq (O.verticalIdentity (F.vertical.map (𝟙 a))) (O.verticalIdentity (𝟙 (F.vertical.obj a)))
    rw [F.vertical.map_id]
  · intro a b j
    exact CellGraph.transport_heq (F.horizontalIdentity_boundary j) (O.horizontalIdentity (F.horizontal j))

theorem pullback_horizontalIdentities {a b : C} (p : HPath H a b) :
    HEq (F.row ((F.pullbackOperations O).horizontalIdentities p)) (O.horizontalIdentities (F.path p)) := by
  induction p with
  | nil => exact CellGraph.Row.nil_heq (F.side_identity a)
  | @cons b d p j ih =>
    apply CellGraph.Row.cons_heq (F.side_identity a) (F.side_identity b) (F.side_identity d) ih
    · exact Boundary.heq_of_frame_eq (F.horizontalIdentity_boundary j).symm
    · exact CellGraph.transport_heq (F.horizontalIdentity_boundary j) (O.horizontalIdentity (F.horizontal j))

theorem pullback_identityRow {a b : C} (p : HPath H a b) :
    HEq (F.row ((F.pullbackOperations O).identityRow p).val) (O.identityRow (F.path p)).val := by
  cases p with
  | nil =>
    apply CellGraph.Row.cons_heq (F.side_identity a) (F.side_identity a) (F.side_identity a)
      (CellGraph.Row.nil_heq (F.side_identity a))
    · apply Boundary.heq_of_frame_eq
      apply Boundary.frame_eq (F.side_identity a) (F.side_identity a) (HEq.refl _) (HEq.refl _)
    · change HEq (O.verticalIdentity (F.vertical.map (𝟙 a))) (O.verticalIdentity (𝟙 (F.vertical.obj a)))
      rw [F.vertical.map_id]
  | cons p j => exact F.pullback_horizontalIdentities O (Quiver.Path.cons (V := Horizontal H) p j)

end BaseMap
end Kernel.Augmented

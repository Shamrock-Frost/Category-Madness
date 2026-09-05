import Kernel.Augmented.FreeGeneratingLift

/-! A map out of the free vertical category is determined by its generating graph map.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented
universe w
namespace BaseMap
variable {C D : Type w} [Category.{w} C] [Category.{w} D]
  {H : C → C → Type w} {K : D → D → Type w}

@[ext] theorem ext (F I : BaseMap H K) (hv : F.vertical = I.vertical)
    (hh : HEq (@F.horizontal) (@I.horizontal)) : F = I := by
  cases F; cases I; cases hv; cases eq_of_heq hh; rfl

end BaseMap
namespace Generating.Graph
variable {G : Graph.{w}} {A : BundledAlgebra.{w}}

abbrev restrictMap (M : G.freeObject ⟶ A) : G ⟶ BundledAlgebra.forget.obj A :=
  G.unit ≫ BundledAlgebra.forget.map M

private theorem restrict_vertical (M : G.freeObject ⟶ A) {a b : G.Objects} (e : a ⟶ b) :
    (skeleton (restrictMap M)).vertical.map e = M.base.vertical.map ((Paths.of G.Objects).map e) := by
  have h := (skeleton_vertical (restrictMap M) e).trans
    (congrArg (fun e => FinPath.mapEdge M.base.vertical.toPrefunctor
      (FinPath.mapEdge (Paths.of G.Objects) e)) (G.verticalPack_fiber e).symm)
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2

private theorem restrict_horizontal (M : G.freeObject ⟶ A) {a b : G.Objects} (e : G.horizontal a b) :
    (skeleton (restrictMap M)).horizontal e = M.base.horizontal e := by
  have h := (skeleton_horizontal (restrictMap M) e).trans
    (congrArg (FinPath.mapEdge M.base.horizontalPrefunctor) (G.horizontalPack_fiber e).symm)
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2

/-- Restriction to the generating graph recovers the entire vertical/horizontal base map. -/
theorem base_restrict (M : G.freeObject ⟶ A) : (skeleton (restrictMap M)).baseMap = M.base := by
  apply BaseMap.ext
  · apply (SkeletonAssignment.baseMap_unique (skeleton (restrictMap M)) M.base.vertical _).symm
    refine Prefunctor.ext ?_ ?_
    · intro a
      rfl
    intro a b e
    exact (restrict_vertical M e).symm
  · apply heq_of_eq
    funext a b e
    exact restrict_horizontal M e

end Generating.Graph
end Kernel.Augmented

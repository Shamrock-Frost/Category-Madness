import Kernel.Augmented.FreeGeneratingGraph
import Kernel.Augmented.PullbackLaws

/-! The global free construction's mapping property, allowing objects and edges to vary.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe w u v h c

namespace BaseMap
variable {C : Type w} [Category.{w} C] {H : C → C → Type w}
  {D : Type u} [Category.{v} D] {K : D → D → Type h}

theorem pullback_transport (B : BaseMap H K) {G : CellGraph.{u,v,h,c} D K}
    {f g f' g' : Side C} {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) (φ : (B.pullback G).Cell b) :
    CellGraph.transport (G := B.pullback G) e φ =
      CellGraph.transport (G := G) (congrArg B.frame e) φ := by
  exact eq_of_heq ((CellGraph.transport_heq (G := B.pullback G) e φ).trans
    (CellGraph.transport_heq (G := G) (congrArg B.frame e) φ).symm)

end BaseMap
namespace Generating.Graph
variable (G : Generating.Graph.{w}) {D : Type u} [Category.{v} D] (K : D → D → Type h)

/-- Assign objects and generating vertical/horizontal edges in a target base. -/
structure SkeletonAssignment where
  vertical : G.Objects ⥤q D
  horizontal : {a b : G.Objects} → G.horizontal a b → K (vertical.obj a) (vertical.obj b)

namespace SkeletonAssignment
variable {G K}

def baseMap (B : SkeletonAssignment G K) : BaseMap G.freeHorizontal K where
  vertical := Paths.lift B.vertical
  horizontal := B.horizontal

theorem baseMap_generator (B : SkeletonAssignment G K) {a b : G.Objects} (f : a ⟶ b) :
    B.baseMap.vertical.map ((Paths.of G.Objects).map f) = B.vertical.map f :=
  Paths.lift_toPath B.vertical f

/-- A vertical functor extending the generating edges is forced to be the path extension. -/
theorem baseMap_unique (B : SkeletonAssignment G K) (F : Paths G.Objects ⥤ D)
    (hF : Paths.of G.Objects ⋙q F.toPrefunctor = B.vertical) : F = B.baseMap.vertical :=
  Paths.lift_unique B.vertical F hF

end SkeletonAssignment
variable {K} (B : SkeletonAssignment G K) {Q : CellGraph.{u,v,h,c} D K}

abbrev CellAssignment := ∀ {n ε} (x : G.Cell n ε), Q.Cell (B.baseMap.boundary (G.freeBoundary x))

theorem freeGenerator_transport {n ε} (x : G.Cell n ε)
    {f g : Side (Paths G.Objects)} {b : Boundary G.freeHorizontal f g}
    (e : (G.freeBoundary x).frame = b.frame) :
    CellGraph.transport (G := G.freeCellGenerators) e ⟨⟨n, ε, x⟩, rfl⟩ = ⟨⟨n, ε, x⟩, e⟩ := by
  have aux : ∀ (b' : CellBoundary (Paths G.Objects) G.freeHorizontal) (h : (G.freeBoundary x).frame = b'),
      cast (congrArg G.freeCellGenerators.family h) (⟨⟨n, ε, x⟩, rfl⟩ : G.freeCellGenerators.family (G.freeBoundary x).frame) =
        (⟨⟨n, ε, x⟩, h⟩ : G.freeCellGenerators.family b') := by
    intro b' h
    cases h
    rfl
  exact aux b.frame e

def cellAssignmentEquiv : CellAssignment G B (Q := Q) ≃ CellGraph.Map G.freeCellGenerators (B.baseMap.pullback Q) where
  toFun a := ⟨fun {_ _} {b} φ =>
    CellGraph.transport (G := Q) (congrArg B.baseMap.frame φ.property) (a φ.val.2.2)⟩
  invFun F := fun {_ _} x => F.cell ⟨⟨_, _, x⟩, rfl⟩
  left_inv a := by
    funext n ε x
    rfl
  right_inv F := by
    apply CellGraph.Map.ext
    intro f g b φ
    rcases φ with ⟨⟨n, ε, x⟩, e⟩
    have E := F.transport e (⟨⟨n, ε, x⟩, rfl⟩ : G.freeCellGenerators.Cell (G.freeBoundary x))
    rw [freeGenerator_transport G x e, B.baseMap.pullback_transport] at E
    exact E.symm

/-- Generator assignments extend uniquely to operation-preserving maps over the induced base functor. -/
noncomputable def freeMapEquiv (A : Algebra Q) :
    CellAssignment G B (Q := Q) ≃ G.freeAlgebra.toOperations.Map (B.baseMap.pullbackAlgebra A).toOperations :=
  (cellAssignmentEquiv G B).trans (CellTerm.freeLiftEquiv G.freeCellGenerators (B.baseMap.pullbackAlgebra A))

end Generating.Graph
end Kernel.Augmented

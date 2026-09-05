import Kernel.Augmented.FreeGeneratingBase
import Kernel.Augmented.GlobalMapExt

/-! Uniqueness of global maps out of the free augmented algebra.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating.Graph
universe w
variable {G : Graph.{w}} {A : BundledAlgebra.{w}}

private theorem generator_pack {f g : Side (Paths G.Objects)} {b : Boundary G.freeHorizontal f g}
    (φ : G.freeCellGenerators.Cell b) :
    CellGraph.pack ((CellTerm.freeGenerators G.freeCellGenerators).cell φ) =
      CellGraph.pack (G.freeCell φ.val.2.2) := by
  rcases φ with ⟨⟨n, ε, x⟩, e⟩
  have h := (CellTerm.freeGenerators G.freeCellGenerators).transport e
    (⟨⟨n, ε, x⟩, rfl⟩ : G.freeCellGenerators.Cell (G.freeBoundary x))
  rw [freeGenerator_transport G x e] at h
  rw [h]
  exact CellGraph.pack_transport _ _

private theorem hom_ext_of_base (I J : G.freeObject ⟶ A) (hb : I.base = J.base)
    (hgen : ∀ {n ε} (x : G.Cell n ε),
      I.total (CellGraph.pack (G.freeCell x)) = J.total (CellGraph.pack (G.freeCell x))) : I = J := by
  let I' := I.changeBase J.base hb
  have e : I'.toPullback = J.toPullback := by
    apply (CellTerm.freeLiftEquiv G.freeCellGenerators (J.base.pullbackAlgebra A.algebra)).symm.injective
    apply CellGraph.Map.ext
    intro f g b φ
    change I'.toOverMap.cell ((CellTerm.freeGenerators G.freeCellGenerators).cell φ) =
      J.toOverMap.cell ((CellTerm.freeGenerators G.freeCellGenerators).cell φ)
    have ht : I'.total (CellGraph.pack ((CellTerm.freeGenerators G.freeCellGenerators).cell φ)) =
        J.total (CellGraph.pack ((CellTerm.freeGenerators G.freeCellGenerators).cell φ)) := by
      erw [generator_pack]
      exact hgen φ.val.2.2
    exact eq_of_heq (CellGraph.Total.cell_heq ((I'.toOverMap.pack_cell _).trans
      (ht.trans (J.toOverMap.pack_cell _).symm)))
  apply Operations.OverMap.ext
  apply CellGraph.OverMap.ext _ _ hb
  funext x
  calc
    I.total x = CellGraph.pack (I'.toOverMap.cell x.2) := (I'.toOverMap.pack_cell x.2).symm
    _ = CellGraph.pack (J.toOverMap.cell x.2) := congrArg (CellGraph.pack (G := A.cells))
      (congrArg (fun F => F.cell x.2) e)
    _ = J.total x := J.toOverMap.pack_cell x.2

theorem restrictMap_generator (M : G.freeObject ⟶ A) {n ε} (x : G.Cell n ε) :
    (mapCell (restrictMap M) x).val = M.total (CellGraph.pack (G.freeCell x)) :=
  M.toOverMap.arityCell_val (G.unitCell x)

/-- Global free-algebra maps are determined by their restriction to all generating sorts. -/
theorem hom_ext (I J : G.freeObject ⟶ A) (h : restrictMap I = restrictMap J) : I = J := by
  apply hom_ext_of_base I J
  · exact (base_restrict I).symm.trans
      ((congrArg (fun F => (skeleton F).baseMap) h).trans (base_restrict J))
  · intro n ε x
    exact (restrictMap_generator I x).symm.trans
      ((congrArg (fun F : G ⟶ BundledAlgebra.forget.obj A => (mapCell F x).val) h).trans
        (restrictMap_generator J x))

theorem lift_restrictMap (M : G.freeObject ⟶ A) : lift (restrictMap M) = M :=
  hom_ext _ _ (unit_lift (restrictMap M))

end Kernel.Augmented.Generating.Graph

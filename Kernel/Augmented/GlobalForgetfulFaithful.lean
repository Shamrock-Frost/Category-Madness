import Kernel.Augmented.FreeGeneratingAdjunction

/-! The generating forgetful functor retains every global algebra map.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented
universe w

namespace BaseMap
variable {C D : Type w} [Category.{w} C] [Category.{w} D]
  {H : C → C → Type w} {K : D → D → Type w}

theorem ext_edges (F I : BaseMap H K)
    (ho : F.vertical.obj = I.vertical.obj)
    (hv : Generating.FinPath.mapEdge F.vertical.toPrefunctor =
      Generating.FinPath.mapEdge I.vertical.toPrefunctor)
    (hh : Generating.FinPath.mapEdge F.horizontalPrefunctor =
      Generating.FinPath.mapEdge I.horizontalPrefunctor) : F = I := by
  rcases F with ⟨⟨fo, fm, fi, fc⟩, fh⟩
  rcases I with ⟨⟨io, im, ii, ic⟩, ih⟩
  change fo = io at ho
  cases ho
  have hm : @fm = @im := by
    funext a b f
    have he := congrFun hv ⟨a, b, f⟩
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  cases hm
  have hj : @fh = @ih := by
    funext a b j
    have he := congrFun hh ⟨a, b, j⟩
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  cases hj
  rfl

end BaseMap

namespace CellGraph.Total
variable {C : Type w} [Category.{w} C] {H : C → C → Type w}
  {G : CellGraph.{w,w,w,w} C H}

def outputFlag (x : G.Total) : Bool := decide (x.1.2.2.output.val.length = 1)

theorem outputFlag_length (x : G.Total) : x.1.2.2.output.val.length = x.outputFlag.toNat := by
  have h := x.1.2.2.output.property
  unfold outputFlag
  by_cases h1 : x.1.2.2.output.val.length = 1
  · simp [h1]
  · have h0 : x.1.2.2.output.val.length = 0 := by omega
    simp [h0]

/-- Every cell belongs to its generating arity sort, including empty-output cells. -/
def arityCell (x : G.Total) : G.ArityCell x.1.2.2.input.length x.outputFlag :=
  ⟨x, Prod.ext rfl x.outputFlag_length⟩

end CellGraph.Total

namespace BundledAlgebra

instance : forget.{w}.Faithful where
  map_injective := by
    intro A B F I h
    apply Operations.OverMap.ext
    apply CellGraph.OverMap.ext
    · apply BaseMap.ext_edges
      · exact congrArg (fun f : forget.obj A ⟶ forget.obj B => Generating.Graph.mapObject f) h
      · exact congrArg (fun f : forget.obj A ⟶ forget.obj B => Generating.Graph.mapVertical f) h
      · exact congrArg (fun f : forget.obj A ⟶ forget.obj B => Generating.Graph.mapHorizontal f) h
    · funext x
      have he := congrArg (fun f : forget.obj A ⟶ forget.obj B =>
        (Generating.Graph.mapCell f x.arityCell).val) h
      exact (F.toOverMap.arityCell_val x.arityCell).symm.trans
        (he.trans (I.toOverMap.arityCell_val x.arityCell))

/-- The concrete comparison into algebras for the generating monad. -/
def generatingComparison : BundledAlgebra.{w} ⥤ generatingMonad.Algebra :=
  Monad.comparison freeForgetAdjunction

instance : generatingComparison.{w}.Faithful :=
  inferInstanceAs (Monad.comparison freeForgetAdjunction).Faithful

end BundledAlgebra
end Kernel.Augmented

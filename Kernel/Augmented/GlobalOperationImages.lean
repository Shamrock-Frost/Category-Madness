import Kernel.Augmented.GlobalMapToPullback
import Kernel.Augmented.SubstitutionCongruence
import Kernel.Augmented.PullbackRows

/-! Operation images with explicitly identified incident target data.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe w
variable {C D : Type w} [Category.{w} C] [Category.{w} D]
  {H : C → C → Type w} {K : D → D → Type w}
  {G : CellGraph.{w,w,w,w} C H} {Q : CellGraph.{w,w,w,w} D K}

namespace CellGraph.OverMap

theorem single_image (F : G.OverMap Q) {f g : Side C} {f' g' : Side D}
    {b : Boundary H f g} {b' : Boundary K f' g'} (φ : G.Cell b) (ψ : Q.Cell b')
    (hf : F.base.side f = f') (hg : F.base.side g = g')
    (hφ : F.total (CellGraph.pack φ) = CellGraph.pack ψ) :
    HEq (F.row (CellGraph.Row.single φ).val) (CellGraph.Row.single ψ).val := by
  apply CellGraph.Row.cons_heq hf hf hg (CellGraph.Row.nil_heq hf)
  · exact Boundary.heq_of_frame_eq ((F.boundary (CellGraph.pack φ)).symm.trans (congrArg Sigma.fst hφ))
  · exact CellGraph.Total.cell_heq ((F.pack_cell φ).trans hφ)

theorem row_comp (F : G.OverMap Q) {f g k : Side C} (p : G.Row f g) (q : G.Row g k) :
    F.row (p.comp q) = (F.row p).comp (F.row q) := by
  induction q with
  | nil => rfl
  | cons q e ih => exact congrArg (fun r => r.cons ⟨F.base.boundary e.1, F.cell e.2⟩) ih

end CellGraph.OverMap
namespace Operations.OverMap
variable {O : Operations G} {O' : Operations Q}

theorem substitute_image (F : O.OverMap O') {f g : Side C} {f' g' : Side D}
    (r : G.NonemptyRow f g) (r' : Q.NonemptyRow f' g')
    (hf : F.base.side f = f') (hg : F.base.side g = g') (hr : HEq (F.toOverMap.row r.val) r'.val)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b)
    (h' : f'.target ⟶ F.base.vertical.obj a) (k' : g'.target ⟶ F.base.vertical.obj b)
    (hh : HEq (F.base.vertical.map h) h') (hk : HEq (F.base.vertical.map k) k')
    (L : ShortPath H a b) (L' : ShortPath K (F.base.vertical.obj a) (F.base.vertical.obj b))
    (hL : F.base.shortPath L = L')
    (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L))
    (ψ' : Q.Cell (CellGraph.Row.outerBoundary r' h' k' L'))
    (hψ : F.total (CellGraph.pack ψ) = CellGraph.pack ψ') :
    F.total (CellGraph.pack (O.substitute r h k L ψ)) = CellGraph.pack (O'.substitute r' h' k' L' ψ') := by
  apply (F.substitute r h k L ψ).trans
  apply Operations.pack_substitute_heq O' hf hg hr rfl rfl hh hk (heq_of_eq hL)
  exact CellGraph.Total.cell_heq ((F.toOverMap.pack_outerCell r h k L ψ).trans hψ)

theorem identityRow (F : O.OverMap O') {a b : C} (p : HPath H a b) :
    HEq (F.toOverMap.row (O.identityRow p).val) (O'.identityRow (F.base.path p)).val := by
  have e := congrArg (fun r => F.base.row r.val) (F.toPullback.identityRow p)
  have h : F.base.row (F.toOverMap.toFamily.row (O.identityRow p).val) =
      F.base.row ((F.base.pullbackOperations O').identityRow p).val := e
  rw [F.toOverMap.toFamily_row] at h
  exact (heq_of_eq h).trans (F.base.pullback_identityRow O' p)

theorem insertedRow (F : O.OverMap O') {f g k : Side C} (p : G.Row f g) (q : G.Row g k) :
    F.toOverMap.row (O.insertedRow p q).val = (O'.insertedRow (F.toOverMap.row p) (F.toOverMap.row q)).val := by
  have h := congrArg (fun r => F.base.row r.val) (F.toPullback.insertedRow p q)
  change F.base.row (F.toOverMap.toFamily.row (O.insertedRow p q).val) =
    F.base.row ((F.base.pullbackOperations O').insertedRow
      (F.toOverMap.toFamily.row p) (F.toOverMap.toFamily.row q)).val at h
  rw [F.toOverMap.toFamily_row, F.base.pullback_insertedRow,
    F.toOverMap.toFamily_row, F.toOverMap.toFamily_row] at h
  exact h

end Operations.OverMap

namespace Operations

theorem insertedRow_heq (O : Operations G) {f g k f' g' k' : Side C}
    {p : G.Row f g} {q : G.Row g k} {p' : G.Row f' g'} {q' : G.Row g' k'}
    (hf : f = f') (hg : g = g') (hk : k = k') (hp : HEq p p') (hq : HEq q q') :
    HEq (O.insertedRow p q).val (O.insertedRow p' q').val := by
  cases hf; cases hg; cases hk; cases eq_of_heq hp; cases eq_of_heq hq; rfl

end Operations
end Kernel.Augmented

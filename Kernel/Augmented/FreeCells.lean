import Kernel.Augmented.CellQuotient
import Kernel.Augmented.CellMapSections

/-! The free augmented cell algebra over a fixed vertical category and horizontal graph.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellTerm
universe u v h c
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  (G : CellGraph.{u,v,h,c} C H)

noncomputable def quotientSection : CellGraph.Map (quotientGraph G) (graph G) := ⟨Quotient.out⟩

theorem quotient_section {f g : Side C} {b : Boundary H f g} (φ : (quotientGraph G).Cell b) :
    (quotientMap G).cell ((quotientSection G).cell φ) = φ := Quotient.out_eq φ

theorem quotient_laws : Laws (quotientOperations G) := by
  let F := quotientOperationMap G
  let S := quotientSection G
  have hs : ∀ {f g : Side C} {b : Boundary H f g} (φ : (quotientGraph G).Cell b),
      F.cell (S.cell φ) = φ := quotient_section G
  constructor
  · intro a b d f g
    have E : F.cell ((operations G).verticalStack ((operations G).verticalIdentity f)
        ((operations G).verticalIdentity g)) = F.cell ((operations G).verticalIdentity (f ≫ g)) :=
      Quotient.sound (Related.verticalIdentity_stack f g)
    erw [F.verticalStack, F.verticalIdentity, F.verticalIdentity, F.verticalIdentity] at E
    exact E
  · intro f g b φ
    have E := F.leftUnitEquation (S.cell φ)
    have Q : F.cell (CellGraph.transport (Operations.leftUnit_boundary (S.cell φ))
        ((operations G).leftUnitComposite (S.cell φ))) = F.cell (S.cell φ) :=
      Quotient.sound (Related.leftUnit (S.cell φ))
    rw [E, hs] at Q
    exact Q
  · intro f g b φ
    have E := F.rightUnitEquation (S.cell φ)
    have Q : F.cell (CellGraph.transport ((operations G).rightUnit_boundary b)
        ((operations G).rightUnitComposite (S.cell φ))) = F.cell (S.cell φ) :=
      Quotient.sound (Related.rightUnit (S.cell φ))
    rw [E, hs] at Q
    exact Q
  · intro f g k p q hn a b h l L ψ
    let p0 := S.row p
    let q0 := S.row q
    have hn0 : 0 < (p0.comp q0).length := by
      erw [Quiver.Path.length_comp, S.row_length, S.row_length]
      exact lt_of_lt_of_eq hn (Quiver.Path.length_comp (V := (quotientGraph G).Vertex) p q)
    let p' := F.toMap.row p0
    let q' := F.toMap.row q0
    have hn' : 0 < (p'.comp q').length := by
      rw [← F.toMap.row_comp, F.toMap.row_length]
      exact hn0
    have eo : CellGraph.Row.output (p'.comp q') = CellGraph.Row.output (p0.comp q0) := by
      rw [← F.toMap.row_comp, F.toMap.row_output]
    have E : ∀ (hn' : 0 < (p'.comp q').length) (ψ' : (quotientGraph G).Cell (CellGraph.Row.outerBoundary ⟨p'.comp q', hn'⟩ h l L)),
        CellGraph.transport ((quotientOperations G).inserted_boundary p' q' hn' h l L)
          ((quotientOperations G).insertedComposite p' q' hn' h l L ψ') =
            (quotientOperations G).substitute ⟨p'.comp q', hn'⟩ h l L ψ' := by
      intro hn' ψ'
      let ψ0 := S.cell (CellGraph.castInput (G := quotientGraph G) (f := ⟨f.target, a, h⟩)
        (g := ⟨k.target, b, l⟩) (L := L) eo ψ')
      have Q := (F.insertion_iff p0 q0 hn0 h l L ψ0).mp
        (Quotient.sound (Related.insertion p0 q0 hn0 h l L ψ0))
      change CellGraph.transport _ ((quotientOperations G).insertedComposite p' q' hn' h l L
        (CellGraph.castInput eo.symm (F.cell ψ0))) =
        (quotientOperations G).substitute ⟨p'.comp q', hn'⟩ h l L
          (CellGraph.castInput eo.symm (F.cell ψ0)) at Q
      dsimp only [ψ0] at Q
      erw [hs, CellGraph.castInput_trans] at Q
      exact Q
    let P (p : (quotientGraph G).Row f g) (q : (quotientGraph G).Row g k) : Prop :=
      ∀ (hn : 0 < (p.comp q).length)
        (ψ : (quotientGraph G).Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)),
        CellGraph.transport ((quotientOperations G).inserted_boundary p q hn h l L)
          ((quotientOperations G).insertedComposite p q hn h l L ψ) =
            (quotientOperations G).substitute ⟨p.comp q, hn⟩ h l L ψ
    have eP : P p' q' = P p q := congrArg₂ P (F.toMap.row_section S hs p) (F.toMap.row_section S hs q)
    exact (Eq.mp eP E) hn ψ
  · intro s t r a b p q L χ
    let r0 := S.nestedNonemptyRow r
    let r' := F.toMap.nestedNonemptyRow r0
    have eo : CellGraph.Row.output r'.outer.val = CellGraph.Row.output r0.outer.val :=
      (congrArg CellGraph.Row.output (F.toMap.nestedRow_outer r0.val)).symm.trans
        (F.toMap.row_output r0.outer.val)
    have E : ∀ χ' : (quotientGraph G).Cell (CellGraph.Row.outerBoundary r'.outer p q L),
        CellGraph.transport ((quotientOperations G).assoc_boundary r' p q L)
          ((quotientOperations G).assocLeft r' p q L χ') =
            (quotientOperations G).assocRight r' p q L χ' := by
      intro χ'
      let χ0 := S.cell (CellGraph.castInput (G := quotientGraph G) (f := ⟨s.bottom, a, p⟩)
        (g := ⟨t.bottom, b, q⟩) (L := L) eo χ')
      have Q := (F.assoc_iff r0 p q L χ0).mp
        (Quotient.sound (Related.assoc r0 p q L χ0))
      change CellGraph.transport _ ((quotientOperations G).assocLeft r' p q L
        (CellGraph.castInput eo.symm (F.cell χ0))) =
        (quotientOperations G).assocRight r' p q L (CellGraph.castInput eo.symm (F.cell χ0)) at Q
      dsimp only [χ0] at Q
      erw [hs, CellGraph.castInput_trans] at Q
      exact Q
    let P (r : Nested.NonemptyRow (quotientGraph G) s t) : Prop :=
      ∀ χ : (quotientGraph G).Cell (CellGraph.Row.outerBoundary r.outer p q L),
        CellGraph.transport ((quotientOperations G).assoc_boundary r p q L)
          ((quotientOperations G).assocLeft r p q L χ) = (quotientOperations G).assocRight r p q L χ
    have eP : P r' = P r := congrArg P (F.toMap.nestedNonemptyRow_section S hs r)
    exact (Eq.mp eP E) χ

noncomputable def freeAlgebra : Algebra (quotientGraph G) where
  toOperations := quotientOperations G
  laws := quotient_laws G

end Kernel.Augmented.CellTerm

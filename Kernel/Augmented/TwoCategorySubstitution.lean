import Kernel.Augmented.TwoCategoryComparison

/-! The reconstruction comparison preserves arbitrary incident substitutions.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.NoHorizontal
universe u v c
variable {C : Type u} [Category.{v} C]
  {G : CellGraph.{u,v,0,c} C (fun _ _ : C => Empty)} (A : Algebra G)

@[simp] theorem toOriginal_embed {a b : C} {f g : a ⟶ b}
    (p : Vertical.Row (G := G) f g) :
    (toOriginal A).row (Vertical.Row.embed (G := reconstructedGraph A) p) = p.embed := by
  induction p with
  | nil => rfl
  | cons p φ ih =>
    change ((toOriginal A).row (Vertical.Row.embed (G := reconstructedGraph A) p)).cons _ =
      (Vertical.Row.embed (G := G) p).cons _
    rw [ih]
    rfl

/-- Reconstruction preserves the whole substitution API with its explicit input transport. -/
theorem substitute_roundtrip {f g : Side C} (r : (reconstructedGraph A).NonemptyRow f g)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b)
    (L : ShortPath (fun _ _ : C => Empty) a b)
    (ψ : (reconstructedGraph A).Cell (CellGraph.Row.outerBoundary r h k L)) :
    (toOriginal A).cell ((reconstructedAlgebra A).substitute r h k L ψ) =
      CellGraph.castInput (G := G) (f := f.post h) (g := g.post k) (L := L)
        ((toOriginal A).row_input r.val)
        (A.substitute ((toOriginal A).nonemptyRow r) h k L
          (CellGraph.castInput ((toOriginal A).row_output r.val).symm ((toOriginal A).cell ψ))) := by
  rcases r with ⟨r, hn⟩
  rcases rowView r with ⟨x, y, f', g', p, hf, hg, he⟩
  cases hf; cases hg
  have er : r = p.embed := eq_of_heq he
  subst r
  rcases L with ⟨L, hL⟩
  cases L with
  | cons _ edge => exact Empty.elim edge
  | nil =>
    let F := toOriginal A
    let B := reconstructedAlgebra A
    have hp : 0 < p.length := by simpa only [Vertical.Row.embed_length] using hn
    let β : G.Cell (Boundary.vertical h k) := CellGraph.castInput (G := reconstructedGraph A)
      (f := ⟨y, a, h⟩) (g := ⟨y, a, k⟩) (L := ShortPath.empty a)
      (Vertical.Row.embed_output p) ψ
    have eβ : HEq (F.cell ψ) β :=
      (CellGraph.castInput_heq (Vertical.Row.embed_output p) (F.cell ψ)).symm.trans
        (heq_of_eq (F.castInput (Vertical.Row.embed_output p) ψ).symm)
    have em := congrArg
      (fun φ : (reconstructedGraph A).Cell (Boundary.vertical (f' ≫ h) (g' ≫ k)) => F.cell φ)
      (Vertical.substitute_cast B.toOperations p hp h k ψ)
    have ec := F.castInput (f := ⟨x, a, f' ≫ h⟩) (g := ⟨x, a, g' ≫ k⟩)
      (L := ShortPath.empty a) (Vertical.Row.embed_input p)
      (B.substitute (Vertical.Row.nonempty p hp) h k (ShortPath.empty a) ψ)
    have el : HEq (F.cell (B.substitute (Vertical.Row.nonempty p hp) h k (ShortPath.empty a) ψ))
        (Vertical.substitute B.toOperations (h := h) (k := k) p hp β) :=
      (CellGraph.castInput_heq (G := G) (f := ⟨x, a, f' ≫ h⟩) (g := ⟨x, a, g' ≫ k⟩)
        (L := ShortPath.empty a) (Vertical.Row.embed_input p)
        (F.cell (B.substitute (Vertical.Row.nonempty p hp) h k (ShortPath.empty a) ψ))).symm.trans
        (heq_of_eq (ec.symm.trans em))
    have ea := A.toOperations.substitute_heq
      (r := F.nonemptyRow (Vertical.Row.nonempty p hp))
      (r' := Vertical.Row.nonempty (G := G) p hp)
      rfl rfl (heq_of_eq (toOriginal_embed A p)) (HEq.refl h) (HEq.refl k) rfl
      ((CellGraph.castInput_heq (F.row_output p.embed).symm (F.cell ψ)).trans
        (eβ.trans (CellGraph.castInput_heq
          (Vertical.Row.embed_output (G := G) p).symm β).symm))
    apply eq_of_heq
    apply el.trans
    apply (heq_of_eq (reconstructed_substitute A p hp β)).trans
    exact ((CellGraph.castInput_heq _ _).trans
      (ea.trans (Vertical.substitute_heq_raw A.toOperations p hp β).symm)).symm

end Kernel.Augmented.NoHorizontal

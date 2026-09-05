import Kernel.Augmented.PathPositions

/-! Ordered path positions recover the entire path and its finite-edge presentation.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
namespace Kernel.Augmented.Generating.FinPath
universe w
variable {C : Type w} [Quiver.{w} C]

theorem vertexAt_ofEdges (n : ℕ) (o : Fin (n + 1) → C)
    (e : (i : Fin n) → (o i.castSucc ⟶ o i.succ)) (i : Fin (n + 1)) :
    vertexAt (ofEdges n o e) i.val (by rw [length_ofEdges]; omega) = o i := by
  induction n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [ofEdges, vertexAt, Fin.val_last]
      have hn : ¬n + 1 ≤ (ofEdges n (fun i => o i.castSucc) (fun i => e i.castSucc)).length := by
        rw [length_ofEdges]
        omega
      erw [dif_neg hn]
    · simp only [ofEdges, vertexAt, Fin.val_castSucc]
      have hi : i.val ≤ (ofEdges n (fun i => o i.castSucc) (fun i => e i.castSucc)).length := by
        rw [length_ofEdges]
        omega
      erw [dif_pos hi]
      exact ih _ _ i

theorem edgeAt_ofEdges (n : ℕ) (o : Fin (n + 1) → C)
    (e : (i : Fin n) → (o i.castSucc ⟶ o i.succ)) (i : Fin n) :
    edgeAt (ofEdges n o e) i.val (by rw [length_ofEdges]; exact i.isLt) =
      ⟨o i.castSucc, o i.succ, e i⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [ofEdges, edgeAt, Fin.val_last]
      have hn : ¬n < (ofEdges n (fun i => o i.castSucc) (fun i => e i.castSucc)).length := by
        rw [length_ofEdges]
        omega
      erw [dif_neg hn]
      rfl
    · simp only [ofEdges, edgeAt, Fin.val_castSucc]
      have hi : i.val < (ofEdges n (fun i => o i.castSucc) (fun i => e i.castSucc)).length := by
        rw [length_ofEdges]
        exact i.isLt
      erw [dif_pos hi]
      exact ih _ _ i

/-- Equal ordered edge occurrences determine a path with fixed endpoints. -/
theorem path_ext {a b : C} (p q : Quiver.Path a b) (hlen : p.length = q.length)
    (hedge : ∀ (i : ℕ) (hi : i < p.length),
      edgeAt p i hi = edgeAt q i (by rw [← hlen]; exact hi)) : p = q := by
  induction p with
  | nil => exact (Quiver.Path.eq_nil_of_length_zero q hlen.symm).symm
  | @cons b d p e ih =>
    cases q with
    | nil => simp only [Quiver.Path.length] at hlen; omega
    | @cons b' d q f =>
      have hpq : p.length = q.length := Nat.succ.inj hlen
      have he := hedge p.length (Nat.lt_succ_self _)
      have hq : ¬p.length < q.length := by omega
      simp only [edgeAt, dif_neg (Nat.lt_irrefl _), dif_neg hq] at he
      obtain ⟨hb, hf⟩ := Sigma.mk.inj he
      cases hb
      have hef : e = f := eq_of_heq (Sigma.mk.inj (eq_of_heq hf)).2
      subst f
      have epq : p = q := ih q hpq (by
        intro i hi
        have hh := hedge i (Nat.lt_succ_of_lt hi)
        have hiq : i < q.length := by omega
        simpa only [edgeAt, dif_pos hi, dif_pos hiq] using hh)
      subst q
      rfl

theorem path_heq {a b a' b' : C} (p : Quiver.Path a b) (q : Quiver.Path a' b')
    (ha : a = a') (hb : b = b') (hlen : p.length = q.length)
    (hedge : ∀ (i : ℕ) (hi : i < p.length),
      edgeAt p i hi = edgeAt q i (by rw [← hlen]; exact hi)) : HEq p q := by
  cases ha; cases hb
  exact heq_of_eq (path_ext p q hlen hedge)

end Kernel.Augmented.Generating.FinPath

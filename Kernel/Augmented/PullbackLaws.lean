import Kernel.Augmented.PullbackRows

/-! Algebra laws under change of vertical and horizontal base.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.BaseMap
universe u v h u' v' h' c
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {H : C → C → Type h} {K : D → D → Type h'}
  (F : BaseMap H K) {G : CellGraph.{u',v',h',c} D K}

private theorem substitute_image (O : Operations G) {f g : Side C} {f' g' : Side D}
    (r : (F.pullback G).NonemptyRow f g) (r' : G.NonemptyRow f' g')
    (hf : F.side f = f') (hg : F.side g = g') (er : HEq (F.row r.val) r'.val)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b)
    (h' : f'.target ⟶ F.vertical.obj a) (k' : g'.target ⟶ F.vertical.obj b)
    (hh : HEq (F.vertical.map h) h') (hk : HEq (F.vertical.map k) k')
    (L : ShortPath H a b) (L' : ShortPath K (F.vertical.obj a) (F.vertical.obj b)) (hL : F.shortPath L = L')
    (ψ : (F.pullback G).Cell (CellGraph.Row.outerBoundary r h k L))
    (ψ' : G.Cell (CellGraph.Row.outerBoundary r' h' k' L')) (hψ : HEq ψ ψ') :
    HEq ((F.pullbackOperations O).substitute r h k L ψ) (O.substitute r' h' k' L' ψ') := by
  apply (CellGraph.transport_heq (G := G) (F.substitute_boundary r h k L) _).trans
  exact O.substitute_heq hf hg er hh hk hL ((CellGraph.castInput_heq _ _).trans hψ)

private theorem nestedRow_composite (O : Operations G) {s t : Nested.Side C}
    (r : Nested.Row (F.pullback G) s t) :
    HEq (F.row (Nested.Row.composite (F.pullbackOperations O) r))
      (Nested.Row.composite O (F.nestedRow r)) := by
  induction r with
  | nil => exact CellGraph.Row.nil_heq (F.side_post s.upper s.lower)
  | @cons t z r e ih =>
    apply CellGraph.Row.cons_heq (F.side_post s.upper s.lower) (F.side_post t.upper t.lower)
      (F.side_post z.upper z.lower) ih
    · exact Boundary.heq_of_frame_eq (F.substitute_boundary e.inner t.lower z.lower e.output).symm
    · exact F.substitute_image O e.inner (F.nonemptyRow e.inner) rfl rfl (HEq.refl _)
        t.lower z.lower (F.vertical.map t.lower) (F.vertical.map z.lower) (HEq.refl _) (HEq.refl _)
        e.output (F.shortPath e.output) rfl e.outer
        (CellGraph.castInput (F.row_output e.inner.val).symm e.outer)
        (CellGraph.castInput_heq (G := G) (f := F.side t.middle) (g := F.side z.middle)
          (L := F.shortPath e.output) (F.row_output e.inner.val).symm e.outer).symm

theorem pullback_leftUnit (A : Algebra G) {f g : Side C} {b : Boundary H f g} (φ : (F.pullback G).Cell b) :
    CellGraph.transport (Operations.leftUnit_boundary φ) ((F.pullbackOperations A.toOperations).leftUnitComposite φ) = φ := by
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  apply (F.substitute_image A.toOperations (CellGraph.Row.single φ) (CellGraph.Row.single (G := G) φ)
    rfl rfl (HEq.refl _) (𝟙 f.target) (𝟙 g.target) (𝟙 _) (𝟙 _)
    (heq_of_eq (F.vertical.map_id _)) (heq_of_eq (F.vertical.map_id _)) b.output (F.shortPath b.output) rfl _
    (CellGraph.castInput (CellGraph.Row.output_single (G := G) φ).symm
      (A.shortIdentity (F.shortPath b.output))) ?_).trans
  · exact A.laws.leftUnit_heq φ
  · exact (CellGraph.castInput_heq _ _).trans
      ((F.pullback_shortIdentity A.toOperations b.output).trans (CellGraph.castInput_heq _ _).symm)

theorem pullback_rightUnit (A : Algebra G) {f g : Side C} {b : Boundary H f g} (φ : (F.pullback G).Cell b) :
    CellGraph.transport ((F.pullbackOperations A.toOperations).rightUnit_boundary b)
      ((F.pullbackOperations A.toOperations).rightUnitComposite φ) = φ := by
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  apply (F.substitute_image A.toOperations
    ((F.pullbackOperations A.toOperations).identityRow b.input) (A.identityRow (F.path b.input))
    (F.side_identity f.source) (F.side_identity g.source) (F.pullback_identityRow A.toOperations b.input)
    f.arrow g.arrow (F.vertical.map f.arrow) (F.vertical.map g.arrow) (HEq.refl _) (HEq.refl _)
    b.output (F.shortPath b.output) rfl _
    (CellGraph.castInput (A.identityRow_output (F.path b.input)).symm φ) ?_).trans
  · exact A.laws.rightUnit_heq φ
  · exact (CellGraph.castInput_heq _ _).trans
      (CellGraph.castInput_heq (G := G) (f := F.side f) (g := F.side g)
        (L := F.shortPath b.output) (A.identityRow_output (F.path b.input)).symm φ).symm

theorem pullback_verticalIdentity_stack (A : Algebra G) {a b d : C} (f : a ⟶ b) (g : b ⟶ d) :
    (F.pullbackOperations A.toOperations).verticalStack
      ((F.pullbackOperations A.toOperations).verticalIdentity f)
      ((F.pullbackOperations A.toOperations).verticalIdentity g) =
        (F.pullbackOperations A.toOperations).verticalIdentity (f ≫ g) := by
  apply eq_of_heq
  apply (F.substitute_image A.toOperations
    (CellGraph.Row.single ((F.pullbackOperations A.toOperations).verticalIdentity f))
    (CellGraph.Row.single (G := G) (A.verticalIdentity (F.vertical.map f)))
    rfl rfl (HEq.refl _) g g (F.vertical.map g) (F.vertical.map g) (HEq.refl _) (HEq.refl _)
    (ShortPath.empty d) (ShortPath.empty (F.vertical.obj d)) rfl
    ((F.pullbackOperations A.toOperations).verticalIdentity g) (A.verticalIdentity (F.vertical.map g)) (HEq.refl _)).trans
  apply (heq_of_eq (A.laws.verticalIdentity_stack (F.vertical.map f) (F.vertical.map g))).trans
  change HEq (A.verticalIdentity (F.vertical.map f ≫ F.vertical.map g)) (A.verticalIdentity (F.vertical.map (f ≫ g)))
  rw [F.vertical.map_comp]


theorem pullback_insertion (A : Algebra G) {f g k : Side C}
    (p : (F.pullback G).Row f g) (q : (F.pullback G).Row g k) (hn : 0 < (p.comp q).length)
    {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b) (L : ShortPath H a b)
    (ψ : (F.pullback G).Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    CellGraph.transport ((F.pullbackOperations A.toOperations).inserted_boundary p q hn h l L)
      ((F.pullbackOperations A.toOperations).insertedComposite p q hn h l L ψ) =
        (F.pullbackOperations A.toOperations).substitute ⟨p.comp q, hn⟩ h l L ψ := by
  let p' := F.row p
  let q' := F.row q
  have hn' : 0 < (p'.comp q').length := by rw [← F.row_comp, F.row_length]; exact hn
  have eo : CellGraph.Row.output (p'.comp q') = F.path (CellGraph.Row.output (p.comp q)) := by
    rw [← F.row_comp, F.row_output]
  let ψ' : G.Cell (CellGraph.Row.outerBoundary ⟨p'.comp q', hn'⟩ (F.vertical.map h) (F.vertical.map l) (F.shortPath L)) :=
    CellGraph.castInput eo.symm ψ
  have E := F.substitute_image A.toOperations ⟨p.comp q, hn⟩ ⟨p'.comp q', hn'⟩
    rfl rfl (heq_of_eq (F.row_comp p q)) h l (F.vertical.map h) (F.vertical.map l) (HEq.refl _) (HEq.refl _)
    L (F.shortPath L) rfl ψ ψ' (CellGraph.castInput_heq (G := G)
      (f := F.side ⟨f.target, a, h⟩) (g := F.side ⟨k.target, b, l⟩) (L := F.shortPath L) eo.symm ψ).symm
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  apply (F.substitute_image A.toOperations ((F.pullbackOperations A.toOperations).insertedRow p q)
    (A.insertedRow p' q') rfl rfl (heq_of_eq (F.pullback_insertedRow A.toOperations p q))
    h l (F.vertical.map h) (F.vertical.map l) (HEq.refl _) (HEq.refl _) L (F.shortPath L) rfl _
    (CellGraph.castInput (A.insertedRow_output p' q').symm ψ') ?_).trans
  · exact (A.laws.insertion_heq p' q' hn' (F.vertical.map h) (F.vertical.map l) (F.shortPath L) ψ').trans E.symm
  · exact (CellGraph.castInput_heq _ _).trans
      ((CellGraph.castInput_heq (G := G) (f := F.side ⟨f.target, a, h⟩) (g := F.side ⟨k.target, b, l⟩)
        (L := F.shortPath L) (A.insertedRow_output p' q').symm ψ').trans
        (CellGraph.castInput_heq (G := G) (f := F.side ⟨f.target, a, h⟩) (g := F.side ⟨k.target, b, l⟩)
          (L := F.shortPath L) eo.symm ψ)).symm

theorem pullback_assoc (A : Algebra G) {s t : Nested.Side C}
    (r : Nested.NonemptyRow (F.pullback G) s t) {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b)
    (L : ShortPath H a b) (χ : (F.pullback G).Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    CellGraph.transport ((F.pullbackOperations A.toOperations).assoc_boundary r p q L)
      ((F.pullbackOperations A.toOperations).assocLeft r p q L χ) =
        (F.pullbackOperations A.toOperations).assocRight r p q L χ := by
  let r' := F.nestedNonemptyRow r
  have eo : CellGraph.Row.output r'.outer.val = F.path (CellGraph.Row.output r.outer.val) :=
    (congrArg CellGraph.Row.output (F.nestedRow_outer r.val)).symm.trans (F.row_output r.outer.val)
  let χ' : G.Cell (CellGraph.Row.outerBoundary r'.outer (F.vertical.map p) (F.vertical.map q) (F.shortPath L)) :=
    CellGraph.castInput eo.symm χ
  have hχ : HEq χ χ' := (CellGraph.castInput_heq (G := G)
    (f := F.side ⟨s.bottom, a, p⟩) (g := F.side ⟨t.bottom, b, q⟩) (L := F.shortPath L) eo.symm χ).symm
  have eouter := F.substitute_image A.toOperations r.outer r'.outer rfl rfl (heq_of_eq (F.nestedRow_outer r.val))
    p q (F.vertical.map p) (F.vertical.map q) (HEq.refl _) (HEq.refl _) L (F.shortPath L) rfl χ χ' hχ
  have eright : HEq ((F.pullbackOperations A.toOperations).assocRight r p q L χ)
      (A.assocRight r' (F.vertical.map p) (F.vertical.map q) (F.shortPath L) χ') := by
    apply F.substitute_image A.toOperations r.inner r'.inner rfl rfl (heq_of_eq (F.nestedRow_inner r.val))
      (s.lower ≫ p) (t.lower ≫ q) (F.vertical.map s.lower ≫ F.vertical.map p) (F.vertical.map t.lower ≫ F.vertical.map q)
      (heq_of_eq (F.vertical.map_comp _ _)) (heq_of_eq (F.vertical.map_comp _ _)) L (F.shortPath L) rfl
    exact (CellGraph.castInput_heq _ _).trans (eouter.trans (CellGraph.castInput_heq _ _).symm)
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  apply (F.substitute_image A.toOperations (r.composite (F.pullbackOperations A.toOperations)) (r'.composite A.toOperations)
    (F.side_post s.upper s.lower) (F.side_post t.upper t.lower) (F.nestedRow_composite A.toOperations r.val)
    p q (F.vertical.map p) (F.vertical.map q) (HEq.refl _) (HEq.refl _) L (F.shortPath L) rfl _
    (CellGraph.castInput (Nested.Row.composite_output A.toOperations r'.val).symm χ') ?_).trans
  · exact (A.laws.assoc_heq r' (F.vertical.map p) (F.vertical.map q) (F.shortPath L) χ').trans eright.symm
  · exact (CellGraph.castInput_heq _ _).trans
      (hχ.trans (CellGraph.castInput_heq (G := G) (f := F.side ⟨s.bottom, a, p⟩)
        (g := F.side ⟨t.bottom, b, q⟩) (L := F.shortPath L)
        (Nested.Row.composite_output A.toOperations r'.val).symm χ').symm)

def pullbackAlgebra (A : Algebra G) : Algebra (F.pullback G) where
  toOperations := F.pullbackOperations A.toOperations
  laws := ⟨F.pullback_verticalIdentity_stack A, F.pullback_leftUnit A, F.pullback_rightUnit A,
    F.pullback_insertion A, F.pullback_assoc A⟩

end Kernel.Augmented.BaseMap

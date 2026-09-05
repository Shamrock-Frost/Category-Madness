import Kernel.Augmented.OperationMaps
import Kernel.Augmented.ComparisonTransport

/-! Preservation of the augmented equation instances by operation maps.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c c'
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}
  {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}

namespace CellGraph.Map

theorem row_comp (F : Map G K) {f g k : Side C} (p : G.Row f g) (q : G.Row g k) :
    F.row (p.comp q) = (F.row p).comp (F.row q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (F.row (p.comp q)).cons _ = ((F.row p).comp (F.row q)).cons _
    rw [ih]


def nestedStep (F : Map G K) {s t : Nested.Side C} (e : Nested.Step G s t) : Nested.Step K s t where
  inner := F.nonemptyRow e.inner
  output := e.output
  outer := CellGraph.castInput (F.row_output e.inner.val).symm (F.cell e.outer)

def nestedRow (F : Map G K) {s : Nested.Side C} :
    {t : Nested.Side C} → Nested.Row G s t → Nested.Row K s t
  | _, .nil => .nil
  | _, .cons r e => (F.nestedRow r).cons (F.nestedStep e)

theorem nestedRow_length (F : Map G K) {s t : Nested.Side C} (r : Nested.Row G s t) :
    (F.nestedRow r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

def nestedNonemptyRow (F : Map G K) {s t : Nested.Side C}
    (r : Nested.NonemptyRow G s t) : Nested.NonemptyRow K s t :=
  ⟨F.nestedRow r.val, by rw [F.nestedRow_length]; exact r.property⟩

theorem nestedRow_inner (F : Map G K) {s t : Nested.Side C} (r : Nested.Row G s t) :
    F.row (Nested.Row.inner r) = Nested.Row.inner (F.nestedRow r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change F.row ((Nested.Row.inner r).comp e.inner.val) = _
    rw [F.row_comp, ih]
    rfl

theorem nestedRow_outer (F : Map G K) {s t : Nested.Side C} (r : Nested.Row G s t) :
    F.row (Nested.Row.outer r) = Nested.Row.outer (F.nestedRow r) := by
  induction r with
  | nil => rfl
  | @cons t z r e ih =>
    apply eq_of_heq
    apply CellGraph.Row.cons_heq rfl rfl rfl (heq_of_eq ih)
    · exact heq_of_eq (congrArg (fun p => (⟨p, e.output⟩ : Boundary H t.middle z.middle))
        (F.row_output e.inner.val).symm)
    · exact (CellGraph.castInput_heq (G := K) (f := t.middle) (g := z.middle)
        (L := e.output) (F.row_output e.inner.val).symm (F.cell e.outer)).symm

end CellGraph.Map
namespace Operations.Map
variable {O : Operations G} {O' : Operations K}

private theorem substitute_image (F : O.Map O') {f g : Side C}
    (r : G.NonemptyRow f g) (r' : K.NonemptyRow f g) (er : F.toMap.row r.val = r'.val)
    {a b : C} (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L))
    (ψ' : K.Cell (CellGraph.Row.outerBoundary r' h k L)) (eψ : HEq (F.cell ψ) ψ') :
    HEq (F.cell (O.substitute r h k L ψ)) (O'.substitute r' h k L ψ') := by
  apply (heq_of_eq (F.substitute r h k L ψ)).trans
  apply (CellGraph.castInput_heq _ _).trans
  exact O'.substitute_heq rfl rfl (heq_of_eq er) (HEq.refl _) (HEq.refl _) rfl
    ((CellGraph.castInput_heq _ _).trans eψ)

theorem nestedRow_composite (F : O.Map O') {s t : Nested.Side C} (r : Nested.Row G s t) :
    F.toMap.row (Nested.Row.composite O r) = Nested.Row.composite O' (F.toMap.nestedRow r) := by
  induction r with
  | nil => rfl
  | @cons t z r e ih =>
    apply eq_of_heq
    apply CellGraph.Row.cons_heq rfl rfl rfl (heq_of_eq ih)
    · exact heq_of_eq (congrArg (fun p => (⟨p, e.output⟩ : Boundary H t.composite z.composite))
        (F.toMap.row_input e.inner.val).symm)
    · exact F.substitute_image e.inner (F.toMap.nonemptyRow e.inner) rfl _ _ _ _ _
        (CellGraph.castInput_heq (G := K) (f := t.middle) (g := z.middle)
          (L := e.output) (F.toMap.row_output e.inner.val).symm (F.cell e.outer)).symm

theorem shortIdentity (F : O.Map O') {a b : C} (p : ShortPath H a b) :
    F.cell (O.shortIdentity p) = O'.shortIdentity p := by
  apply ShortPath.cases_on (fun {_ _} p => F.cell (O.shortIdentity p) = O'.shortIdentity p)
  · intro a
    exact F.verticalIdentity (𝟙 a)
  · intro a b j
    exact F.horizontalIdentity j

theorem horizontalIdentities (F : O.Map O') {a b : C} (p : HPath H a b) :
    F.toMap.row (O.horizontalIdentities p) = O'.horizontalIdentities p := by
  induction p with
  | nil => rfl
  | cons p j ih =>
    change (F.toMap.row (O.horizontalIdentities p)).cons
      ⟨_, F.cell (O.horizontalIdentity j)⟩ = _
    rw [ih, F.horizontalIdentity]
    rfl

theorem identityRow (F : O.Map O') {a b : C} (p : HPath H a b) :
    F.toMap.nonemptyRow (O.identityRow p) = O'.identityRow p := by
  apply Subtype.ext
  cases p with
  | nil =>
    change Quiver.Path.cons (V := K.Vertex) .nil ⟨_, F.cell (O.verticalIdentity (𝟙 a))⟩ = _
    rw [F.verticalIdentity]
    rfl
  | cons p j => exact F.horizontalIdentities (Quiver.Path.cons (V := Horizontal H) p j)

theorem verticalStack (F : O.Map O') {a b d : C} {f g : a ⟶ b} {h k : b ⟶ d}
    (α : G.Cell (Boundary.vertical f g)) (β : G.Cell (Boundary.vertical h k)) :
    F.cell (O.verticalStack α β) = O'.verticalStack (F.cell α) (F.cell β) := by
  exact eq_of_heq (F.substitute_image (CellGraph.Row.single α)
    (CellGraph.Row.single (F.cell α)) rfl h k (ShortPath.empty d) β (F.cell β) (HEq.refl _))

theorem leftUnitEquation (F : O.Map O') {f g : Side C} {b : Boundary H f g}
    (φ : G.Cell b) :
    F.cell (CellGraph.transport (Operations.leftUnit_boundary φ) (O.leftUnitComposite φ)) =
      CellGraph.transport (Operations.leftUnit_boundary (F.cell φ))
        (O'.leftUnitComposite (F.cell φ)) := by
  rw [F.toMap.transport]
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  apply (F.substitute_image (CellGraph.Row.single φ) (CellGraph.Row.single (F.cell φ)) rfl
    (𝟙 f.target) (𝟙 g.target) b.output _
    (CellGraph.castInput (CellGraph.Row.output_single (F.cell φ)).symm (O'.shortIdentity b.output)) ?_).trans
  · exact (CellGraph.transport_heq _ _).symm
  · erw [F.toMap.castInput, F.shortIdentity]
    exact (CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _).symm

theorem rightUnitEquation (F : O.Map O') {f g : Side C} {b : Boundary H f g}
    (φ : G.Cell b) :
    F.cell (CellGraph.transport (O.rightUnit_boundary b) (O.rightUnitComposite φ)) =
      CellGraph.transport (O'.rightUnit_boundary b) (O'.rightUnitComposite (F.cell φ)) := by
  rw [F.toMap.transport]
  apply eq_of_heq
  apply (CellGraph.transport_heq _ _).trans
  apply (F.substitute_image (O.identityRow b.input) (O'.identityRow b.input)
    (congrArg Subtype.val (F.identityRow b.input)) f.arrow g.arrow b.output _
    (CellGraph.castInput (O'.identityRow_output b.input).symm (F.cell φ)) ?_).trans
  · exact (CellGraph.transport_heq _ _).symm
  · erw [F.toMap.castInput]
    exact (CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _).symm


theorem insertedRow (F : O.Map O') {f g k : Side C} (p : G.Row f g) (q : G.Row g k) :
    F.toMap.nonemptyRow (O.insertedRow p q) = O'.insertedRow (F.toMap.row p) (F.toMap.row q) := by
  apply Subtype.ext
  change F.toMap.row ((p.cons ⟨_, O.verticalIdentity g.arrow⟩).comp q) = _
  rw [F.toMap.row_comp]
  change ((F.toMap.row p).cons ⟨_, F.cell (O.verticalIdentity g.arrow)⟩).comp (F.toMap.row q) = _
  rw [F.verticalIdentity]
  rfl

theorem insertion_iff (F : O.Map O') {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) (hn : 0 < (p.comp q).length)
    {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    F.cell (CellGraph.transport (O.inserted_boundary p q hn h l L)
      (O.insertedComposite p q hn h l L ψ)) = F.cell (O.substitute ⟨p.comp q, hn⟩ h l L ψ) ↔
      let p' := F.toMap.row p
      let q' := F.toMap.row q
      let hn' : 0 < (p'.comp q').length := by rw [← F.toMap.row_comp, F.toMap.row_length]; exact hn
      let eo : CellGraph.Row.output (p'.comp q') = CellGraph.Row.output (p.comp q) := by
        rw [← F.toMap.row_comp, F.toMap.row_output]
      let ψ' := CellGraph.castInput (G := K) (f := ⟨f.target, a, h⟩) (g := ⟨k.target, b, l⟩)
        (L := L) eo.symm (F.cell ψ)
      CellGraph.transport (O'.inserted_boundary p' q' hn' h l L)
        (O'.insertedComposite p' q' hn' h l L ψ') = O'.substitute ⟨p'.comp q', hn'⟩ h l L ψ' := by
  let p' := F.toMap.row p
  let q' := F.toMap.row q
  have hn' : 0 < (p'.comp q').length := by
    rw [← F.toMap.row_comp, F.toMap.row_length]
    exact hn
  have eo : CellGraph.Row.output (p'.comp q') = CellGraph.Row.output (p.comp q) := by
    rw [← F.toMap.row_comp, F.toMap.row_output]
  let ψ' : K.Cell (CellGraph.Row.outerBoundary ⟨p'.comp q', hn'⟩ h l L) :=
    CellGraph.castInput eo.symm (F.cell ψ)
  have E := F.substitute_image ⟨p.comp q, hn⟩ ⟨p'.comp q', hn'⟩
    (F.toMap.row_comp p q) h l L ψ ψ' (CellGraph.castInput_heq _ _).symm

  have EL : HEq (F.cell (CellGraph.transport (O.inserted_boundary p q hn h l L)
      (O.insertedComposite p q hn h l L ψ)))
      (O'.insertedComposite p' q' hn' h l L ψ') := by
    rw [F.toMap.transport]
    apply (CellGraph.transport_heq _ _).trans
    apply F.substitute_image (O.insertedRow p q) (O'.insertedRow p' q')
      (congrArg Subtype.val (F.insertedRow p q)) h l L
    erw [F.toMap.castInput]
    exact (CellGraph.castInput_heq _ _).trans
      ((CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _)).symm
  constructor
  · intro e
    apply eq_of_heq
    exact (CellGraph.transport_heq _ _).trans (EL.symm.trans ((heq_of_eq e).trans E))
  · intro e
    apply eq_of_heq
    exact EL.trans (((CellGraph.transport_eq_iff_heq _ _ _).mp e).trans E.symm)

theorem insertion (F : O.Map O') (A : Laws O') {f g k : Side C}
    (p : G.Row f g) (q : G.Row g k) (hn : 0 < (p.comp q).length)
    {a b : C} (h : f.target ⟶ a) (l : k.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary ⟨p.comp q, hn⟩ h l L)) :
    F.cell (CellGraph.transport (O.inserted_boundary p q hn h l L)
      (O.insertedComposite p q hn h l L ψ)) = F.cell (O.substitute ⟨p.comp q, hn⟩ h l L ψ) := by
  apply (F.insertion_iff p q hn h l L ψ).mpr
  exact A.insertion _ _ _ h l L _

theorem assoc_iff (F : O.Map O') {s t : Nested.Side C}
    (r : Nested.NonemptyRow G s t) {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b)
    (L : ShortPath H a b) (χ : G.Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    F.cell (CellGraph.transport (O.assoc_boundary r p q L) (O.assocLeft r p q L χ)) =
      F.cell (O.assocRight r p q L χ) ↔
      let r' := F.toMap.nestedNonemptyRow r
      let eo : CellGraph.Row.output r'.outer.val = CellGraph.Row.output r.outer.val :=
        (congrArg CellGraph.Row.output (F.toMap.nestedRow_outer r.val)).symm.trans
          (F.toMap.row_output r.outer.val)
      let χ' := CellGraph.castInput (G := K) (f := ⟨s.bottom, a, p⟩) (g := ⟨t.bottom, b, q⟩)
        (L := L) eo.symm (F.cell χ)
      CellGraph.transport (O'.assoc_boundary r' p q L) (O'.assocLeft r' p q L χ') =
        O'.assocRight r' p q L χ' := by
  let r' := F.toMap.nestedNonemptyRow r
  have eo : CellGraph.Row.output r'.outer.val = CellGraph.Row.output r.outer.val := by
    exact (congrArg CellGraph.Row.output (F.toMap.nestedRow_outer r.val)).symm.trans
      (F.toMap.row_output r.outer.val)
  let χ' : K.Cell (CellGraph.Row.outerBoundary r'.outer p q L) :=
    CellGraph.castInput eo.symm (F.cell χ)
  have eouter := F.substitute_image r.outer r'.outer (F.toMap.nestedRow_outer r.val)
    p q L χ χ' (CellGraph.castInput_heq _ _).symm
  have eright : HEq (F.cell (O.assocRight r p q L χ)) (O'.assocRight r' p q L χ') := by
    apply F.substitute_image r.inner r'.inner (F.toMap.nestedRow_inner r.val)
    erw [F.toMap.castInput]
    exact (CellGraph.castInput_heq _ _).trans
      (eouter.trans (CellGraph.castInput_heq _ _).symm)

  have eleft : HEq (F.cell (CellGraph.transport (O.assoc_boundary r p q L) (O.assocLeft r p q L χ)))
      (O'.assocLeft r' p q L χ') := by
    rw [F.toMap.transport]
    apply (CellGraph.transport_heq _ _).trans
    apply F.substitute_image (r.composite O) (r'.composite O') (F.nestedRow_composite r.val)
      p q L
    erw [F.toMap.castInput]
    exact (CellGraph.castInput_heq _ _).trans
      ((CellGraph.castInput_heq _ _).trans (CellGraph.castInput_heq _ _)).symm
  constructor
  · intro e
    apply eq_of_heq
    exact (CellGraph.transport_heq _ _).trans (eleft.symm.trans ((heq_of_eq e).trans eright))
  · intro e
    apply eq_of_heq
    exact eleft.trans (((CellGraph.transport_eq_iff_heq _ _ _).mp e).trans eright.symm)

theorem assoc (F : O.Map O') (A : Laws O') {s t : Nested.Side C}
    (r : Nested.NonemptyRow G s t) {a b : C} (p : s.bottom ⟶ a) (q : t.bottom ⟶ b)
    (L : ShortPath H a b) (χ : G.Cell (CellGraph.Row.outerBoundary r.outer p q L)) :
    F.cell (CellGraph.transport (O.assoc_boundary r p q L) (O.assocLeft r p q L χ)) =
      F.cell (O.assocRight r p q L χ) := by
  apply (F.assoc_iff r p q L χ).mpr
  exact A.assoc _ p q L _

end Operations.Map
end Kernel.Augmented

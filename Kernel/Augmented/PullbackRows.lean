import Kernel.Augmented.PullbackIdentityRows

/-! Incident row and nested-row maps under change of base.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.BaseMap
universe u v h u' v' h' c
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {H : C → C → Type h} {K : D → D → Type h'}
  (F : BaseMap H K) {G : CellGraph.{u',v',h',c} D K}

theorem row_comp {f g k : Side C} (p : (F.pullback G).Row f g) (q : (F.pullback G).Row g k) :
    F.row (p.comp q) = (F.row p).comp (F.row q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (F.row (p.comp q)).cons _ = ((F.row p).comp (F.row q)).cons _
    rw [ih]

theorem pullback_insertedRow (O : Operations G) {f g k : Side C}
    (p : (F.pullback G).Row f g) (q : (F.pullback G).Row g k) :
    F.row ((F.pullbackOperations O).insertedRow p q).val = (O.insertedRow (F.row p) (F.row q)).val := by
  change F.row ((p.cons ⟨_, (F.pullbackOperations O).verticalIdentity g.arrow⟩).comp q) = _
  rw [F.row_comp]
  rfl

def nestedSide (s : Nested.Side C) : Nested.Side D := ⟨F.side s.upper, F.vertical.obj s.bottom, F.vertical.map s.lower⟩

def nestedStep {s t : Nested.Side C} (e : Nested.Step (F.pullback G) s t) :
    Nested.Step G (F.nestedSide s) (F.nestedSide t) where
  inner := F.nonemptyRow e.inner
  output := F.shortPath e.output
  outer := CellGraph.castInput (G := G) (F.row_output e.inner.val).symm e.outer

def nestedRow (F : BaseMap H K) {G : CellGraph.{u',v',h',c} D K} {s : Nested.Side C} :
    {t : Nested.Side C} → Nested.Row (F.pullback G) s t → Nested.Row G (F.nestedSide s) (F.nestedSide t)
  | _, .nil => .nil
  | _, .cons r e => (F.nestedRow r).cons (F.nestedStep e)

theorem nestedRow_length {s t : Nested.Side C} (r : Nested.Row (F.pullback G) s t) :
    (F.nestedRow r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

def nestedNonemptyRow {s t : Nested.Side C} (r : Nested.NonemptyRow (F.pullback G) s t) :
    Nested.NonemptyRow G (F.nestedSide s) (F.nestedSide t) :=
  ⟨F.nestedRow r.val, by rw [F.nestedRow_length]; exact r.property⟩

theorem nestedRow_inner {s t : Nested.Side C} (r : Nested.Row (F.pullback G) s t) :
    F.row (Nested.Row.inner r) = Nested.Row.inner (F.nestedRow r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change F.row ((Nested.Row.inner r).comp e.inner.val) = _
    rw [F.row_comp, ih]
    rfl

theorem nestedRow_outer {s t : Nested.Side C} (r : Nested.Row (F.pullback G) s t) :
    F.row (Nested.Row.outer r) = Nested.Row.outer (F.nestedRow r) := by
  induction r with
  | nil => rfl
  | @cons t z r e ih =>
    apply eq_of_heq
    apply CellGraph.Row.cons_heq rfl rfl rfl (heq_of_eq ih)
    · exact heq_of_eq (congrArg (fun p => (⟨p, F.shortPath e.output⟩ : Boundary K
        (F.side t.middle) (F.side z.middle))) (F.row_output e.inner.val).symm)
    · exact (CellGraph.castInput_heq (G := G) (f := F.side t.middle) (g := F.side z.middle)
        (L := F.shortPath e.output) (F.row_output e.inner.val).symm e.outer).symm

end Kernel.Augmented.BaseMap

import Kernel.Augmented.BaseMapComposition
import Kernel.Augmented.PullbackIdentityRows

/-! Maps of cells over changing bases, with their complete boundaries retained.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.CellGraph
universe u v h c u' v' h' c' u'' v'' h'' c'' u''' v''' h''' c'''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {J : Type u'''} [Category.{v'''} J]
  {H : C → C → Type h} {K : D → D → Type h'} {L : E → E → Type h''}
  {N : J → J → Type h'''}
  {G : CellGraph.{u,v,h,c} C H} {G' : CellGraph.{u',v',h',c'} D K}
  {G'' : CellGraph.{u'',v'',h'',c''} E L} {G''' : CellGraph.{u''',v''',h''',c'''} J N}

/-- A cell together with its entire incident boundary. -/
abbrev Total (G : CellGraph.{u,v,h,c} C H) := Σ b : CellBoundary C H, G.family b

def pack {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) : G.Total := ⟨b.frame, φ⟩

theorem Total.cell_heq {x y : G.Total} (e : x = y) : HEq x.2 y.2 := by cases e; rfl

theorem pack_transport {f g f' g' : Side C} {b : Boundary H f g} {b' : Boundary H f' g'}
    (e : b.frame = b'.frame) (φ : G.Cell b) : pack (transport (G := G) e φ) = pack φ :=
  Sigma.ext e.symm (transport_heq e φ)

/-- A cell map records its base map and preserves each full boundary. -/
structure OverMap (G : CellGraph.{u,v,h,c} C H) (G' : CellGraph.{u',v',h',c'} D K) where
  base : BaseMap H K
  total : G.Total → G'.Total
  boundary : ∀ x, (total x).1 = base.frame x.1

namespace OverMap

@[ext] theorem ext (F I : OverMap G G') (hb : F.base = I.base) (ht : F.total = I.total) : F = I := by
  cases F; cases I; cases hb; cases ht; rfl

def id (G : CellGraph.{u,v,h,c} C H) : OverMap G G where
  base := BaseMap.id H
  total x := x
  boundary x := (BaseMap.id_frame x.1).symm

def comp (F : OverMap G G') (I : OverMap G' G'') : OverMap G G'' where
  base := F.base.comp I.base
  total x := I.total (F.total x)
  boundary x := by rw [I.boundary, F.boundary, BaseMap.comp_frame]

@[simp] theorem id_comp (F : OverMap G G') : (id G).comp F = F :=
  ext _ _ (BaseMap.id_comp F.base) rfl
@[simp] theorem comp_id (F : OverMap G G') : F.comp (id G') = F :=
  ext _ _ (BaseMap.comp_id F.base) rfl
@[simp] theorem comp_assoc (F : OverMap G G') (I : OverMap G' G'') (P : OverMap G'' G''') :
    (F.comp I).comp P = F.comp (I.comp P) := rfl

def cell (F : OverMap G G') {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) :
    G'.Cell (F.base.boundary b) :=
  cast (congrArg G'.family (F.boundary (pack φ))) (F.total (pack φ)).2

theorem pack_cell (F : OverMap G G') {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) :
    pack (F.cell φ) = F.total (pack φ) :=
  Sigma.ext (F.boundary (pack φ)).symm (cast_heq _ _)

theorem cell_transport (F : OverMap G G') {f g f' g' : Side C}
    {b : Boundary H f g} {b' : Boundary H f' g'} (e : b.frame = b'.frame) (φ : G.Cell b) :
    F.cell (transport (G := G) e φ) = transport (G := G') (congrArg F.base.frame e) (F.cell φ) := by
  apply eq_of_heq
  have h := congrArg F.total (pack_transport e φ)
  rw [← F.pack_cell, ← F.pack_cell] at h
  exact (Total.cell_heq h).trans (transport_heq (G := G') _ _).symm

theorem comp_cell (F : OverMap G G') (I : OverMap G' G'') {f g : Side C}
    {b : Boundary H f g} (φ : G.Cell b) :
    HEq ((F.comp I).cell φ) (I.cell (F.cell φ)) := by
  apply Total.cell_heq (x := pack (G := G'') ((F.comp I).cell φ)) (y := pack (G := G'') (I.cell (F.cell φ)))
  rw [(F.comp I).pack_cell, I.pack_cell, F.pack_cell]
  rfl

theorem id_cell {f g : Side C} {b : Boundary H f g} (φ : G.Cell b) : HEq ((id G).cell φ) φ :=
  Total.cell_heq ((id G).pack_cell φ)

def row (F : OverMap G G') {f : Side C} : {g : Side C} → G.Row f g → G'.Row (F.base.side f) (F.base.side g)
  | _, .nil => .nil
  | _, .cons r e => (F.row r).cons ⟨F.base.boundary e.1, F.cell e.2⟩

theorem row_length (F : OverMap G G') {f g : Side C} (r : G.Row f g) : (F.row r).length = r.length := by
  induction r with
  | nil => rfl
  | cons r e ih => exact congrArg Nat.succ ih

theorem row_input (F : OverMap G G') {f g : Side C} (r : G.Row f g) :
    Row.input (F.row r) = F.base.path (Row.input r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (Row.input (F.row r)).comp (F.base.path e.1.input) =
      F.base.path ((Row.input r).comp e.1.input)
    rw [ih, F.base.path_comp]
    rfl

theorem row_output (F : OverMap G G') {f g : Side C} (r : G.Row f g) :
    Row.output (F.row r) = F.base.path (Row.output r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    change (Row.output (F.row r)).comp (F.base.path e.1.output.val) =
      F.base.path ((Row.output r).comp e.1.output.val)
    rw [ih, F.base.path_comp]
    rfl

def nonemptyRow (F : OverMap G G') {f g : Side C} (r : G.NonemptyRow f g) :
    G'.NonemptyRow (F.base.side f) (F.base.side g) := ⟨F.row r.val, by rw [F.row_length]; exact r.property⟩

theorem comp_row (F : OverMap G G') (I : OverMap G' G'') {f g : Side C} (r : G.Row f g) :
    (F.comp I).row r = I.row (F.row r) := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    apply eq_of_heq
    exact Row.cons_heq rfl rfl rfl (heq_of_eq ih) (Boundary.heq_of_frame_eq (BaseMap.comp_frame _ _ e.1.frame))
      (F.comp_cell I e.2)

theorem id_row {f g : Side C} (r : G.Row f g) : (id G).row r = r := by
  induction r with
  | nil => rfl
  | cons r e ih =>
    apply eq_of_heq
    exact Row.cons_heq rfl rfl rfl (heq_of_eq ih)
      (Boundary.heq_of_frame_eq (BaseMap.id_frame e.1.frame)) (id_cell e.2)

end OverMap
end Kernel.Augmented.CellGraph

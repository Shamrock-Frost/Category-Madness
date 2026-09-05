import Kernel.Augmented.GlobalSubstitutionMaps
import Kernel.Augmented.Algebra

/-! The category of augmented algebras with varying objects, arrows and cells.
Preservation laws are equalities of cells with their entire boundaries attached.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c u' v' h' c' u'' v'' h'' c'' u''' v''' h''' c''' w
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {J : Type u'''} [Category.{v'''} J]
  {H : C → C → Type h} {K : D → D → Type h'} {L : E → E → Type h''}
  {N : J → J → Type h'''}
  {G : CellGraph.{u,v,h,c} C H} {G' : CellGraph.{u',v',h',c'} D K}
  {G'' : CellGraph.{u'',v'',h'',c''} E L} {G''' : CellGraph.{u''',v''',h''',c'''} J N}

open CellGraph in
structure Operations.OverMap (O : Operations G) (O' : Operations G') extends CellGraph.OverMap G G' where
  horizontalIdentity : ∀ {a b : C} (j : H a b),
    total (pack (O.horizontalIdentity j)) = pack (O'.horizontalIdentity (base.horizontal j))
  verticalIdentity : ∀ {a b : C} (f : a ⟶ b),
    total (pack (O.verticalIdentity f)) = pack (O'.verticalIdentity (base.vertical.map f))
  substitute : ∀ {f g : Side C} (r : G.NonemptyRow f g) {a b : C}
    (h : f.target ⟶ a) (k : g.target ⟶ b) (L : ShortPath H a b)
    (ψ : G.Cell (CellGraph.Row.outerBoundary r h k L)),
    total (pack (O.substitute r h k L ψ)) = toOverMap.substituteImage O' r h k L ψ

namespace Operations.OverMap
variable {O : Operations G} {O' : Operations G'} {O'' : Operations G''} {O''' : Operations G'''}

@[ext] theorem ext (F I : O.OverMap O') (h : F.toOverMap = I.toOverMap) : F = I := by
  cases F; cases I; cases h; rfl

def id (O : Operations G) : O.OverMap O where
  toOverMap := CellGraph.OverMap.id G
  horizontalIdentity j := rfl
  verticalIdentity f := rfl
  substitute := by
    intro f g r a b h k L ψ
    exact (CellGraph.OverMap.id_substituteImage O r h k L ψ).symm

def comp (F : O.OverMap O') (I : O'.OverMap O'') : O.OverMap O'' where
  toOverMap := F.toOverMap.comp I.toOverMap
  horizontalIdentity j := by
    change I.total (F.total _) = _
    rw [F.horizontalIdentity, I.horizontalIdentity]
    rfl
  verticalIdentity f := by
    change I.total (F.total _) = _
    rw [F.verticalIdentity, I.verticalIdentity]
    rfl
  substitute := by
    intro f g r a b h k L ψ
    change I.total (F.total _) = _
    rw [F.substitute, CellGraph.OverMap.comp_substituteImage]
    exact I.substitute _ _ _ _ _

@[simp] theorem id_comp (F : O.OverMap O') : (id O).comp F = F :=
  ext _ _ (CellGraph.OverMap.id_comp F.toOverMap)
@[simp] theorem comp_id (F : O.OverMap O') : F.comp (id O') = F :=
  ext _ _ (CellGraph.OverMap.comp_id F.toOverMap)
@[simp] theorem comp_assoc (F : O.OverMap O') (I : O'.OverMap O'') (P : O''.OverMap O''') :
    (F.comp I).comp P = F.comp (I.comp P) := rfl

end Operations.OverMap

/-- Small augmented algebras in one chosen universe, for the global adjunction. -/
structure BundledAlgebra where
  Obj : Type w
  vertical : Category.{w} Obj
  horizontal : Obj → Obj → Type w
  cells : @CellGraph.{w,w,w,w} Obj vertical.toQuiver horizontal
  algebra : @Algebra.{w,w,w,w} Obj vertical horizontal cells

attribute [instance] BundledAlgebra.vertical

instance : Category BundledAlgebra.{w} where
  Hom A B := A.algebra.toOperations.OverMap B.algebra.toOperations
  id A := Operations.OverMap.id A.algebra.toOperations
  comp F I := F.comp I
  id_comp := Operations.OverMap.id_comp
  comp_id := Operations.OverMap.comp_id
  assoc := Operations.OverMap.comp_assoc

end Kernel.Augmented

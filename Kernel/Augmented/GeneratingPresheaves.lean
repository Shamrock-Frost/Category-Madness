import Kernel.Augmented.GeneratingShapes

/-! Generating augmented incidence as presheaves on the elementary boundary category.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory Opposite
namespace Kernel.Augmented.Generating
universe w

/-- Unbundled incidence data before any vertical or cell composition is supplied. -/
structure Graph where
  Object : Type w
  Vertical : Type w
  Horizontal : Type w
  Cell : ℕ → Bool → Type w
  verticalEndpoint : Bool → Vertical → Object
  horizontalEndpoint : Bool → Horizontal → Object
  cellVertex : {n : ℕ} → {ε : Bool} → Vertex n ε → Cell n ε → Object
  cellVertical : {n : ℕ} → {ε : Bool} → Bool → Cell n ε → Vertical
  cellHorizontal : {n : ℕ} → {ε : Bool} → HorizontalEdge n ε → Cell n ε → Horizontal
  vertical_incidence : ∀ {n ε} (side endpoint : Bool) (x : Cell n ε),
    verticalEndpoint endpoint (cellVertical side x) = cellVertex (Generating.verticalEndpoint n ε side endpoint) x
  horizontal_incidence : ∀ {n ε} (i : HorizontalEdge n ε) (endpoint : Bool) (x : Cell n ε),
    horizontalEndpoint endpoint (cellHorizontal i x) = cellVertex (edgeEndpoint i endpoint) x

namespace Graph

def value (G : Graph.{w}) : Shape → Type w
  | .point => G.Object
  | .vertical => G.Vertical
  | .horizontal => G.Horizontal
  | .cell n ε => G.Cell n ε

def restrict (G : Graph.{w}) {x y : Shape} : Hom x y → G.value y → G.value x
  | .id _ => fun x => x
  | .verticalEndpoint e => G.verticalEndpoint e
  | .horizontalEndpoint e => G.horizontalEndpoint e
  | .cellVertex i => G.cellVertex i
  | .cellVertical side => G.cellVertical side
  | .cellHorizontal i => G.cellHorizontal i

theorem restrict_comp (G : Graph.{w}) {x y z : Shape} (f : Hom x y) (g : Hom y z) (a : G.value z) :
    G.restrict (Hom.comp f g) a = G.restrict f (G.restrict g a) := by
  cases f <;> cases g
  all_goals first | rfl | exact (G.vertical_incidence _ _ _).symm | exact (G.horizontal_incidence _ _ _).symm

def toPresheaf (G : Graph.{w}) : Presheaf.{w} where
  obj x := G.value x.unop
  map f := ↾G.restrict f.unop
  map_id x := rfl
  map_comp f g := by
    ext a
    exact G.restrict_comp g.unop f.unop a

def ofPresheaf (P : Presheaf.{w}) : Graph.{w} where
  Object := P.obj (op .point)
  Vertical := P.obj (op .vertical)
  Horizontal := P.obj (op .horizontal)
  Cell n ε := P.obj (op (.cell n ε))
  verticalEndpoint e := P.map (Hom.verticalEndpoint e : Shape.point ⟶ Shape.vertical).op
  horizontalEndpoint e := P.map (Hom.horizontalEndpoint e : Shape.point ⟶ Shape.horizontal).op
  cellVertex i := P.map (Hom.cellVertex i : Shape.point ⟶ Shape.cell _ _).op
  cellVertical side := P.map (Hom.cellVertical side : Shape.vertical ⟶ Shape.cell _ _).op
  cellHorizontal i := P.map (Hom.cellHorizontal i : Shape.horizontal ⟶ Shape.cell _ _).op
  vertical_incidence := by
    intro n ε side endpoint x
    exact (P.map_comp_apply (Hom.cellVertical side : Shape.vertical ⟶ Shape.cell n ε).op
      (Hom.verticalEndpoint endpoint : Shape.point ⟶ Shape.vertical).op x).symm
  horizontal_incidence := by
    intro n ε i endpoint x
    exact (P.map_comp_apply (Hom.cellHorizontal i : Shape.horizontal ⟶ Shape.cell n ε).op
      (Hom.horizontalEndpoint endpoint : Shape.point ⟶ Shape.horizontal).op x).symm

theorem of_toPresheaf (G : Graph.{w}) : ofPresheaf G.toPresheaf = G := by
  cases G
  rfl

theorem to_ofPresheaf (P : Presheaf.{w}) : (ofPresheaf P).toPresheaf = P := by
  apply Functor.hext
  · rintro ⟨x⟩
    cases x <;> rfl
  · rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
    cases f with
    | id x =>
      cases x <;> apply heq_of_eq <;> exact (P.map_id _).symm
    | verticalEndpoint => rfl
    | horizontalEndpoint => rfl
    | cellVertex => rfl
    | cellVertical => rfl
    | cellHorizontal => rfl

/-- The global generating data is exactly a presheaf on the elementary incidence category. -/
def presheafEquiv : Graph.{w} ≃ Presheaf.{w} where
  toFun := toPresheaf
  invFun := ofPresheaf
  left_inv := of_toPresheaf
  right_inv := to_ofPresheaf

end Graph
end Kernel.Augmented.Generating

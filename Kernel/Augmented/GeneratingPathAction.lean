import Kernel.Augmented.GeneratingComparisonBase
import Kernel.Augmented.PathEvaluation

/-! The vertical path action of an arbitrary algebra for the generating monad.
Cites: D-KR-15, D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented
universe w
open Generating

namespace Generating.Graph
variable {G H : Graph.{w}}

/-- The vertical quiver map of any incidence-natural generating graph map. -/
def verticalMap (F : G ⟶ H) : G.Objects ⥤q H.Objects where
  obj := mapObject F
  map e := ⟨mapVertical F e.val,
    (map_verticalEndpoint F false e.val).trans (congrArg (mapObject F) e.property.1),
    (map_verticalEndpoint F true e.val).trans (congrArg (mapObject F) e.property.2)⟩

theorem free_map_generator (F : G ⟶ H) {a b : G.Objects} (e : a ⟶ b) :
    (BundledAlgebra.free.map F).base.vertical.map e.toPath =
      ((verticalMap F).map e).toPath := by
  have h := BundledAlgebra.freeForgetAdjunction.unit.naturality F
  erw [BundledAlgebra.freeForgetAdjunction_unit,
    BundledAlgebra.freeForgetAdjunction_unit] at h
  have he := congrArg (fun f : G ⟶ BundledAlgebra.forget.obj H.freeObject => mapVertical f e.val) h
  change H.unitVertical (mapVertical F e.val) =
    FinPath.mapEdge (BundledAlgebra.free.map F).base.vertical.toPrefunctor
      (G.unitVertical e.val) at he
  have hp := G.verticalPack_fiber e
  have hq := H.verticalPack_fiber ((verticalMap F).map e)
  unfold unitVertical at he
  erw [← hp, ← hq] at he
  exact (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2).symm

/-- The vertical part of the free functor maps every edge of a path. -/
theorem free_map_path (F : G ⟶ H) {a b : G.Objects} (p : Quiver.Path a b) :
    (BundledAlgebra.free.map F).base.vertical.map p = (verticalMap F).mapPath p := by
  induction p with
  | nil => exact (BundledAlgebra.free.map F).base.vertical.map_id _
  | cons p e ih =>
    change (BundledAlgebra.free.map F).base.vertical.map (p ≫ e.toPath) = _
    erw [Functor.map_comp, ih, free_map_generator]
    rfl

end Generating.Graph

namespace GeneratingMonadAlgebra
variable (A : BundledAlgebra.generatingMonad.{w}.Algebra)

/-- The monad unit law forces the action to fix every object. -/
theorem action_object (a : A.A.Objects) : Graph.mapObject A.a a = a := by
  have h := A.unit
  change BundledAlgebra.freeForgetAdjunction.unit.app A.A ≫ A.a = 𝟙 A.A at h
  erw [BundledAlgebra.freeForgetAdjunction_unit] at h
  exact congrArg (fun f : A.A ⟶ A.A => Graph.mapObject f a) h

/-- Evaluate a vertical path, retaining its source and target in the original graph. -/
def evalPath {a b : A.A.Objects} (p : Quiver.Path a b) : a ⟶ b :=
  ⟨Graph.mapVertical A.a ⟨a, b, p⟩,
    (Graph.map_verticalEndpoint A.a false ⟨a, b, p⟩).trans (action_object A a),
    (Graph.map_verticalEndpoint A.a true ⟨a, b, p⟩).trans (action_object A b)⟩

theorem evalPath_single {a b : A.A.Objects} (e : a ⟶ b) : evalPath A e.toPath = e := by
  apply Subtype.ext
  have h := A.unit
  change BundledAlgebra.freeForgetAdjunction.unit.app A.A ≫ A.a = 𝟙 A.A at h
  erw [BundledAlgebra.freeForgetAdjunction_unit] at h
  have he := congrArg (fun f : A.A ⟶ A.A => Graph.mapVertical f e.val) h
  change Graph.mapVertical A.a (A.A.unitVertical e.val) = e.val at he
  unfold Graph.unitVertical at he
  erw [← A.A.verticalPack_fiber e] at he
  exact he

private theorem edge_comp {C : Type w} [Category.{w} C]
    {a b c a' b' c' : C} (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c')
    (hf : (⟨a, b, f⟩ : FinPath.Edge C) = ⟨a', b', f'⟩)
    (hg : (⟨b, c, g⟩ : FinPath.Edge C) = ⟨b', c', g'⟩) :
    (⟨a, c, f ≫ g⟩ : FinPath.Edge C) = ⟨a', c', f' ≫ g'⟩ := by
  have ha : a = a' := congrArg Sigma.fst hf
  have hb : b = b' := congrArg Sigma.fst hg
  have hc : c = c' := congrArg (fun e : FinPath.Edge C => e.2.1) hg
  cases ha; cases hb; cases hc
  have he : f = f' := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hf).2)).2
  have hi : g = g' := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hg).2)).2
  cases he; cases hi; rfl

private theorem free_action_single {a b : A.A.Objects} (p : Quiver.Path a b) :
    FinPath.mapEdge (BundledAlgebra.free.map A.a).base.vertical.toPrefunctor
      ⟨a, b, (Paths.of (BundledAlgebra.forget.obj A.A.freeObject).Objects).map (A.A.freeObject.arrowGenerators.map p)⟩ =
      (⟨a, b, (evalPath A p).toPath⟩ : FinPath.Edge (Paths A.A.Objects)) := by
  change (⟨Graph.mapObject A.a a, Graph.mapObject A.a b,
    (BundledAlgebra.free.map A.a).base.vertical.map
      (A.A.freeObject.arrowGenerators.map p).toPath⟩ : FinPath.Edge (Paths A.A.Objects)) = _
  erw [Graph.free_map_generator]
  exact congrArg (FinPath.mapEdge (Paths.of A.A.Objects))
    ((A.A.verticalPack_fiber ((Graph.verticalMap A.a).map (A.A.freeObject.arrowGenerators.map p))).trans
      (A.A.verticalPack_fiber (evalPath A p)).symm)

/-- The monad associativity law evaluates concatenation by evaluating its two paths first. -/
theorem evalPath_flatten {a b c : A.A.Objects} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    evalPath A (p.comp q) = evalPath A ((evalPath A p).toPath.comp (evalPath A q).toPath) := by
  let p0 := (Paths.of (BundledAlgebra.forget.obj A.A.freeObject).Objects).map (A.A.freeObject.arrowGenerators.map p)
  let q0 := (Paths.of (BundledAlgebra.forget.obj A.A.freeObject).Objects).map (A.A.freeObject.arrowGenerators.map q)
  have h := congrArg (fun f : BundledAlgebra.generatingMonad.toFunctor.obj
      (BundledAlgebra.generatingMonad.toFunctor.obj A.A) ⟶ A.A =>
    Graph.mapVertical f ⟨a, c, p0 ≫ q0⟩) A.assoc
  change Graph.mapVertical A.a
      (FinPath.mapEdge (BundledAlgebra.evaluation A.A.freeObject).base.vertical.toPrefunctor
        ⟨a, c, p0 ≫ q0⟩) =
    Graph.mapVertical A.a
      (FinPath.mapEdge (BundledAlgebra.free.map A.a).base.vertical.toPrefunctor
        ⟨a, c, p0 ≫ q0⟩) at h
  have hm : FinPath.mapEdge (BundledAlgebra.evaluation A.A.freeObject).base.vertical.toPrefunctor
      ⟨a, c, p0 ≫ q0⟩ = (⟨a, c, p.comp q⟩ : FinPath.Edge (Paths A.A.Objects)) := by
    change (⟨a, c, (BundledAlgebra.evaluation A.A.freeObject).base.vertical.map (p0 ≫ q0)⟩ :
      FinPath.Edge (Paths A.A.Objects)) = _
    erw [Functor.map_comp]
    dsimp [p0, q0]
    erw [BundledAlgebra.evaluation_generator, BundledAlgebra.evaluation_generator]
    rfl
  have hf : FinPath.mapEdge (BundledAlgebra.free.map A.a).base.vertical.toPrefunctor
      ⟨a, c, p0 ≫ q0⟩ =
      (⟨a, c, (evalPath A p).toPath.comp (evalPath A q).toPath⟩ :
        FinPath.Edge (Paths A.A.Objects)) := by
    change (⟨_, _, (BundledAlgebra.free.map A.a).base.vertical.map (p0 ≫ q0)⟩ :
      FinPath.Edge (Paths A.A.Objects)) = _
    erw [Functor.map_comp]
    exact edge_comp _ _ _ _ (free_action_single A p) (free_action_single A q)
  erw [hm, hf] at h
  exact Subtype.ext h

/-- Every generating-monad algebra supplies lawful evaluation of vertical paths. -/
def pathEvaluation : PathEvaluation A.A.Objects where
  eval := evalPath A
  single := evalPath_single A
  flatten := evalPath_flatten A

/-- The vertical category reconstructed solely from the two monad-algebra laws. -/
abbrev Vertical := (pathEvaluation A).Objects

/-- Evaluation of free vertical paths into the reconstructed category. -/
def verticalEvaluation : Paths A.A.Objects ⥤ Vertical A := (pathEvaluation A).evaluation

/-- The horizontal graph is retained over the reconstructed vertical category. -/
abbrev horizontal (a b : Vertical A) : Type w := A.A.horizontal a b

/-- The action fixes each horizontal generator, with its original incident endpoints. -/
theorem action_horizontal {a b : A.A.Objects} (j : A.A.horizontal a b) :
    Graph.mapHorizontal A.a
      (⟨a, b, j⟩ : FinPath.Edge (Kernel.Augmented.Horizontal A.A.freeHorizontal)) = j.val := by
  have h := A.unit
  change BundledAlgebra.freeForgetAdjunction.unit.app A.A ≫ A.a = 𝟙 A.A at h
  rw [BundledAlgebra.freeForgetAdjunction_unit] at h
  have he := congrArg (fun f : A.A ⟶ A.A => Graph.mapHorizontal f j.val) h
  change Graph.mapHorizontal A.a (A.A.unitHorizontal j.val) = j.val at he
  unfold Graph.unitHorizontal at he
  erw [← A.A.horizontalPack_fiber j] at he
  exact he

/-- Evaluation of the complete vertical/horizontal base, ready for cell reconstruction. -/
def evaluationBase : BaseMap A.A.freeHorizontal (horizontal A) where
  vertical := verticalEvaluation A
  horizontal j := j

end GeneratingMonadAlgebra
end Kernel.Augmented

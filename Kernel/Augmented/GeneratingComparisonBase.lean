import Kernel.Augmented.GeneratingEvaluation

/-! Recover vertical functoriality from compatibility with free evaluation.
Cites: D-KR-18, D-RT-30, AT-FD-7.
-/

open CategoryTheory
noncomputable section
namespace Kernel.Augmented.BundledAlgebra
universe w
open Generating

/-- Include each actual arrow as one generating edge of the underlying graph. -/
def arrowGenerators (A : BundledAlgebra.{w}) : A.Obj ⥤q (forget.obj A).Objects where
  obj a := a
  map {a b} f := ⟨⟨a, b, f⟩, rfl, rfl⟩

def graphVertical {A B : BundledAlgebra.{w}} (F : forget.obj A ⟶ forget.obj B) : A.Obj ⥤q B.Obj :=
  A.arrowGenerators ⋙q (Graph.skeleton F).vertical

theorem graphVertical_pack {A B : BundledAlgebra.{w}} (F : forget.obj A ⟶ forget.obj B)
    {a b : A.Obj} (f : a ⟶ b) :
    (⟨Graph.mapObject F a, Graph.mapObject F b, (graphVertical F).map f⟩ : FinPath.Edge B.Obj) =
      Graph.mapVertical F ⟨a, b, f⟩ :=
  Graph.skeleton_vertical F (A.arrowGenerators.map f)

theorem evaluation_generator (A : BundledAlgebra.{w}) {a b : A.Obj} (f : a ⟶ b) :
    (evaluation A).base.vertical.map ((Paths.of (forget.obj A).Objects).map (A.arrowGenerators.map f)) = f := by
  change (Graph.skeleton (𝟙 (forget.obj A))).baseMap.vertical.map _ = f
  erw [Graph.SkeletonAssignment.baseMap_generator]
  rfl

theorem graphVertical_evaluation {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F)
    {a b : (forget.obj A).freeObject.Obj} (p : a ⟶ b) :
    (graphVertical F).map ((evaluation A).base.vertical.map p) =
      (Graph.lift F).base.vertical.map p := by
  have h := congrArg (fun f : forget.obj ((forget.obj A).freeObject) ⟶ forget.obj B =>
    Graph.mapVertical f ⟨a, b, p⟩) hF
  have hp := graphVertical_pack F ((evaluation A).base.vertical.map p)
  have he := hp.trans h.symm
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2

/-- Evaluation compatibility forces preservation of vertical identities and composition. -/
def comparisonVertical {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) : A.Obj ⥤ B.Obj where
  obj := (graphVertical F).obj
  map := (graphVertical F).map
  map_id a := by
    have h := graphVertical_evaluation F hF
      (@CategoryStruct.id _ (forget.obj A).freeObject.vertical.toCategoryStruct a)
    erw [(evaluation A).base.vertical.map_id, (Graph.lift F).base.vertical.map_id] at h
    exact h
  map_comp {a b c} f g := by
    let p := (Paths.of _).map (A.arrowGenerators.map f)
    let q := (Paths.of _).map (A.arrowGenerators.map g)
    have h := graphVertical_evaluation F hF (p ≫ q)
    erw [(evaluation A).base.vertical.map_comp, (Graph.lift F).base.vertical.map_comp] at h
    have hf := graphVertical_evaluation F hF p
    have hg := graphVertical_evaluation F hF q
    change (graphVertical F).map ((evaluation A).base.vertical.map p ≫
      (evaluation A).base.vertical.map q) = _ at h
    dsimp [p, q] at h hf hg
    erw [evaluation_generator, evaluation_generator] at h
    erw [evaluation_generator] at hf hg
    exact h.trans (congrArg₂ (fun f g => f ≫ g) hf.symm hg.symm)

def graphHorizontal {A B : BundledAlgebra.{w}} (F : forget.obj A ⟶ forget.obj B)
    {a b : A.Obj} (j : A.horizontal a b) : B.horizontal (Graph.mapObject F a) (Graph.mapObject F b) :=
  (Graph.skeleton F).horizontal ⟨⟨a, b, j⟩, rfl, rfl⟩

theorem graphHorizontal_pack {A B : BundledAlgebra.{w}} (F : forget.obj A ⟶ forget.obj B)
    {a b : A.Obj} (j : A.horizontal a b) :
    (⟨Graph.mapObject F a, Graph.mapObject F b, graphHorizontal F j⟩ :
      FinPath.Edge (Horizontal B.horizontal)) = Graph.mapHorizontal F ⟨a, b, j⟩ :=
  Graph.skeleton_horizontal F ⟨⟨a, b, j⟩, rfl, rfl⟩

def comparisonBase {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) :
    BaseMap A.horizontal B.horizontal where
  vertical := comparisonVertical F hF
  horizontal := graphHorizontal F

theorem lift_base_factorization {A B : BundledAlgebra.{w}}
    (F : forget.obj A ⟶ forget.obj B) (hF : EvaluationCompatible F) :
    (Graph.lift F).base = (evaluation A).base.comp (comparisonBase F hF) := by
  apply BaseMap.ext_edges
  · rfl
  · funext x
    rcases x with ⟨a, b, p⟩
    exact congrArg (fun f : @Quiver.Hom B.Obj B.vertical.toQuiver
        (Graph.mapObject F a) (Graph.mapObject F b) =>
      (⟨Graph.mapObject F a, Graph.mapObject F b, f⟩ : FinPath.Edge B.Obj))
      (graphVertical_evaluation F hF p).symm
  · funext x
    rcases x with ⟨a, b, j⟩
    have he := Graph.skeleton_horizontal (𝟙 (forget.obj A)) j
    exact (Graph.skeleton_horizontal F j).trans
      ((congrArg (Graph.mapHorizontal F) he).symm.trans
        (graphHorizontal_pack F ((evaluation A).base.horizontal j)).symm)

end Kernel.Augmented.BundledAlgebra

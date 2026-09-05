import Kernel.Augmented.GeneratingPresheaves
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.KanExtension.Dense

/-! Generating graph morphisms, their presheaf equivalence, and elementary density.
The elementary representables are a dense generator of the base presheaf category;
this alone does not make them arities for the augmented free construction.
Cites: D-KR-15, D-KR-18, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating
universe w

/-- A generating graph map is exactly a family of maps natural in every incidence. -/
instance : Category Graph.{w} where
  Hom G H := G.toPresheaf ⟶ H.toPresheaf
  id G := 𝟙 G.toPresheaf
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

def Graph.presheafFunctor : Graph.{w} ⥤ Presheaf.{w} where
  obj := Graph.toPresheaf
  map f := f

instance : Graph.presheafFunctor.{w}.Full where
  map_surjective f := ⟨f, rfl⟩

instance : Graph.presheafFunctor.{w}.Faithful where
  map_injective h := h

instance : Graph.presheafFunctor.{w}.EssSurj where
  mem_essImage P := ⟨Graph.ofPresheaf P, ⟨eqToIso (Graph.to_ofPresheaf P)⟩⟩

instance : Graph.presheafFunctor.{w}.IsEquivalence where

/-- The equivalence now includes morphisms and composition. -/
noncomputable def Graph.presheafEquivalence : Graph.{w} ≌ Presheaf.{w} :=
  Graph.presheafFunctor.asEquivalence

/-- Elementary incidence generators, lifted to the chosen presheaf universe. -/
abbrev elementary : Shape ⥤ Presheaf.{w} := uliftYoneda.{w}

/-- Every generating presheaf is the canonical colimit of its elementary generators. -/
noncomputable def elementaryDensity (P : Presheaf.{w}) : elementary.DenseAt P :=
  elementary.denseAt P

end Kernel.Augmented.Generating

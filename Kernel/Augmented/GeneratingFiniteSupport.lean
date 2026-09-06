import Kernel.Augmented.GeneratingFiniteIncidence
import Kernel.Augmented.GeneratingCategory
import Mathlib.CategoryTheory.Subfunctor.Finite
import Mathlib.Data.Finite.Sigma

/-! Finite sets of generators close to finite incidence subpresheaves.
Cites: D-KR-15, D-KR-18, AT-FD-7.

Finiteness counts all objects, vertical and horizontal edges, and all cell sorts.
It does not assert that the generating monad preserves filtered colimits.
-/

open CategoryTheory Opposite
noncomputable section
namespace Kernel.Augmented.Generating
universe w

/-- All generators of a presheaf, tagged with their elementary incidence sort. -/
abbrev Element (P : Presheaf.{w}) := Σ U, P.obj U

instance finite_ofSection_elements (P : Presheaf.{w}) {U : Shapeᵒᵖ} (x : P.obj U) :
    Finite (Element (Subfunctor.ofSection x).toFunctor) := by
  let f : (Σ V, Hom V U.unop) → Element (Subfunctor.ofSection x).toFunctor :=
    fun a => ⟨op a.1, ⟨P.map a.2.op x, ⟨a.2.op, rfl⟩⟩⟩
  apply Finite.of_surjective f
  rintro ⟨⟨V⟩, ⟨y, g, rfl⟩⟩
  exact ⟨⟨V, g.unop⟩, rfl⟩

/-- In this incidence category, finitely generated subpresheaves have finite total incidence. -/
instance finite_subfunctor_elements (P : Presheaf.{w}) (S : Subfunctor P) [S.IsFinite] :
    Finite (Element S.toFunctor) := by
  let x := Subfunctor.IsFinite.x (G := S)
  have h := Subfunctor.isGeneratedBy_of_isFinite S
  have (j : Subfunctor.IsFinite.Index S) : Finite (Element (Subfunctor.ofSection (x j)).toFunctor) :=
    finite_ofSection_elements P (x j)
  let f : (Σ j : Subfunctor.IsFinite.Index S, Element (Subfunctor.ofSection (x j)).toFunctor) →
      Element S.toFunctor := fun a =>
    ⟨a.2.1, ⟨a.2.2.val, (h.ofSection_le a.1) _ a.2.2.property⟩⟩
  apply Finite.of_surjective f
  rintro ⟨U, ⟨y, hy⟩⟩
  rw [← h.iSup_eq, Subfunctor.iSup_obj, Set.mem_iUnion] at hy
  obtain ⟨j, hj⟩ := hy
  exact ⟨⟨j, U, y, hj⟩, rfl⟩

/-- Close a finite set of generators under every incidence map. -/
def finiteSupport (P : Presheaf.{w}) (s : Finset (Element P)) : Subfunctor P :=
  ⨆ x : s, Subfunctor.ofSection x.val.2

theorem finiteSupport_isGeneratedBy (P : Presheaf.{w}) (s : Finset (Element P)) :
    (finiteSupport P s).IsGeneratedBy (fun x : s => x.val.2) := rfl

instance (P : Presheaf.{w}) (s : Finset (Element P)) : (finiteSupport P s).IsFinite :=
  (finiteSupport_isGeneratedBy P s).isFinite

theorem mem_finiteSupport (P : Presheaf.{w}) (s : Finset (Element P))
    {U : Shapeᵒᵖ} (x : P.obj U) (hx : (⟨U, x⟩ : Element P) ∈ s) :
    x ∈ (finiteSupport P s).obj U :=
  (finiteSupport_isGeneratedBy P s).mem ⟨⟨U, x⟩, hx⟩

theorem finiteSupport_mono (P : Presheaf.{w}) {s t : Finset (Element P)} (h : s ≤ t) :
    finiteSupport P s ≤ finiteSupport P t := by
  apply iSup_le
  intro x
  exact le_iSup_of_le (⟨x.val, h x.property⟩ : t) le_rfl

/-- For this base, finite generation is equivalent to having finite total incidence. -/
theorem presheafIsFinite_iff_finite_elements (P : Presheaf.{w}) :
    PresheafIsFinite P ↔ Finite (Element P) := by
  constructor
  · intro h
    have := h
    let f : Element (⊤ : Subfunctor P).toFunctor → Element P := fun x => ⟨x.1, x.2.val⟩
    exact Finite.of_surjective f (fun x => ⟨⟨x.1, x.2, Set.mem_univ _⟩, rfl⟩)
  · intro h
    have := h
    have hg : PresheafIsGeneratedBy P (fun x : Element P => x.2) := by
      apply Subfunctor.ext
      funext U
      apply Set.ext
      intro x
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj,
        Set.top_eq_univ, Set.mem_univ, iff_true]
      exact ⟨⟨U, x⟩, Subfunctor.mem_ofSection_obj x⟩
    exact hg.isFinite

/-- Maps from finite incidence data have finite images, with every incidence retained. -/
theorem finite_range_elements {P Q : Presheaf.{w}} [Finite (Element P)] (f : P ⟶ Q) :
    Finite (Element (Subfunctor.range f).toFunctor) := by
  have : PresheafIsFinite P := (presheafIsFinite_iff_finite_elements P).mpr inferInstance
  have := Subfunctor.range_isFinite P f
  infer_instance

end Kernel.Augmented.Generating

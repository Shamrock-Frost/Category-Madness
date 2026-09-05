import Kernel.Augmented.GeneratingPresheaves

/-! From global generating presheaves to the dependent incident-cell representation.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating
universe w

namespace Graph

def Objects (G : Graph.{w}) := G.Object

instance quiver (G : Graph.{w}) : Quiver G.Objects where
  Hom a b := {e : G.Vertical // G.verticalEndpoint false e = a ∧ G.verticalEndpoint true e = b}

def horizontal (G : Graph.{w}) (a b : G.Objects) : Type w :=
  {e : G.Horizontal // G.horizontalEndpoint false e = a ∧ G.horizontalEndpoint true e = b}

def side (G : Graph.{w}) {n ε} (x : G.Cell n ε) (s : Bool) : Side G.Objects where
  source := G.cellVertex (Generating.verticalEndpoint n ε s false) x
  target := G.cellVertex (Generating.verticalEndpoint n ε s true) x
  arrow := ⟨G.cellVertical s x, G.vertical_incidence s false x, G.vertical_incidence s true x⟩

def inputObjects (G : Graph.{w}) {n ε} (x : G.Cell n ε) (i : Fin (n + 1)) : Kernel.Augmented.Horizontal G.horizontal :=
  G.cellVertex (.inl i) x

def inputEdge (G : Graph.{w}) {n ε} (x : G.Cell n ε) (i : Fin n) :
    inputObjects G x i.castSucc ⟶ inputObjects G x i.succ :=
  ⟨G.cellHorizontal (.inl i) x, G.horizontal_incidence (.inl i) false x,
    G.horizontal_incidence (.inl i) true x⟩

end Graph

namespace FinPath
variable {C : Type w} [Quiver C]

def ofEdges : (n : ℕ) → (o : Fin (n + 1) → C) →
    ((i : Fin n) → (o i.castSucc ⟶ o i.succ)) → Quiver.Path (o 0) (o (Fin.last n))
  | 0, _, _ => .nil
  | n + 1, o, e => (ofEdges n (fun i => o i.castSucc) (fun i => e i.castSucc)).cons (e (Fin.last n))

theorem length_ofEdges (n : ℕ) (o : Fin (n + 1) → C)
    (e : (i : Fin n) → (o i.castSucc ⟶ o i.succ)) : (ofEdges n o e).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih _ _)

end FinPath
namespace Graph

def inputPath (G : Graph.{w}) {n ε} (x : G.Cell n ε) :
    HPath G.horizontal (G.side x false).source (G.side x true).source :=
  FinPath.ofEdges n (G.inputObjects x) (G.inputEdge x)

def outputObjects (G : Graph.{w}) {n ε} (x : G.Cell n ε) (i : Fin (ε.toNat + 1)) : Kernel.Augmented.Horizontal G.horizontal :=
  G.cellVertex (.inr i) x

def outputEdge (G : Graph.{w}) {n ε} (x : G.Cell n ε) (i : Fin ε.toNat) :
    outputObjects G x i.castSucc ⟶ outputObjects G x i.succ :=
  ⟨G.cellHorizontal (.inr i) x, G.horizontal_incidence (.inr i) false x,
    G.horizontal_incidence (.inr i) true x⟩

def outputPath (G : Graph.{w}) {n ε} (x : G.Cell n ε) :
    ShortPath G.horizontal (G.side x false).target (G.side x true).target :=
  ⟨FinPath.ofEdges ε.toNat (G.outputObjects x) (G.outputEdge x), by
    erw [FinPath.length_ofEdges]
    cases ε <;> decide⟩

def boundary (G : Graph.{w}) {n ε} (x : G.Cell n ε) :
    Boundary G.horizontal (G.side x false) (G.side x true) := ⟨G.inputPath x, G.outputPath x⟩

/-- A cell generator at its full boundary, with all objects and edges retained. -/
def cellGraph (G : Graph.{w}) : CellGraph G.Objects G.horizontal where
  Cell b := {x : Σ n : ℕ, Σ ε : Bool, G.Cell n ε // (G.boundary x.2.2).frame = b.frame}

def generator (G : Graph.{w}) {n ε} (x : G.Cell n ε) : (G.cellGraph).Cell (G.boundary x) :=
  ⟨⟨n, ε, x⟩, rfl⟩

theorem boundary_arity (G : Graph.{w}) {n ε} (x : G.Cell n ε) : (G.boundary x).arity = (n, ε.toNat) := by
  apply Prod.ext <;> exact FinPath.length_ofEdges _ _ _

end Graph
end Kernel.Augmented.Generating

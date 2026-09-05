import Kernel.Augmented.GeneratingCells
import Kernel.Augmented.FreeCellUniversal
import Mathlib.CategoryTheory.PathCategory.Basic

/-! Freely adjoining vertical paths and then augmented cells to a generating graph.
The global mapping property is proved in FreeGeneratingUniversal using change of base.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented.Generating.Graph
universe w
variable (G : Graph.{w})

def freeHorizontal (a b : Paths G.Objects) : Type w := G.horizontal a b

def freeSide {n ε} (x : G.Cell n ε) (s : Bool) : Side (Paths G.Objects) where
  source := (G.side x s).source
  target := (G.side x s).target
  arrow := (Paths.of G.Objects).map (G.side x s).arrow

def freeBoundary {n ε} (x : G.Cell n ε) :
    Boundary G.freeHorizontal (G.freeSide x false) (G.freeSide x true) :=
  ⟨(G.boundary x).input, (G.boundary x).output⟩

def freeCellGenerators : CellGraph (Paths G.Objects) G.freeHorizontal where
  Cell b := {x : Σ n : ℕ, Σ ε : Bool, G.Cell n ε // (G.freeBoundary x.2.2).frame = b.frame}

noncomputable def freeAlgebra : Algebra (CellTerm.quotientGraph G.freeCellGenerators) :=
  CellTerm.freeAlgebra G.freeCellGenerators

def freeCell {n ε} (x : G.Cell n ε) :
    (CellTerm.quotientGraph G.freeCellGenerators).Cell (G.freeBoundary x) :=
  (CellTerm.freeGenerators G.freeCellGenerators).cell ⟨⟨n, ε, x⟩, rfl⟩

theorem freeBoundary_arity {n ε} (x : G.Cell n ε) : (G.freeBoundary x).arity = (n, ε.toNat) :=
  G.boundary_arity x

end Kernel.Augmented.Generating.Graph

import Kernel.Foundations.Signatures
import Interface.CategorySpec

/-! Universe contracts for the root and its later constructions.
These records assert sizes, not the existence of the augmented arity category,
a walking nerve, a derived relative mapping space, or the Mod construction.
Cites: D-RT-16, D-RT-23, D-RT-24, D-RT-27, AT-FD-1.
-/

open CategoryTheory Kernel.Foundations

namespace Root.Foundations
universe l s u v

/-- Proposition-valued root conditions do not increase the presheaf universe.
Their mathematical definition belongs to the later shape/model gates. -/
structure RootSignature (S : ShapeSignature)
    (conditions : (X : Type l) → Diagram.{l,s} S X → Prop) where
  Label : Type l
  diagram : Diagram.{l,s} S Label
  satisfies : conditions Label diagram

structure WalkingSignature (S : ShapeSignature) (X : Type l) where
  boundary : Diagram.{l,s} S X
  total : Diagram.{l,s} S X
  inclusion : boundary ⟶ total

/-- Strict relative choices; this is not a derived mapping-space definition. -/
abbrev RelativeChoice {S : ShapeSignature} {X : Type l}
    (W : WalkingSignature.{l,s} S X) (P : Diagram.{l,s} S X)
    (b : W.boundary ⟶ P) : Type (max l s) :=
  { f : W.total ⟶ P // W.inclusion ≫ f = b }

/-- Input family of full walking monad nerves in the fixed label fibre. -/
abbrev MonadNerves (S : ShapeSignature) (X : Type l) : Type (max l (s + 1)) :=
  X → Diagram.{l,s} S X

/-- Universe of all labels equipped with a map out of their walking monad nerve. -/
abbrev MonadCollection {S : ShapeSignature} {X : Type l}
    (W : MonadNerves.{l,s} S X) (P : Diagram.{l,s} S X) : Type (max l s) :=
  Σ x : X, W x ⟶ P

set_option linter.checkUnivs false in
/-- Mapping-space simplices range over diagram maps, hence max l s. -/
abbrev RelativeMappingSpace : Type (max l s + 1) := SSet.{max l s}

/-- The output carrier for coherent Mod; this does not construct its value maps. -/
abbrev ModSignature {S : ShapeSignature} {X : Type l}
    (W : MonadNerves.{l,s} S X) (P : Diagram.{l,s} S X) :
    Type (max (l + 1) (s + 1)) :=
  Diagram.{max l s,max l s} S (MonadCollection W P)

abbrev CategoryOn (A : Type u) : Type (max u (v + 1)) :=
  Interface.Category.{u,v} A

-- The independent levels remain visible in the bundled category's fields.
set_option linter.checkUnivs false in
abbrev CategoryCollection : Type (max (u + 1) (v + 1)) :=
  Interface.CategorySpec.{u,v}

end Root.Foundations

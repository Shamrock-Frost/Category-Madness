import Kernel.Augmented.OperationSignature

/-! Freely generated cell terms before imposing the augmented algebra equations.
The vertical category and horizontal graph are parameters of this construction.
Cites: D-KR-15, D-KR-18, D-TL-21, AT-FD-7.
-/

open CategoryTheory
namespace Kernel.Augmented
universe u v h c c' c''
variable {C : Type u} [Category.{v} C] {H : C → C → Type h}

inductive CellTerm (G : CellGraph.{u,v,h,c} C H) : CellBoundary C H → Type (max u v h c)
  | generator {b : CellBoundary C H} (φ : G.family b) : CellTerm G b
  | operation (o : CellOperation C H) (children : (p : o.Position) → CellTerm G (o.input p)) :
      CellTerm G o.output

namespace CellTerm
variable {G : CellGraph.{u,v,h,c} C H} {K : CellGraph.{u,v,h,c'} C H}
  {J : CellGraph.{u,v,h,c''} C H}

def graph (G : CellGraph.{u,v,h,c} C H) : CellGraph C H where
  Cell b := CellTerm G b.frame

def generators (G : CellGraph.{u,v,h,c} C H) : CellGraph.Map G (graph G) :=
  ⟨fun {_ _} {b} φ => generator (G := G) (b := b.frame) φ⟩

def evaluate (O : Operations K) (F : CellGraph.Map G K) :
    {b : CellBoundary C H} → CellTerm G b → K.family b
  | _, .generator φ => F.cell φ
  | _, .operation o children => o.interpret O (fun p => evaluate O F (children p))

def evaluation (O : Operations K) (F : CellGraph.Map G K) : CellGraph.Map (graph G) K :=
  ⟨evaluate O F⟩

def bind (F : CellGraph.Map G (graph K)) : {b : CellBoundary C H} → CellTerm G b → CellTerm K b
  | _, .generator φ => F.cell φ
  | _, .operation o children => .operation o (fun p => bind F (children p))

def bindMap (F : CellGraph.Map G (graph K)) : CellGraph.Map (graph G) (graph K) := ⟨bind F⟩

@[simp] theorem bind_generators {b : CellBoundary C H} (t : CellTerm G b) : bind (generators G) t = t := by
  induction t with
  | generator φ => rfl
  | operation o children ih => exact congrArg (operation o) (funext ih)

theorem bind_bind (F : CellGraph.Map G (graph K)) (F' : CellGraph.Map K (graph J))
    {b : CellBoundary C H} (t : CellTerm G b) :
    bind F' (bind F t) = bind (F.comp (bindMap F')) t := by
  induction t with
  | generator φ => rfl
  | operation o children ih => exact congrArg (operation o) (funext ih)

theorem evaluate_bind (O : Operations J) (F : CellGraph.Map G (graph K)) (F' : CellGraph.Map K J)
    {b : CellBoundary C H} (t : CellTerm G b) :
    evaluate O F' (bind F t) = evaluate O (F.comp (evaluation O F')) t := by
  induction t with
  | generator φ => rfl
  | operation o children ih => exact congrArg (o.interpret O) (funext ih)

/-- Any interpretation preserving generators and operation nodes is the recursive evaluation. -/
theorem evaluate_unique (O : Operations K) (F : CellGraph.Map G K)
    (e : {b : CellBoundary C H} → CellTerm G b → K.family b)
    (hg : ∀ {b : CellBoundary C H} (φ : G.family b), e (.generator φ) = F.cell φ)
    (ho : ∀ (o : CellOperation C H) (x : (p : o.Position) → CellTerm G (o.input p)),
      e (.operation o x) = o.interpret O (fun p => e (x p)))
    {b : CellBoundary C H} (t : CellTerm G b) : e t = evaluate O F t := by
  induction t with
  | generator φ => exact hg φ
  | operation o children ih => exact (ho o children).trans (congrArg (o.interpret O) (funext ih))

def substitutionNode (s : SubstitutionShape C H) (x : s.Inputs (graph G)) : (graph G).Cell s.result :=
  .operation (.substitution s)
    (Sum.rec (fun p => RowShape.atPosition s.row x.1 p) (fun _ => x.2))

theorem substitutionNode_transport {s t : SubstitutionShape C H} (e : s = t)
    (x : s.Inputs (graph G)) :
    CellGraph.transport (congrArg (fun s => s.result.frame) e) (substitutionNode s x) =
      substitutionNode t (SubstitutionShape.Inputs.transport e x) := by
  cases e
  rfl

/-- The incident operations on raw terms; no algebra equations have been imposed yet. -/
def operations (G : CellGraph.{u,v,h,c} C H) : Operations (graph G) where
  horizontalIdentity j := .operation (.horizontalIdentity j) (fun p => PEmpty.elim p)
  verticalIdentity f := .operation (.verticalIdentity ⟨_, _, f⟩) (fun p => PEmpty.elim p)
  substitute := by
    intro f g r a b h k L ψ
    let s := SubstitutionShape.ofRow r h k L
    let x := SubstitutionShape.rowInputs r h k L ψ
    exact CellGraph.castInput (G := graph G) (f := f.post h) (g := g.post k) (L := L)
      (CellGraph.Row.shape_input r.val)
      (substitutionNode s x)

end CellTerm
end Kernel.Augmented

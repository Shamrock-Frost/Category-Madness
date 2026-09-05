import Lean
import Foundations
import Augmented
import Theory.Category

/-! Minimal environment exporter and scoped foundation axiom audit.
Cites: D-KR-14, D-KR-18, D-CH-20, D-WF-08, D-WF-10, AT-KR-0, AT-FD-1, AT-FD-7.
-/

open Lean Elab Command

namespace FoundationExport

def approvedAxioms : Array Name :=
  #["propext", "Classical.choice", "Quot.sound"].map String.toName

def foundationName (n : Name) : Bool :=
  ["Kernel.Foundations.", "Root.Foundations.", "Kernel.Augmented.", "Prototype.Universes."].any
    (fun p => n.toString.startsWith p)

def namesJson (ns : List Name) : Json :=
  toJson ((ns.toArray.qsort Name.lt).map Name.toString)

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def declaration (n : Name) : CommandElabM Json := do
  let env ← getEnv
  let some ci := env.find? n | throwError "INVENTORY_MISSING: {n}"
  let axs ← collectAxioms n
  let approved := axs.all approvedAxioms.contains
  let status := if !approved then "stated" else
    match ci with | .thmInfo _ => "proved" | _ => "checked"
  let pretty ← liftTermElabM do
    Meta.ppExpr ci.type
  let moduleName := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  let pos ← findDeclarationRanges? n
  let posJson := match pos with
    | none => Json.null
    | some p => Json.mkObj [
      ("line", toJson p.range.pos.line), ("column", toJson p.range.pos.column),
      ("endLine", toJson p.range.endPos.line), ("endColumn", toJson p.range.endPos.column)]
  let valueDeps := (ci.value? (allowOpaque := true)).map (·.getUsedConstants.toList) |>.getD []
  return Json.mkObj [
    ("name", toJson n.toString), ("kind", toJson (kind ci)),
    ("universeParameters", toJson (ci.levelParams.map Name.toString)),
    ("type", toJson pretty.pretty), ("typeExpression", toJson (reprStr ci.type)),
    ("docstring", toJson (← findDocString? env n)),
    ("module", toJson (moduleName.map Name.toString)), ("position", posJson),
    ("statementDependencies", namesJson ci.type.getUsedConstants.toList),
    ("proofDependencies", namesJson valueDeps),
    ("axioms", namesJson axs.toList), ("approvedAxioms", toJson approved),
    ("status", toJson status)]

def writeDeclarations (names : Array Name) (path : System.FilePath) : CommandElabM Unit := do
  let rows ← (names.qsort Name.lt).mapM declaration
  liftIO <| IO.FS.writeFile path ((Json.arr rows).pretty ++ "\n")

end FoundationExport

set_option pp.universes true
set_option pp.fullNames true

run_cmd do
  let dependencies := (#[
    "CategoryTheory.Category", "CategoryTheory.Functor", "CategoryTheory.NatTrans",
    "CategoryTheory.Cat", "CategoryTheory.Cat.of",
    "CategoryTheory.Functor.Elements", "CategoryTheory.categoryOfElements",
    "CategoryTheory.NatTrans.mapElements", "CategoryTheory.groupoidOfElements",
    "SSet", "CategoryTheory.nerve", "CategoryTheory.nerveMap",
    "CategoryTheory.Nerve.strictSegal", "SSet.IsStrictSegal",
    "CategoryTheory.nerveAdjunction", "CategoryTheory.nerveFunctor.fullyfaithful",
    "CategoryTheory.nerveFunctorCompHoFunctorIso", "CategoryTheory.Codiscrete.equivFun",
    "CategoryTheory.SingleObj.groupoid", "CategoryTheory.SingleObj.toEnd",
    "SSet.modelCategoryQuillen.I", "SSet.modelCategoryQuillen.J",
    "SSet.modelCategoryQuillen.cofibration_iff", "SSet.modelCategoryQuillen.fibration_iff",
    "SSet.rlp_monomorphisms", "SSet.KanComplex", "SSet.KanComplex.hornFilling",
    "SSet.anodyneExtensions", "SSet.anodyneExtensions_pushoutObjObjι",
    "SSet.fibration_pullbackObjObjπ", "CategoryTheory.ihom",
    "CategoryTheory.MonoidalClosed.internalHom", "SSet.RelativeMorphism",
    "SSet.RelativeMorphism.HomotopyClass",
    "HomotopicalAlgebra.CategoryWithWeakEquivalences",
    "HomotopicalAlgebra.WeakEquivalence", "HomotopicalAlgebra.ModelCategory",
    "HomotopicalAlgebra.PathObject", "HomotopicalAlgebra.ReedyStructure",
    "HomotopicalAlgebra.ReedyStructure.op",
    "HomotopicalAlgebra.ReedyStructure.mapFactorizationData",
    "Quiver.Path", "Quiver.Path.comp", "Quiver.Path.comp_assoc",
    "Quiver.Path.length_comp", "Quiver.Path.eq_of_length_zero",
    "SimplexCategory.Hom.toOrderHom",
    "CategoryTheory.Bicategory", "CategoryTheory.Bicategory.Strict",
    "CategoryTheory.Bicategory.whisker_exchange",
    "CategoryTheory.Bicategory.Strict.associator_eqToIso",
    "CategoryTheory.conj_eqToHom_iff_heq",
    "AddCommMonoid", "add_assoc", "add_add_add_comm"] : Array String).map String.toName
  let project := (← getEnv).constants.toList.filterMap fun (n, _) =>
    if FoundationExport.foundationName n then some n else none
  for n in project do
    for ax in (← collectAxioms n) do
      unless FoundationExport.approvedAxioms.contains ax do
        throwError "FOUNDATION_AXIOM_REJECTED: {n} uses {ax}"
  let some path ← IO.getEnv "CATEGORY_MADNESS_INVENTORY_OUT" |
    throwError "Set CATEGORY_MADNESS_INVENTORY_OUT to the output JSON path"
  FoundationExport.writeDeclarations (dependencies ++ project.toArray) path
  logInfo m!"FOUNDATIONS_AUDIT_OK {project.length} project declarations; {dependencies.size} dependency entries"

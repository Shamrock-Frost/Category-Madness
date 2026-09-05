import Lean

/-! Compiled dependency and axiom checks (D-TL-17, AT-FD-2, AT-FD-11).
Axiom checks cross the seal; client dependency checks stop at audited Interface laws. -/
set_option autoImplicit false

open Lean Elab Command

namespace Prototype.Audit

def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.header.mainModule

def forbidden (env : Environment) (name : Name) : Bool :=
  let mod := moduleOf env name
  #[`Kernel, `Root, `Mathlib.CategoryTheory, `Mathlib.AlgebraicTopology].any fun p =>
    p.isPrefixOf mod || p.isPrefixOf (privateToUserName name)

-- Generated recursors can be cyclic; inspect each dependency once.
partial def checkDependencies (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : Except String Unit := do
  match pending with
  | [] => pure ()
  | name :: rest =>
    if seen.contains name then return ← checkDependencies env rest seen
    if forbidden env name then throw s!"SEAL_LEAK: forbidden dependency {name}"
    let seen := seen.insert name
    let some info := env.find? name
      | throw s!"SEAL_MISSING: dependency {name} has no declaration"
    if (`Interface).isPrefixOf name then return ← checkDependencies env rest seen
    checkDependencies env (info.getUsedConstantsAsSet.toList ++ rest) seen

partial def checkSignature (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : Except String Unit := do
  match pending with
  | [] => pure ()
  | name :: rest =>
    if seen.contains name then return ← checkSignature env rest seen
    if forbidden env name then throw s!"SEAL_SIGNATURE: forbidden dependency {name}"
    let seen := seen.insert name
    let some info := env.find? name
      | throw s!"SEAL_MISSING: signature dependency {name} has no declaration"
    -- Inspect transparent aliases, while keeping opaque packages and theorem proofs sealed.
    let deps := info.type.getUsedConstants.toList ++
      (info.value?.map (fun v => v.getUsedConstants.toList)).getD []
    checkSignature env (deps ++ rest) seen

def auditAxioms (name : Name) (stub : Bool) : CommandElabM (Array Name) := do
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax ||
        (stub && ax == `Interface.Prototype.monoid) do
      throwError "SEAL_AXIOM: {name} depends on unapproved axiom {ax}"
  pure axioms

elab "#audit_seal " mode:str : command => do
  let stub := mode.getString == "stub"
  unless stub || mode.getString == "implementation" do
    throwError "audit mode must be implementation or stub"
  let env := (← getEnv).setExporting false
  let names := env.constants.toList.map Prod.fst |>.filter fun n =>
    let mod := moduleOf env n
    (`Interface).isPrefixOf mod || (`Theory).isPrefixOf mod || mod == `Prototype.Universes
  let names := names.toArray.qsort Name.lt
  unless names.contains `Theory.Prototype.product_append do
    throwError "SEAL_EMPTY: the nontrivial client was not imported"
  let mut declarations : Array Json := #[]
  for name in names do
    let some info := env.find? name | throwError "missing audited declaration {name}"
    let axioms ← auditAxioms name stub
    if (`Interface).isPrefixOf (moduleOf env name) then
      if let .error err := checkSignature env info.type.getUsedConstants.toList then
        throwError "{name}: {err}"
    if (`Theory).isPrefixOf (moduleOf env name) then
      if let .error err := checkDependencies env info.getUsedConstantsAsSet.toList then
        throwError "{name}: {err}"
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("type", toJson (reprStr info.type)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toArray.map Name.toString))]
  let report := Json.mkObj [("mode", toJson mode.getString),
    ("declarations", toJson declarations)]
  let some output ← IO.getEnv "SEAL_AUDIT_OUTPUT"
    | throwError "SEAL_AUDIT_OUTPUT is required to preserve the audit report"
  IO.FS.writeFile output report.pretty
  logInfo m!"seal audit: {names.size} declarations checked ({mode.getString})"

-- Negative fixtures exercise the same checks as the full audit.
elab "#audit_axioms " decl:ident : command => do
  discard <| auditAxioms decl.getId false

elab "#audit_client " decl:ident : command => do
  let env := (← getEnv).setExporting false
  let some info := env.find? decl.getId | throwError "unknown fixture {decl.getId}"
  if let .error err := checkDependencies env info.getUsedConstantsAsSet.toList then
    throwError "{err}"

end Prototype.Audit

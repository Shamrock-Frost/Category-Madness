import Lean
import Interface
import Theory

/-! Scoped compiled-signature, client-dependency and axiom audit.
Cites: D-TL-17, D-RT-28, AT-FD-2, AT-FD-11. -/
open Lean Elab Command

private def projectName (n : Name) : Bool :=
  ["Interface.", "Theory.", "Kernel.Matrix.", "Root.MatrixCategory."].any (fun p => n.toString.startsWith p)

private def implementationName (n : Name) : Bool :=
  ["Kernel.", "Root."].any (fun p => n.toString.startsWith p) ||
    (n.toString.startsWith "_private." &&
      ["Kernel", "Root"].any (n.toString.splitOn ".").contains)

private partial def checkBoundary (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : CommandElabM Unit := do
  match todo with
  | [] => pure ()
  | n :: rest =>
    if seen.contains n then return ← checkBoundary env rest seen
    if implementationName n then throwError "SEAL_LEAK: {n}"
    let seen := seen.insert n
    match env.find? n with
    | none => throwError "SEAL_MISSING: {n}"
    | some ci =>
      let mut deps := ci.type.getUsedConstants.toList
      -- Public interface theorems and opaque inhabitants form the trusted boundary.
      -- Transparent aliases/projections must still be followed.
      let publicLaw := n.toString.startsWith "Interface." &&
        (match ci with | .thmInfo _ | .opaqueInfo _ => true | _ => false)
      if !publicLaw then
        if let some value := ci.value? (allowOpaque := true) then
          deps := value.getUsedConstants.toList ++ deps
      checkBoundary env (deps ++ rest) seen

run_cmd do
  let env ← getEnv
  let stub := (← IO.getEnv "CATEGORY_MADNESS_STUB") == some "1"
  let allowed := if stub then
      #[``propext, ``Quot.sound, ``Classical.choice, ``Interface.functionCategory]
    else #[``propext, ``Quot.sound, ``Classical.choice]
  let constants := env.constants.toList.filter (fun p => projectName p.1)
  let constants := constants.toArray.qsort (fun a b => Name.lt a.1 b.1)
  for (n, ci) in constants do
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do throwError "AXIOM_REJECTED: {n} uses {ax}"
    if n.toString.startsWith "Interface." then
      checkBoundary env ci.type.getUsedConstants.toList
      let signature := Json.arr #[toJson n.toString, toJson (reprStr ci.levelParams),
        toJson (reprStr ci.type)]
      logInfo ("SIGNATURE " ++ signature.compress)
    if n.toString.startsWith "Theory." then
      checkBoundary env [n]
  let axs ← collectAxioms ``Theory.function_inverse_unique
  if stub && !axs.contains ``Interface.functionCategory then
    throwError "STUB_NOT_USED: client did not depend on the stub package"
  logInfo m!"AUDIT_OK {constants.size} declarations; client axioms: {axs}"

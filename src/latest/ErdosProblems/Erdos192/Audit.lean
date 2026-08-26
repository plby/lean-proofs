import ErdosProblems.Erdos192
import Lean.Util.CollectAxioms

open Lean

#print axioms Erdos192.erdos_192
#print axioms Erdos192.erdos_problem_192_classification
#print axioms Erdos192.exists_avoiding_walk
#print axioms Erdos192.masksCertificate_true
#print axioms Erdos192.pairsCheck_true

namespace Erdos192.Audit

/-- Traverse actual types and proof bodies, independently of the axiom cache. -/
partial def closure (env : Lean.Environment) (todo : List Lean.Name)
    (seen : Lean.NameSet := {}) : Lean.NameSet := Id.run do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return closure env rest seen
    let seen := seen.insert n
    let some ci := env.find? n | return closure env rest seen
    let deps := ci.type.getUsedConstants
    let deps := match ci.value? (allowOpaque := true) with
      | some v => deps ++ v.getUsedConstants
      | none => deps
    return closure env (deps.toList ++ rest) seen

end Erdos192.Audit

run_cmd do
  let opts ← Lean.getOptions
  unless Lean.maxHeartbeats.get opts == Lean.maxHeartbeats.defValue &&
      Lean.maxRecDepth.get opts == Lean.maxRecDepth.defValue &&
      Lean.Meta.maxSynthPendingDepth.get opts == Lean.Meta.maxSynthPendingDepth.defValue do
    throwError "resource options differ from the stock defaults"
  logInfo m!"Stock options: maxHeartbeats={Lean.maxHeartbeats.get opts}, maxRecDepth={Lean.maxRecDepth.get opts}, maxSynthPendingDepth={Lean.Meta.maxSynthPendingDepth.get opts}"
  let env := (← Lean.getEnv).setExporting false
  let names := (Erdos192.Audit.closure env
    [`Erdos192.erdos_192, `Erdos192.erdos_problem_192_classification,
      `Erdos192.exists_avoiding_walk]).toArray.qsort Lean.Name.lt
  let mut axioms : Array Lean.Name := #[]
  let mut taskNames : Array Lean.Name := #[]
  for n in names do
    let some ci := env.find? n | throwError "missing declaration: {n}"
    if ci.isAxiom then
      axioms := axioms.push n
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "forbidden axiom in transitive closure: {n}"
    let s := n.toString
    if s == "sorryAx" || s.contains "ofReduceBool" || s.contains "trustCompiler" ||
        s.contains "native_decide" || s.contains "nativeDecide" then
      throwError "forbidden compiler/native mechanism: {n}"
    if let some idx := env.getModuleIdxFor? n then
      if "ErdosProblems.Erdos192".isPrefixOf env.header.moduleNames[idx.toNat]!.toString then
        taskNames := taskNames.push n
        if ci.isAxiom then
          throwError "axiom or opaque assumption in a task module: {n}"
        if let .opaqueInfo _ := ci then
          throwError "opaque assumption in a task module: {n}"
  logInfo m!"Raw proof closure: {names.size} constants; {taskNames.size} task constants; axioms={axioms}"
  let lines := names.toList.map Lean.Name.toString
  IO.FS.writeFile ".lake/erdos192-proof-dependencies.txt" (String.intercalate "\n" lines)

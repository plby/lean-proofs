import ErdosProblems.Erdos1058

/- Fail the build if the final theorem acquires an axiom outside Comparator's
existing policy, including any compiled-evaluation or sorry axiom. -/
open Lean in
run_cmd do
  let axioms ← collectAxioms ``Erdos1058.erdos_1058
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom in Erdos1058: {axiomName}"

#print axioms Erdos1058.erdos_1058

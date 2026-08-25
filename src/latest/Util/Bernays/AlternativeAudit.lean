import ErdosProblems.Erdos659b

/-!
The alternative proof must remain usable without importing either Bernays'
theorem or the primary Erdős 659 theorem. Shared geometry is allowed.
-/

run_cmd do
  let env ← Lean.getEnv
  for name in [`bernays, `Bernays.bernays_theorem, `Erdos659.erdos_659] do
    if env.contains name then
      throwError "The alternative proof unexpectedly imports {name}"

/-- info: 'Erdos659b.erdos_659' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos659b.erdos_659

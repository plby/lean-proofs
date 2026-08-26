import Mathlib

/-!
# Kernel-checked closed decisions

`native_decide` is deliberately not used in the final proof: it introduces
the compiler-trust axioms `Lean.ofReduceBool` and `Lean.trustCompiler`.

`kernel_decide` first uses Lean's kernel decision procedure.  The original
full-transparency reflexivity proof remains as a fallback.  All branches
use kernel reduction, so the resulting declaration contains no
native-evaluator trust axiom.
-/

set_option warningAsError false

/-- Discharge a closed decidable proposition by proof-producing kernel
reduction, without `Lean.ofReduceBool` or `Lean.trustCompiler`. -/
macro "kernel_decide" : tactic =>
  `(tactic| first | decide +kernel | rfl' | exact of_decide_eq_true (by rfl'))

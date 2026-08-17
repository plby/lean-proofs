/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos847.FinitePipeline
import ErdosProblems.Erdos847.FinalAssembly

/-!
# The constructed counterexample for Erdős 847

This module joins the finite RRS block theorem to the separated-block
assembly.  The resulting set has hereditary one-third 3-AP-free subsets and
is Ramsey for a three-term arithmetic progression under every finite
coloring.
-/

namespace Erdos847Construction

/-- The complete RRS counterexample, with the convenient constant `1/3`. -/
theorem exists_counterexample :
    ∃ A : Set ℕ, A.Infinite ∧
      Erdos847Assembly.IsRRSCounterexample A (1 / 3 : ℝ) := by
  apply Erdos847FinalAssembly.exists_infinite_counterexample_of_good_blocks
  intro r hr
  obtain ⟨X, hne, hramsey, hdense⟩ :=
    Erdos847FinitePipeline.exists_finite_rrs_block r hr
  exact ⟨X, hne, hramsey, hdense⟩

end Erdos847Construction

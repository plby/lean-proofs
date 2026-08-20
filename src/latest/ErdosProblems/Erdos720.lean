import ErdosProblems.Erdos720.Asymptotic

open Filter Topology
open scoped SimpleGraph

noncomputable section

namespace Erdos720

open SimpleGraph

/-!
# Erdős Problem 720

This file exposes the completed formal resolution.  The imported development
defines the size-Ramsey number from first principles, proves explicit eventual
linear bounds for paths and cycles, and derives the three asymptotic answers:
the proposed divergence for paths is false, while both quadratic ratios tend
to zero.
-/

/-- Formal resolution of Erdős Problem 720, together with the stronger
eventual linear bounds supplied by the sparse no-hole constructions. -/
theorem erdos_problem_720 :
    (¬ Tendsto (fun n : ℕ ↦
      (sizeRamsey (pathGraph (n + 1)) : ℝ) / n) atTop atTop) ∧
    Tendsto (fun n : ℕ ↦
      (sizeRamsey (pathGraph (n + 1)) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0) ∧
    Tendsto (fun n : ℕ ↦ (sizeRamsey (cycleGraph n) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0) ∧
    (∀ᶠ n : ℕ in atTop, sizeRamsey (pathGraph (n + 1)) ≤ 6272 * n) ∧
    (∀ᶠ n : ℕ in atTop,
      sizeRamsey (cycleGraph n) ≤ cycleRamseyEdgeConstant * n) := by
  exact ⟨path_sizeRamsey_ratio_not_tendsto_atTop,
    path_sizeRamsey_div_sq_tendsto_zero,
    cycle_sizeRamsey_div_sq_tendsto_zero,
    eventually_path_linear,
    eventually_cycle_linear⟩

end Erdos720

#print axioms Erdos720.erdos_problem_720

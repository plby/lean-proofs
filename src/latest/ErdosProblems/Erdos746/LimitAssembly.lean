import ErdosProblems.Erdos746.Monotonicity
import ErdosProblems.Erdos746.Parameters

/-!
# Final monotone limit assembly for Erdős 746

Once Hamiltonicity is known at the rounded threshold, monotonicity in the
exact fixed-edge model gives every eventually admissible larger edge count.
-/

open Filter

namespace Erdos746

/-- It is enough to prove Hamiltonicity with high probability at the least
integer edge count above the real threshold. -/
theorem erdos746Statement_of_threshold
    (hthreshold : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ hamiltonianProbability n (edgeThreshold ε n))
        atTop (nhds 1)) :
    Erdos746Statement := by
  intro ε hε m hlower hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hthreshold ε hε) tendsto_const_nhds
  · filter_upwards [hlower, hupper] with n hnLower hnUpper
    exact hamiltonianProbability_mono
      (edgeThreshold_le_of_real_le hnLower) hnUpper
  · exact Filter.Eventually.of_forall fun n ↦
      hamiltonianProbability_le_one n (m n)

end Erdos746

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform eighth moments on a short logarithmic interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.IntervalMoments
import ErdosProblems.Erdos521.RefinedGridEndpoints
import ErdosProblems.Erdos521.LogGridScale
import ErdosProblems.Erdos521.BulkStability

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem eventually_logInterval_eighth_moment (n : ℕ → ℕ) (s : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hs : Tendsto s atTop atTop) {C a ℓ : ℝ}
    (hC : localMomentBulkConstant 8 ≤ C) (ha : 0 < a) (hwidth : Real.exp ℓ - 1 ≤ 1 / 8)
    (hbulk : ∀ᶠ j : ℕ in atTop, logGrid (s j) a ℓ 1 ≤ endpointCenter C (n j)) :
    ∀ᶠ j : ℕ in atTop, (∫ ε,
      (intervalRootCount ε (n j) (logGrid (s j) a ℓ 0) (logGrid (s j) a ℓ 1) : ℝ) ^ 8 ∂sequenceLaw) ≤
        localMomentBoundConstant 8 := by
  filter_upwards [hn.eventually (eventually_bulk_interval_moments 8), hbulk,
    hn.eventually_ge_atTop 1, eventually_logGrid_point_bounds s hs ha ℓ 1,
    (logGrid_point_tendsto s hs a ℓ 1).eventually (lt_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1))]
    with j hjmom hjbulk hjn hjbounds hjlo
  apply hjmom _ _
  · exact ⟨hjlo.le, hjbulk.trans (endpointCenter_antitone_constant hC hjn)⟩
  · exact short_logGrid_width hwidth hjbounds.2.le

end Erdos521

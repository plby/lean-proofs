/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An almost-sure reversed-count subsequence yields the required total-root limsup.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ReversalConvergence
import ErdosProblems.Erdos521.RootSubsequenceBounds

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem ae_normalizedRootCount_limsup :
    ∀ᵐ ε ∂sequenceLaw,
      (2 / Real.pi : ℝ) ≤ limsup (fun n ↦ (normalizedRootCount ε n : EReal)) atTop := by
  obtain ⟨u, hu, hreverse⟩ := exists_reversedInteriorRootCount_subsequence_limit
  filter_upwards [ae_interiorRootCount_div_log_limit, hreverse, ae_sequence_signs]
    with ε hinter hrev hsign
  have hf := reversalLowerStatistic_subsequence_limit ε u hu.tendsto_atTop hinter hrev
  apply le_limsup_of_subsequence_lower_bound (normalizedRootCount ε)
    (fun j ↦ reversalLowerStatistic ε (u j)) u hu.tendsto_atTop (2 / Real.pi) hf
  filter_upwards [hu.tendsto_atTop.eventually (eventually_ge_atTop 2)] with j hj
  have hε₀ : ε 0 ≠ 0 := by rcases hsign 0 with h | h <;> simp [h]
  have hεn : ε (u j) ≠ 0 := by rcases hsign (u j) with h | h <;> simp [h]
  exact reversalLowerStatistic_le ε hj hε₀ hεn

end Erdos521

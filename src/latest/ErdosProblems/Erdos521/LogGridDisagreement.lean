/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The limiting discrepancy probability between roots and a fixed logarithmic grid.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGridProbabilities
import ErdosProblems.Erdos521.SimpleRootProbability
import ErdosProblems.Erdos521.SignGridProbability

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators Topology

theorem logGrid_disagreement_probability :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ → ℕ) (s : ℕ → ℝ),
      Tendsto n atTop atTop → Tendsto s atTop atTop →
      Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop →
      ∀ a δ : ℝ, 0 < a → 0 < δ → ∀ N : ℕ,
      (∀ᶠ j : ℕ in atTop, logGrid (s j) a δ N ≤ endpointCenter C (n j)) →
      ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
        sequenceLaw.real {ε | intervalRootCount ε (n j) (logGrid (s j) a δ 0) (logGrid (s j) a δ N) ≠
          gridSignChanges ε (n j) (logGrid (s j) a δ) N} ≤
            (N : ℝ) * ((normalizedSmallBallConstant + 96) * (Real.exp δ - 1) ^ (4 / 3 : ℝ)) + η := by
  obtain ⟨C, hC, hrep⟩ := simpleRoot_bulk_probability
  refine ⟨C, hC, ?_⟩
  intro n s hn hs hN a δ ha hδ N hbulk η hη
  have he : 0 < η / 3 := by linarith
  have hzero := logGrid_zero_probability_sum_tendsto_zero n s hn hs ha δ N
  have hinv : Tendsto (fun j ↦ (n j : ℝ) ^ (-1 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hn)
  filter_upwards [hn.eventually hrep, hbulk, hs.eventually_gt_atTop 0,
    (logGrid_point_tendsto s hs a δ 0).eventually (lt_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1)),
    hzero.eventually (gt_mem_nhds he), hinv.eventually (gt_mem_nhds he),
    eventually_logGrid_two_root_probability n s hn hs hN ha hδ N he]
    with j hjrep hjbulk hsj hjlo hjzero hjinv hjtwo
  have hr := hjrep (logGrid (s j) a δ 0) (logGrid (s j) a δ N) hjlo.le hjbulk
  have h := rootCount_signGrid_probability (n j) N (logGrid (s j) a δ)
    (logGrid_mono hsj ha.le hδ.le) (δ := 0) (τ := 0) le_rfl le_rfl
  nlinarith

end Erdos521

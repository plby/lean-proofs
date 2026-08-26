import ErdosProblems.Erdos421.ThetaLogSaving

/-! # A uniform prime-weight lower bound in logarithmically long reference intervals -/

namespace Erdos421

open Filter Topology

theorem theta_long_interval_lower_bound {B : ℝ} (hB : 0 ≤ B) :
    ∃ X₀ > 1, ∀ X u v : ℝ, X₀ ≤ X → X ≤ u → u ≤ v → v ≤ 2 * X →
      X / (Real.log X) ^ B ≤ v - u → (v - u) / 2 ≤ Chebyshev.theta v - Chebyshev.theta u := by
  have hA : 0 ≤ B + 1 := by linarith
  obtain ⟨X₁, _, htheta⟩ := chebyshev_theta_log_saving hA (by norm_num : (0 : ℝ) < 1)
  have hlarge : ∀ᶠ X : ℝ in atTop, ∀ u v : ℝ, X ≤ u → u ≤ v → v ≤ 2 * X →
      X / (Real.log X) ^ B ≤ v - u → (v - u) / 2 ≤ Chebyshev.theta v - Chebyshev.theta u := by
    filter_upwards [eventually_ge_atTop (max X₁ 2),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 8)] with X hX hlog
    have hXX : X₁ ≤ X := (le_max_left _ _).trans hX
    have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
    have hXp : 0 < X := by linarith
    have hL : 0 < Real.log X := by linarith
    have hLB : 0 < (Real.log X) ^ B := Real.rpow_pos_of_pos hL B
    have hLA : 0 < (Real.log X) ^ (B + 1) := Real.rpow_pos_of_pos hL (B + 1)
    let Q : ℝ := 2 * X / (Real.log X) ^ (B + 1)
    have herror : ∀ z : ℝ, X ≤ z → z ≤ 2 * X → |Chebyshev.theta z - z| ≤ Q := by
      intro z hXz hzX
      have hzp : 0 < z := hXp.trans_le hXz
      have hlogz := Real.log_le_log hXp hXz
      have hb := htheta z (hXX.trans hXz)
      simp only [one_mul] at hb
      calc
        _ ≤ z / (Real.log z) ^ (B + 1) := hb
        _ ≤ z / (Real.log X) ^ (B + 1) :=
          div_le_div_of_nonneg_left hzp.le hLA (Real.rpow_le_rpow hL.le hlogz hA)
        _ ≤ Q := div_le_div_of_nonneg_right hzX hLA.le
    intro u v hXu huv hvX hlen
    have hu := herror u hXu (huv.trans hvX)
    have hv := herror v (hXu.trans huv) hvX
    have hfrac : 4 / Real.log X ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith)
    have hQ : 2 * Q ≤ (v - u) / 2 := by
      calc
        _ = (4 / Real.log X) * (X / (Real.log X) ^ B) := by
          dsimp only [Q]
          rw [Real.rpow_add hL, Real.rpow_one]
          ring
        _ ≤ (1 / 2) * (X / (Real.log X) ^ B) :=
          mul_le_mul_of_nonneg_right hfrac (div_nonneg hXp.le hLB.le)
        _ ≤ (1 / 2) * (v - u) := mul_le_mul_of_nonneg_left hlen (by norm_num)
        _ = _ := by ring
    linarith [(abs_le.mp hu).2, (abs_le.mp hv).1]
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro X u v hX hXu huv hvX hlen
  exact hX₀ X ((le_max_left X₀ 2).trans hX) u v hXu huv hvX hlen

end Erdos421

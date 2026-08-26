import ErdosProblems.Erdos747.UpperLimit

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

lemma upperEdgeCount_mono (epsilon delta : ℝ) (h : epsilon ≤ delta) (n : ℕ) :
    upperEdgeCount epsilon n ≤ upperEdgeCount delta n := by
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl h) (shamirScale_nonneg n)

lemma upperEdgeCount_div_cube_tendsto_zero (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    Tendsto (fun n ↦ (upperEdgeCount epsilon n : ℝ) / (n : ℝ)^3) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)^3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hbound := (tendsto_log_three_mul_div_sq.const_mul (1 + epsilon)).add hinv
  norm_num only [mul_zero, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ hbound
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hceil := (upperEdgeCount_cast_lt epsilon (by linarith only [hepsilon]) n).le
  calc
    _ ≤ ((1 + epsilon) * shamirScale n + 1) / (n : ℝ)^3 :=
      div_le_div_of_nonneg_right hceil (by positivity)
    _ = _ := by
      unfold shamirScale
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      field_simp

lemma eventually_upperEdgeCount_le_card (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ∀ᶠ n in atTop, upperEdgeCount epsilon n ≤ (allEdges n).card := by
  have hsmall := (tendsto_order.mp (upperEdgeCount_div_cube_tendsto_zero epsilon hepsilon)).2
    1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hsmalln hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlt : (upperEdgeCount epsilon n : ℝ) < (n : ℝ)^3 := (div_lt_one (by positivity)).mp hsmalln
  have hbound : (upperEdgeCount epsilon n : ℝ) ≤ (allEdges n).card := by
    rw [card_allEdges]
    exact hlt.le.trans (cube_le_choose_three_mul n hn)
  exact_mod_cast hbound

lemma upper_pmProbability_tendsto_one (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun n ↦ pmProbability n (upperEdgeCount epsilon n)) atTop (𝓝 1) := by
  by_cases hepsilon1 : epsilon ≤ 1
  · exact upper_pmProbability_tendsto_one_of_le_one epsilon hepsilon hepsilon1
  · have hbase := upper_pmProbability_tendsto_one_of_le_one 1 (by norm_num) le_rfl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbase tendsto_const_nhds
    · filter_upwards [eventually_upperEdgeCount_le_card epsilon hepsilon.le] with n hn
      exact pmProbability_mono_of_le (upperEdgeCount_mono 1 epsilon (by linarith only [hepsilon1]) n) hn
    · exact Eventually.of_forall fun n ↦ pmProbability_le_one n (upperEdgeCount epsilon n)

theorem shamir_threshold_resolution : ShamirThresholdResolution :=
  ⟨fun epsilon h0 h1 ↦ lower_pmProbability_tendsto_zero epsilon h0 h1,
    fun epsilon h0 ↦ upper_pmProbability_tendsto_one epsilon h0⟩

end

end Erdos747

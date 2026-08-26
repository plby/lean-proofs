import ErdosProblems.Erdos747.ThresholdResolution

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

lemma shamirScale_pos (n : ℕ) (hn : 1 ≤ n) : 0 < shamirScale n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (3 * (n : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  exact mul_pos hnR hlog

lemma shamirScale_tendsto_atTop : Tendsto shamirScale atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [log_vertexCount_tendsto_atTop.eventually_ge_atTop (max R 1), eventually_ge_atTop 1]
    with n hlog hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogR : R ≤ Real.log ((3 * n : ℕ) : ℝ) := (le_max_left _ _).trans hlog
  have hlog0 : 0 ≤ Real.log ((3 * n : ℕ) : ℝ) := by linarith only [hlog, le_max_right R 1]
  have h := mul_le_mul_of_nonneg_right hnR hlog0
  unfold shamirScale
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, one_mul] at hlogR h
  exact hlogR.trans h

lemma lowerEdgeCount_le_upper_zero (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (n : ℕ) :
    lowerEdgeCount epsilon n ≤ upperEdgeCount 0 n := by
  have hlo := lowerEdgeCount_cast_le epsilon hepsilon1 n
  have hs := shamirScale_nonneg n
  have hup := shamirScale_le_upperEdgeCount 0 (by norm_num) n
  have hcast : (lowerEdgeCount epsilon n : ℝ) ≤ upperEdgeCount 0 n := by
    nlinarith only [hlo, hup, mul_nonneg hepsilon0 hs]
  exact_mod_cast hcast

lemma eventually_critical_scale_bounds (epsilon : ℝ) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∀ᶠ n in atTop,
      (1 - epsilon) * shamirScale n < critical n ∧
      (critical n : ℝ) < (1 + epsilon) * shamirScale n + 1 := by
  have hlo := (tendsto_order.mp (lower_pmProbability_tendsto_zero epsilon hepsilon0 hepsilon1)).2
    (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hup := (tendsto_order.mp (upper_pmProbability_tendsto_one epsilon hepsilon0)).1
    (1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [hlo, hup, eventually_upperEdgeCount_le_card 0 (by norm_num)] with n hlon hupn hvalid
  have hlowvalid : lowerEdgeCount epsilon n ≤ (allEdges n).card :=
    (lowerEdgeCount_le_upper_zero epsilon hepsilon0.le hepsilon1.le n).trans hvalid
  have hcritlow : lowerEdgeCount epsilon n < critical n := by
    by_contra hbad
    exact (not_le_of_gt hlon) (half_le_probability_of_critical_le (by omega) hlowvalid)
  have hcritup : critical n ≤ upperEdgeCount epsilon n := critical_min hupn.le
  constructor
  · have hfloor : (1 - epsilon) * shamirScale n < (lowerEdgeCount epsilon n : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hR : (lowerEdgeCount epsilon n : ℝ) + 1 ≤ critical n := by exact_mod_cast hcritlow
    exact hfloor.trans_le hR
  · have hR : (critical n : ℝ) ≤ upperEdgeCount epsilon n := by exact_mod_cast hcritup
    exact hR.trans_lt (upperEdgeCount_cast_lt epsilon (by linarith only [hepsilon0]) n)

lemma critical_div_shamirScale_tendsto_one :
    Tendsto (fun n ↦ (critical n : ℝ) / shamirScale n) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    let epsilon := min ((1 - x) / 2) (1 / 2)
    have he0 : 0 < epsilon := lt_min (by linarith only [hx]) (by norm_num)
    have he1 : epsilon < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hxeps : x < 1 - epsilon := by
      have he := min_le_left ((1 - x) / 2) (1 / 2)
      change epsilon ≤ (1 - x) / 2 at he
      linarith only [hx, he]
    filter_upwards [eventually_critical_scale_bounds epsilon he0 he1, eventually_ge_atTop 1]
      with n hn hnpos
    have hs := shamirScale_pos n hnpos
    exact hxeps.trans ((lt_div_iff₀ hs).mpr hn.1)
  · intro x hx
    let epsilon := min ((x - 1) / 4) (1 / 2)
    have he0 : 0 < epsilon := lt_min (by linarith only [hx]) (by norm_num)
    have he1 : epsilon < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have he : epsilon ≤ (x - 1) / 4 := min_le_left _ _
    have hinv : Tendsto (fun n ↦ (1 : ℝ) / shamirScale n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop shamirScale_tendsto_atTop
    have hsmall := (tendsto_order.mp hinv).2 epsilon he0
    filter_upwards [eventually_critical_scale_bounds epsilon he0 he1, hsmall, eventually_ge_atTop 1]
      with n hn hinvn hnpos
    have hs := shamirScale_pos n hnpos
    have hquot := (div_lt_div_iff_of_pos_right hs).mpr hn.2
    have heq : ((1 + epsilon) * shamirScale n + 1) / shamirScale n = 1 + epsilon + 1 / shamirScale n := by
      field_simp
    rw [heq] at hquot
    linarith only [hquot, hinvn, he, hx]

lemma log_three_mul_div_log_tendsto_one :
    Tendsto (fun n : ℕ ↦ Real.log ((3 * n : ℕ) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hsmall : Tendsto (fun n : ℕ ↦ Real.log 3 / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlim : Tendsto (fun n : ℕ ↦ Real.log 3 / Real.log (n : ℝ) + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using hsmall.add_const 1
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnR.ne']
  field_simp

theorem critical_div_n_log_n_tendsto_one :
    Tendsto (fun n ↦ (critical n : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hlim := critical_div_shamirScale_tendsto_one.mul log_three_mul_div_log_tendsto_one
  norm_num only [one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog3 : Real.log ((3 * n : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))).ne'
  unfold shamirScale
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlog3 ⊢
  have hlog3' : Real.log ((n : ℝ) * 3) ≠ 0 := by simpa only [mul_comm] using hlog3
  field_simp [hlog3, hlog3']

end

end Erdos747

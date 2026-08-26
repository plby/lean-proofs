import ErdosProblems.Erdos856b.UpperBound

/-! # Matching bounds and the limiting exponent -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

theorem tendsto_exp_reciprocal_slope {a : ℝ} (ha : 0 < a) :
    Tendsto (fun z : ℝ => z * (exp (a / z) - 1)) atTop (𝓝 a) := by
  have harg : Tendsto (fun z : ℝ => a / z) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact div_pos ha hz
  have h := ((hasDerivAt_exp 0).tendsto_slope_zero_right.comp harg).const_mul a
  simp only [zero_add, exp_zero, smul_eq_mul, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  dsimp [Function.comp_def]
  field_simp

theorem sunflowerPressure_sub_le {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    sunflowerPressure k z - z ≤ z * (exp (gamma k / z) - 1) := by
  have hP := logPressure_le_gamma_mul hk (one_div_pos.mpr hz)
  rw [mul_one_div] at hP
  have h := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hP) hz.le
  dsimp [sunflowerPressure, cosPressure]
  linarith

theorem upper_bound_gamma {k : ℕ} (hk : 3 ≤ k) {b : ℝ} (hb : gamma k < b) :
    ∀ᶠ N : ℕ in atTop, exponentRatio k N < b := by
  have hlarge := (tendsto_exp_reciprocal_slope (gamma_pos hk)).eventually (gt_mem_nhds hb)
  obtain ⟨z, hz, hbound⟩ := ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  exact weighted_upper_bound hk hz ((sunflowerPressure_sub_le hk hz).trans_lt hbound)

/-- The full logarithmic asymptotic, with the exponent defined by finite uniform families. -/
theorem tendsto_exponentRatio {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (exponentRatio k) atTop (𝓝 (gamma k)) :=
  tendsto_order.mpr ⟨fun _ hb => lower_bound_gamma hk hb, fun _ hb => upper_bound_gamma hk hb⟩

theorem eventually_upper_bound {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, f k N ≤ (log (N : ℝ)) ^ (gamma k + ε) := by
  filter_upwards [upper_bound_gamma hk (by linarith : gamma k < gamma k + ε),
    tendsto_logScale.eventually_gt_atTop 0, eventually_gt_atTop (1 : ℕ)] with N hN hL hN1
  have hfpos : 0 < f k N := zero_lt_one.trans_le (one_le_f hk (by omega))
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
  have hlog := (div_lt_iff₀ hL).mp hN
  rw [rpow_def_of_pos hlogN, ← exp_log hfpos]
  apply exp_le_exp.mpr
  exact le_of_lt (by simpa [logScale, mul_comm] using hlog)

/-- Both matching weighted bounds, for every positive error. -/
theorem eventually_matching_bounds {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (log (N : ℝ)) ^ (gamma k - ε) ≤ f k N ∧
        f k N ≤ (log (N : ℝ)) ^ (gamma k + ε) :=
  (eventually_lower_bound hk hε).and (eventually_upper_bound hk hε)

theorem gamma_le_sunflowerPressure_sub {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    gamma k ≤ sunflowerPressure k z - z := by
  by_contra h
  obtain ⟨b, hb, hbg⟩ := exists_between (lt_of_not_ge h)
  obtain ⟨N, hNlo, hNhi⟩ := ((lower_bound_gamma hk hbg).and
    (weighted_upper_bound hk hz hb)).exists
  exact (lt_asymm hNlo hNhi)

theorem tendsto_sunflowerPressure_sub {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun z : ℝ => sunflowerPressure k z - z) atTop (𝓝 (gamma k)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_exp_reciprocal_slope (gamma_pos hk))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact gamma_le_sunflowerPressure_sub hk hz
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact sunflowerPressure_sub_le hk hz

theorem gamma_eq_inf_sunflowerPressure_sub {k : ℕ} (hk : 3 ≤ k) :
    gamma k = sInf {v : ℝ | ∃ z : ℝ, 0 < z ∧ v = sunflowerPressure k z - z} := by
  let S : Set ℝ := {v | ∃ z : ℝ, 0 < z ∧ v = sunflowerPressure k z - z}
  have hSne : S.Nonempty := ⟨sunflowerPressure k 1 - 1, 1, by norm_num, rfl⟩
  have hSbdd : BddBelow S := by
    refine ⟨gamma k, ?_⟩
    rintro v ⟨z, hz, rfl⟩
    exact gamma_le_sunflowerPressure_sub hk hz
  apply le_antisymm
  · apply le_csInf hSne
    rintro v ⟨z, hz, rfl⟩
    exact gamma_le_sunflowerPressure_sub hk hz
  · apply ge_of_tendsto (tendsto_sunflowerPressure_sub hk)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact csInf_le hSbdd ⟨z, hz, rfl⟩

theorem gamma_eq_sup_log_cosPressure_div {k : ℕ} (hk : 3 ≤ k) :
    gamma k = sSup {v : ℝ | ∃ z : ℝ, 0 < z ∧ v = log (cosPressure k z) / z} := by
  simpa only [cosPressure, log_exp] using gamma_eq_sup_logPressure_div hk

end Erdos856b

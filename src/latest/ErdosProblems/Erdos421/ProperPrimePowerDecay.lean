import ErdosProblems.Erdos421.ProperPrimePowers
import ErdosProblems.Erdos421.UnsmoothingParameters

/-! # Proper prime powers give an error smaller than every logarithmic scale -/

namespace Erdos421

open Filter Topology

theorem properPrimePowers_dyadic_majorant {M : ℕ} (hM : 2 ≤ M)
    (hlog : 1 ≤ Real.log M) :
    ((properPrimePowers (2 * M)).card : ℝ) / M ≤
      (3 * (2 / Real.log 2 + 1)) * Real.log M / (M : ℝ) ^ (1 / 2 : ℝ) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMp
  have hsqrt1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM1
  have hroot : Real.sqrt (2 * M : ℕ) + 1 ≤ 3 * Real.sqrt M := by
    have hsq : Real.sqrt ((2 * M : ℕ) : ℝ) ≤ 2 * Real.sqrt M := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      have he := Real.sq_sqrt hMp.le
      push_cast
      nlinarith
    linarith
  have hlogs : Real.log ((2 * M : ℕ) : ℝ) ≤ 2 * Real.log M := by
    have h := (unsmoothing_log_bounds (by exact_mod_cast hM) hMp.le le_rfl).2
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, two_mul] using h
  have hlogfactor : Real.log ((2 * M : ℕ) : ℝ) / Real.log 2 + 1 ≤
      (2 / Real.log 2 + 1) * Real.log M := by
    have hb := div_le_div_of_nonneg_right hlogs hlog2.le
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith
  have hc := properPrimePowers_card_real_bound (2 * M)
  have hfull := hc.trans (mul_le_mul hroot hlogfactor
    (by positivity) (by positivity))
  calc
    _ ≤ (3 * Real.sqrt M * ((2 / Real.log 2 + 1) * Real.log M)) / M :=
      div_le_div_of_nonneg_right hfull hMp.le
    _ = (3 * (2 / Real.log 2 + 1)) * Real.log M / Real.sqrt M := by
      have he := Real.sq_sqrt hMp.le
      field_simp
      nlinarith [he]
    _ = _ := by rw [Real.sqrt_eq_rpow]

theorem properPrimePowers_log_error_eventually (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      ((properPrimePowers (2 * M)).card : ℝ) / M ≤ ε / (Real.log M) ^ A := by
  let C : ℝ := 3 * (2 / Real.log 2 + 1)
  have hc : 0 < C := by dsimp only [C]; positivity
  have ht : Tendsto (fun x : ℝ ↦ C * ((Real.log x) ^ (A + 1) / x ^ (1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (A + 1)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [mul_zero] using
      h.const_mul C
  have hn := ht.comp tendsto_natCast_atTop_atTop
  have hlargeLog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log M :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [hn.eventually (gt_mem_nhds hε), eventually_ge_atTop (2 : ℕ), hlargeLog]
    with M hsmall hM hlog
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogp : 0 < Real.log M := by linarith
  have hp : 0 < (Real.log M) ^ A := Real.rpow_pos_of_pos hlogp _
  apply (properPrimePowers_dyadic_majorant hM hlog).trans
  apply (le_div_iff₀ hp).mpr
  have he : (C * Real.log M / (M : ℝ) ^ (1 / 2 : ℝ)) * (Real.log M) ^ A =
      C * ((Real.log M) ^ (A + 1) / (M : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [Real.rpow_add hlogp A 1, Real.rpow_one]
    ring
  change (C * Real.log M / (M : ℝ) ^ (1 / 2 : ℝ)) * (Real.log M) ^ A ≤ ε
  rw [he]
  exact hsmall.le

end Erdos421

import Mathlib

/-!
# Cutoff estimates for the Siegel lower bound
-/

open scoped BigOperators Topology

namespace Erdos1141

lemma tendsto_rpow_neg_mul_log (c ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun q : ℕ ↦ c * (q : ℝ) ^ (-ε) * Real.log (q : ℝ))
      Filter.atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop hε).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero.const_mul c
  convert h using 1
  · funext q
    simp only [Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg q), div_eq_mul_inv]
    ring
  · simp

lemma siegel_cutoff_error_le {q : ℕ} (hq : 16 ≤ q) {β : ℝ} (hβ : 3 / 4 ≤ β) :
    4 * (1 + 16 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
      ((q ^ 16 : ℕ) : ℝ) ^ (1 / 2 - β) ≤ 1 / 2 := by
  have hqr : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hsqrt : Real.sqrt (q : ℝ) ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hqone)
  have hlog : Real.log (q : ℝ) ≤ q := (Real.log_le_sub_one_of_pos hqpos).trans (by linarith)
  have hlog0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hscale : 1 + 16 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤ 17 * (q : ℝ) ^ 2 := by
    have hprod := mul_le_mul hsqrt hlog hlog0 hqpos.le
    nlinarith
  have hpower : ((q ^ 16 : ℕ) : ℝ) ^ (1 / 2 - β) ≤ (q : ℝ) ^ (-4 : ℝ) := by
    rw [Nat.cast_pow]
    calc
      _ ≤ ((q : ℝ) ^ 16) ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hqone) (by linarith)
      _ = _ := by rw [← Real.rpow_natCast_mul hqpos.le]; norm_num
  calc
    _ ≤ 4 * (17 * (q : ℝ) ^ 2) * (q : ℝ) ^ (-4 : ℝ) := by gcongr
    _ = 68 / (q : ℝ) ^ 2 := by
      rw [Real.rpow_neg hqpos.le]
      norm_num only [Real.rpow_ofNat]
      field_simp
      ring
    _ ≤ _ := by
      apply (div_le_iff₀ (sq_pos_of_pos hqpos)).mpr
      nlinarith

lemma siegel_cutoff_rpow_le_two {q : ℕ} (hq : 1 ≤ q) {δ : ℝ}
    (hsmall : δ * Real.log (q : ℝ) ≤ 1 / 128) :
    ((q ^ 16 : ℕ) : ℝ) ^ δ ≤ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog2 : (1 / 8 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  rw [Real.rpow_def_of_pos (by positivity), Nat.cast_pow, Real.log_pow]
  calc
    _ ≤ Real.exp (1 / 8) := Real.exp_le_exp.mpr (by norm_num; nlinarith)
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog2
    _ = _ := Real.exp_log (by norm_num)

lemma weighted_harmonic_cutoff_le {q : ℕ} (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ * Real.log (q : ℝ) ≤ 1 / 128) :
    (∑ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ) ^ (-(1 - δ))) ≤ 2 + 32 * Real.log (q : ℝ) := by
  have hpow := siegel_cutoff_rpow_le_two hq hsmall
  have hterm : ∀ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ) ^ (-(1 - δ)) ≤ 2 * (n : ℝ)⁻¹ := by
    intro n hn
    have hn1 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnx : (n : ℝ) ≤ ((q ^ 16 : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hnpow := (Real.rpow_le_rpow hn1.le hnx hδ).trans hpow
    rw [show -(1 - δ) = (-1 : ℝ) + δ by ring, Real.rpow_add hn1, Real.rpow_neg_one]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hnpow (inv_nonneg.mpr hn1.le)
  have hharmonic : (∑ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ)⁻¹) ≤
      1 + Real.log ((q ^ 16 : ℕ) : ℝ) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log (q ^ 16)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (q ^ 16), 2 * (n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = 2 * ∑ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (1 + Real.log ((q ^ 16 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hharmonic (by norm_num)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; norm_num; ring

lemma siegel_scaled_weighted_cutoff_le {q : ℕ} (hq : 1 ≤ q) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 16) (hsmall : δ * Real.log (q : ℝ) ≤ 1 / 128) :
    δ * (∑ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ) ^ (-(1 - δ))) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (weighted_harmonic_cutoff_le hq hδ hsmall) hδ
  nlinarith

end Erdos1141

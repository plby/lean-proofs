import ErdosProblems.Erdos421.MertensSieveIntervals
import ErdosProblems.Erdos421.RoundedTransferSupport
import ErdosProblems.Erdos421.BuchstabLogBounds

/-! # A reciprocal-prime bound below the positivity threshold for the actual cutoffs -/

namespace Erdos421

open Filter Topology

theorem eventually_outer_cutoff_sharp_bound :
    ∀ᶠ X : ℕ in atTop, (outerPrimeCutoff X : ℝ) ≤ (X : ℝ) ^ (501 / 1000 : ℝ) := by
  filter_upwards [eventually_constant_rpow_le 6
    (by norm_num : (1 / 2 : ℝ) < 501 / 1000), eventually_ge_atTop 1] with X hsave hX
  exact (outerPrimeCutoff_bounds (by exact_mod_cast hX)).2.1.trans hsave

theorem eventually_intermediate_cutoff_large (Y : ℝ) :
    ∀ᶠ X : ℕ in atTop, Y ≤ intermediatePrimeCutoff X ∧
      1 ≤ Real.log (intermediatePrimeCutoff X) := by
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 200)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (max Y (Real.exp 1))
  filter_upwards [hp, eventually_ge_atTop 1] with X hlarge hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hz := (roundedPowerCutoff_bounds hXr
    (by norm_num : (0 : ℝ) ≤ 39 / 200)).1
  have hmax : max Y (Real.exp 1) ≤ intermediatePrimeCutoff X := hlarge.trans hz
  have he : Real.exp 1 ≤ intermediatePrimeCutoff X := (le_max_right _ _).trans hmax
  have hlog := Real.log_le_log (Real.exp_pos 1) he
  rw [Real.log_exp] at hlog
  exact ⟨(le_max_left _ _).trans hmax, hlog⟩

theorem log_prime_cutoff_ratio_upper : Real.log (167 / 65 : ℝ) ≤ 119 / 125 := by
  have hsmall := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 501 / 500)
  have hlarge := log_hundred_over_thirty_nine_le
  have heq : (167 / 65 : ℝ) = (100 / 39) * (501 / 500) := by norm_num
  rw [heq, Real.log_mul (by norm_num : (100 / 39 : ℝ) ≠ 0)
    (by norm_num : (501 / 500 : ℝ) ≠ 0)]
  linarith

theorem eventually_prime_cutoff_log_ratio :
    ∀ᶠ X : ℕ in atTop,
      Real.log (outerPrimeCutoff X) ≤ 3 * Real.log (intermediatePrimeCutoff X) ∧
      Real.log (Real.log (outerPrimeCutoff X) / Real.log (intermediatePrimeCutoff X)) ≤
        119 / 125 := by
  filter_upwards [eventually_outer_cutoff_sharp_bound, eventually_ge_atTop 2] with X hQ hX
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hXp : (0 : ℝ) < X := by linarith
  have hLX := Real.log_pos hX1
  have hz := (roundedPowerCutoff_bounds hX1.le (by norm_num : (0 : ℝ) ≤ 39 / 200)).1
  have hZ1 : (1 : ℝ) < intermediatePrimeCutoff X :=
    (Real.one_lt_rpow hX1 (by norm_num : (0 : ℝ) < 39 / 200)).trans_le hz
  have hZp : (0 : ℝ) < intermediatePrimeCutoff X := by linarith
  have hZQ : (intermediatePrimeCutoff X : ℝ) ≤ outerPrimeCutoff X :=
    by exact_mod_cast intermediatePrimeCutoff_le_outer hX1.le
  have hQp : (0 : ℝ) < outerPrimeCutoff X := hZp.trans_le hZQ
  have hLZ := Real.log_pos hZ1
  have hLQ := Real.log_pos (hZ1.trans_le hZQ)
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hXp (39 / 200)) hz
  have hhi := Real.log_le_log hQp hQ
  rw [Real.log_rpow hXp] at hlo hhi
  change (39 / 200 : ℝ) * Real.log X ≤ Real.log (intermediatePrimeCutoff X) at hlo
  refine ⟨by nlinarith, ?_⟩
  have hratio : Real.log (outerPrimeCutoff X) / Real.log (intermediatePrimeCutoff X) ≤
      (167 / 65 : ℝ) := by
    calc
      _ ≤ ((501 / 1000 : ℝ) * Real.log X) / Real.log (intermediatePrimeCutoff X) :=
        div_le_div_of_nonneg_right hhi hLZ.le
      _ ≤ ((501 / 1000 : ℝ) * Real.log X) / ((39 / 200 : ℝ) * Real.log X) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
      _ = _ := by field_simp; norm_num
  exact (Real.log_le_log (div_pos hLQ hLZ) hratio).trans log_prime_cutoff_ratio_upper

theorem eventually_outer_prime_reciprocal_small :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X), (p : ℝ)⁻¹) ≤
        191 / 200 := by
  obtain ⟨X₀, hX₀, hmertens⟩ := mertens_sieve_interval (by norm_num : (0 : ℝ) < 1 / 1000)
  filter_upwards [eventually_prime_cutoff_log_ratio,
    eventually_intermediate_cutoff_large (max X₀ 1000), eventually_ge_atTop 1]
    with X hratio hlarge hX
  have hzX : X₀ ≤ intermediatePrimeCutoff X := (le_max_left _ _).trans hlarge.1
  have hz1000 : (1000 : ℝ) ≤ intermediatePrimeCutoff X := (le_max_right _ _).trans hlarge.1
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hzQ := intermediatePrimeCutoff_le_outer hXr
  have h := hmertens (intermediatePrimeCutoff X) (outerPrimeCutoff X) hzX hzQ hlarge.2 hratio.1
  have hinv : (intermediatePrimeCutoff X : ℝ)⁻¹ ≤ 1 / 1000 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hz1000
  linarith [hratio.2]

end Erdos421

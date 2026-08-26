import ErdosProblems.Erdos421.RoundedPrimeCutoffs

/-! # Support inequalities for the explicit cutoffs in the window transfer -/

namespace Erdos421

open Filter Topology

theorem eventually_small_cutoff_order {β : ℝ} (hβ : 0 < β) (hβ' : β < 39 / 200) :
    ∀ᶠ X : ℕ in atTop, smallPrimeCutoff X β ≤ intermediatePrimeCutoff X := by
  filter_upwards [eventually_constant_rpow_le 3 hβ', eventually_ge_atTop 1] with X hsave hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hw := (smallPrimeCutoff_bounds hXr hβ.le).2
  have hz := (roundedPowerCutoff_bounds hXr (by norm_num : (0 : ℝ) ≤ 39 / 200)).1
  exact_mod_cast hw.trans (hsave.trans hz)

theorem eventually_intermediate_cutoff_bound :
    ∀ᶠ X : ℕ in atTop, (intermediatePrimeCutoff X : ℝ) ≤ (X : ℝ) ^ (79 / 400 : ℝ) := by
  filter_upwards [eventually_constant_rpow_le 2 (by norm_num : (39 / 200 : ℝ) < 79 / 400),
    eventually_ge_atTop 1] with X hsave hX
  exact (roundedPowerCutoff_bounds (by exact_mod_cast hX)
    (by norm_num : (0 : ℝ) ≤ 39 / 200)).2.trans hsave

theorem eventually_outer_cutoff_bound :
    ∀ᶠ X : ℕ in atTop, (outerPrimeCutoff X : ℝ) ≤ (X : ℝ) ^ (51 / 100 : ℝ) := by
  filter_upwards [eventually_constant_rpow_le 6 (by norm_num : (1 / 2 : ℝ) < 51 / 100),
    eventually_ge_atTop 1] with X hsave hX
  exact (outerPrimeCutoff_bounds (by exact_mod_cast hX)).2.1.trans hsave

theorem eventually_convolved_sieve_support {β : ℝ} (hβ : 0 < β) (hβ' : β < 1 / 1000) :
    ∀ᶠ X : ℕ in atTop,
      ((outerPrimeCutoff X * (smallPrimeCutoff X β *
        (roundedPowerCutoff X (1 / 1000)) ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) := by
  have hexp : (1 / 2 : ℝ) + β + (1 / 1000) * 2 < 21 / 40 := by linarith
  filter_upwards [eventually_constant_rpow_le 72 hexp, eventually_ge_atTop 1] with X hsave hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  have hQ := (outerPrimeCutoff_bounds hXr).2.1
  have hW := (smallPrimeCutoff_bounds hXr hβ.le).2
  have hD := (roundedPowerCutoff_bounds hXr (by norm_num : (0 : ℝ) ≤ 1 / 1000)).2
  calc
    _ ≤ (6 * (X : ℝ) ^ (1 / 2 : ℝ)) *
        ((3 * (X : ℝ) ^ β) * (2 * (X : ℝ) ^ (1 / 1000 : ℝ)) ^ 2) := by
      push_cast
      gcongr
    _ = 72 * ((X : ℝ) ^ (1 / 2 : ℝ) *
        (X : ℝ) ^ β * ((X : ℝ) ^ (1 / 1000 : ℝ)) ^ 2) := by ring
    _ = 72 * (X : ℝ) ^ ((1 / 2 : ℝ) + β + (1 / 1000) * 2) := by
      rw [← Real.rpow_mul_natCast hXp.le, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
      norm_num
    _ ≤ _ := hsave

theorem eventually_intermediate_power_dominates :
    ∀ᶠ X : ℕ in atTop, 3 * X < (intermediatePrimeCutoff X) ^ 6 := by
  filter_upwards [eventually_constant_rpow_le 4 (by norm_num : (1 : ℝ) < 117 / 100),
    eventually_ge_atTop 1] with X hsave hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  have hz := (roundedPowerCutoff_bounds hXr (by norm_num : (0 : ℝ) ≤ 39 / 200)).1
  have hzpow := pow_le_pow_left₀
    (Real.rpow_nonneg hXp.le (39 / 200)) hz 6
  rw [← Real.rpow_mul_natCast hXp.le] at hzpow
  norm_num only [Nat.cast_ofNat] at hzpow
  norm_num only [Real.rpow_one] at hsave
  have hpow : (X : ℝ) ^ (117 / 100 : ℝ) ≤ (intermediatePrimeCutoff X : ℝ) ^ 6 := by
    simpa only [intermediatePrimeCutoff] using hzpow
  have hlt : (3 : ℝ) * X < (intermediatePrimeCutoff X : ℝ) ^ 6 := by linarith
  exact_mod_cast hlt

end Erdos421

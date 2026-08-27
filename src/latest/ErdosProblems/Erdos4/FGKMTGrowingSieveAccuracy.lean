import ErdosProblems.Erdos4.FGKMTGrowingAccuracyBudget
import ErdosProblems.Erdos4.FGKMTGrowingParameters

/-! Uniform initial-sieve accuracy for the actual growing dimension and moving prime family. -/

namespace Erdos4.FGKMT

open Filter TupleSurvivalBounds

universe u

noncomputable def growingRandomStart (x : ℕ) : ℕ := ⌊Real.log (x : ℝ) ^ (100 : ℕ)⌋₊

theorem growingRandomStart_tendsto : Tendsto growingRandomStart atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro n
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 1 (n : ℝ)))] with x hx
  change max 1 (n : ℝ) ≤ Real.log (x : ℝ) at hx
  have hL1 : 1 ≤ Real.log (x : ℝ) := (le_max_left _ _).trans hx
  have hLn : (n : ℝ) ≤ Real.log (x : ℝ) := (le_max_right _ _).trans hx
  have hpow : Real.log (x : ℝ) ≤ Real.log (x : ℝ) ^ (100 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (100 : ℕ))
  exact Nat.le_floor (hLn.trans hpow)

theorem eventually_growing_joint_accuracy :
    ∀ᶠ x : ℕ in atTop, ∀ Y : ℕ, 1 ≤ Y → Y ≤ x ^ 3 →
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (ell : P → ℕ) [∀ l, Fact (ell l).Prime],
        Function.Injective ell → (∀ l, growingRandomStart x < ell l) →
        Accurate ell Y (3 * sieveDimension (growingIndex x)) (1 / Real.log (x : ℝ) ^ (80 : ℕ)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growingDimension_bounds,
    hlog.eventually (eventually_ge_atTop (max 12 (2 * (36 + 324 / Real.log 2))))]
    with x hdim hlarge
  let L := Real.log (x : ℝ)
  change max 12 (2 * (36 + 324 / Real.log 2)) ≤ L at hlarge
  have hL : 12 ≤ L := (le_max_left _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLpow : L ≤ L ^ (100 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (100 : ℕ))
  have hKhalf : L ^ (100 : ℕ) / 2 ≤ (growingRandomStart x : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ (100 : ℕ))
    change L ^ (100 : ℕ) < (growingRandomStart x : ℝ) + 1 at hh
    linarith
  have hKposR : (0 : ℝ) < growingRandomStart x :=
    (by positivity : 0 < L ^ (100 : ℕ) / 2).trans_le hKhalf
  have hK : 0 < growingRandomStart x := by exact_mod_cast hKposR
  have hkL : (sieveDimension (growingIndex x) : ℝ) ≤ L := by
    apply hdim.2.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
  have hL2100 : L ^ (2 : ℕ) ≤ L ^ (100 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
  have hsize : 2 * (3 * sieveDimension (growingIndex x)) ≤ growingRandomStart x := by
    have hh : (2 : ℝ) * (3 * (sieveDimension (growingIndex x) : ℝ)) ≤ growingRandomStart x := by
      calc
        _ ≤ 6 * L := by linarith
        _ ≤ L ^ (2 : ℕ) / 2 := by nlinarith
        _ ≤ L ^ (100 : ℕ) / 2 := div_le_div_of_nonneg_right hL2100 (by norm_num)
        _ ≤ _ := hKhalf
    exact_mod_cast hh
  have hcoef : 2 * (36 + 324 / Real.log 2) ≤ L ^ (16 : ℕ) := by
    apply ((le_max_right _ _).trans hlarge).trans
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (16 : ℕ))
  have he0 : 0 ≤ 1 / L ^ (80 : ℕ) := by positivity
  have he1 : 1 / L ^ (80 : ℕ) ≤ 1 := by
    apply (div_le_one (pow_pos hLpos 80)).mpr
    exact one_le_pow₀ hL1
  intro Y hY hYx P _ _ ell _ hinj hell
  have hYlog : Real.log (Y : ℝ) ≤ 3 * L := by
    have hh := Real.log_le_log (by exact_mod_cast hY : (0 : ℝ) < Y)
      (by exact_mod_cast hYx : (Y : ℝ) ≤ (x : ℝ) ^ 3)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hr : ((3 * sieveDimension (growingIndex x) : ℕ) : ℝ) ≤ 3 * L := by
    push_cast
    linarith
  have hbudget := growing_joint_exponent_budget hL hKhalf
    (Nat.cast_nonneg (3 * sieveDimension (growingIndex x))) hr
    (Real.log_natCast_nonneg Y) hYlog hcoef
  exact accurate_of_prime_cutoff ell hK hinj hell hsize hY he0 he1 hbudget

end Erdos4.FGKMT

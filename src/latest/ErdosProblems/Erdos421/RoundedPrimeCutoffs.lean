import ErdosProblems.Erdos421.ComparableWindowScales

/-! # Rounded power cutoffs and their logarithmic sieve levels -/

namespace Erdos421

open Filter Topology

noncomputable def roundedPowerCutoff (X a : ℝ) : ℕ := ⌈X ^ a⌉₊

noncomputable def smallPrimeCutoff (X β : ℝ) : ℕ := roundedPowerCutoff X β + 1

noncomputable def intermediatePrimeCutoff (X : ℝ) : ℕ := roundedPowerCutoff X (39 / 200)

noncomputable def outerPrimeCutoff (X : ℝ) : ℕ := roundedPowerCutoff (3 * X) (1 / 2)

theorem roundedPowerCutoff_bounds {X a : ℝ} (hX : 1 ≤ X) (ha : 0 ≤ a) :
    X ^ a ≤ roundedPowerCutoff X a ∧ (roundedPowerCutoff X a : ℝ) ≤ 2 * X ^ a := by
  have hp : 1 ≤ X ^ a := Real.one_le_rpow hX ha
  have hc := Nat.ceil_lt_add_one (show 0 ≤ X ^ a by positivity)
  exact ⟨Nat.le_ceil _, by change (roundedPowerCutoff X a : ℝ) < _ at hc; linarith⟩

theorem roundedPowerCutoff_pos {X a : ℝ} (hX : 0 < X) : 0 < roundedPowerCutoff X a :=
  Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hX a)

theorem smallPrimeCutoff_bounds {X β : ℝ} (hX : 1 ≤ X) (hβ : 0 ≤ β) :
    X ^ β ≤ (smallPrimeCutoff X β - 1 : ℕ) ∧
      (smallPrimeCutoff X β : ℝ) ≤ 3 * X ^ β := by
  have hp := Real.one_le_rpow hX hβ
  have hb := roundedPowerCutoff_bounds hX hβ
  simp only [smallPrimeCutoff, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  exact ⟨hb.1, by linarith [hb.2]⟩

theorem smallPrimeCutoff_two_le {X β : ℝ} (hX : 0 < X) : 2 ≤ smallPrimeCutoff X β := by
  have h := roundedPowerCutoff_pos (a := β) hX
  dsimp only [smallPrimeCutoff]
  omega

theorem rounded_sieve_log_level {X β d : ℝ} (hX : 1 < X) (hβ : 0 < β) (hd : 0 < d)
    (hlog : Real.log 3 ≤ β * Real.log X) :
    d / (2 * β) ≤ Real.log (roundedPowerCutoff X d) / Real.log (smallPrimeCutoff X β) := by
  have hXp : 0 < X := by linarith
  have hLX := Real.log_pos hX
  have hW := smallPrimeCutoff_two_le (β := β) hXp
  have hWp : (0 : ℝ) < smallPrimeCutoff X β := by
    exact_mod_cast (by omega : 0 < smallPrimeCutoff X β)
  have hLW : 0 < Real.log (smallPrimeCutoff X β) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < smallPrimeCutoff X β))
  have hupper := Real.log_le_log hWp (smallPrimeCutoff_bounds hX.le hβ.le).2
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hXp β).ne',
    Real.log_rpow hXp] at hupper
  have hupper' : Real.log (smallPrimeCutoff X β) ≤ 2 * β * Real.log X := by linarith
  have hlower := Real.log_le_log (Real.rpow_pos_of_pos hXp d)
    (roundedPowerCutoff_bounds hX.le hd.le).1
  rw [Real.log_rpow hXp] at hlower
  calc
    _ = (d * Real.log X) / (2 * β * Real.log X) := by field_simp
    _ ≤ (d * Real.log X) / Real.log (smallPrimeCutoff X β) :=
      div_le_div_of_nonneg_left (mul_nonneg hd.le hLX.le) hLW hupper'
    _ ≤ _ := div_le_div_of_nonneg_right hlower hLW.le

theorem eventually_rounded_sieve_log_level {β d : ℝ} (hβ : 0 < β) (hd : 0 < d) :
    ∀ᶠ X : ℕ in atTop,
      d / (2 * β) ≤ Real.log (roundedPowerCutoff X d) / Real.log (smallPrimeCutoff X β) := by
  have hl : ∀ᶠ X : ℕ in atTop, Real.log 3 / β ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hl, eventually_ge_atTop 2] with X hlog hX
  apply rounded_sieve_log_level (by exact_mod_cast (show 1 < X by omega)) hβ hd
  have h := (div_le_iff₀ hβ).mp hlog
  linarith

theorem outerPrimeCutoff_bounds {X : ℝ} (hX : 1 ≤ X) :
    0 < outerPrimeCutoff X ∧ (outerPrimeCutoff X : ℝ) ≤ 6 * X ^ (1 / 2 : ℝ) ∧
      3 * X ≤ (outerPrimeCutoff X : ℝ) ^ 2 := by
  have hXp : 0 < X := by linarith
  have h3Xp : 0 < 3 * X := by positivity
  have hb := roundedPowerCutoff_bounds (show 1 ≤ 3 * X by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change (3 * X) ^ (1 / 2 : ℝ) ≤ outerPrimeCutoff X ∧
    (outerPrimeCutoff X : ℝ) ≤ 2 * (3 * X) ^ (1 / 2 : ℝ) at hb
  refine ⟨roundedPowerCutoff_pos h3Xp, hb.2.trans ?_, ?_⟩
  · rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hXp.le]
    have hr : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hXp.le (1 / 2))
    linarith
  · have hs := pow_le_pow_left₀ (Real.rpow_nonneg h3Xp.le (1 / 2)) hb.1 2
    rwa [← Real.sqrt_eq_rpow, Real.sq_sqrt h3Xp.le] at hs

theorem intermediatePrimeCutoff_le_outer {X : ℝ} (hX : 1 ≤ X) :
    intermediatePrimeCutoff X ≤ outerPrimeCutoff X := by
  apply Nat.ceil_mono
  calc
    X ^ (39 / 200 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    _ ≤ (3 * X) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)

end Erdos421

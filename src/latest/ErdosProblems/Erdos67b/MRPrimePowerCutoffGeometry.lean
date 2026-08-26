import ErdosProblems.Erdos67b.MRSmoothPrimeSelbergOscillation

/-! # Explicit geometry of the growing prime-sieve cutoff -/

open Filter

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

def mrPrimeSieveExponent (R : ℕ) : ℝ := savingExponent R / 16

def mrPrimeKernelSaving (R : ℕ) : ℝ := savingExponent R / 8

def mrPrimePowerCutoff (R : ℕ) (P : ℝ) : ℕ := ⌊P ^ mrPrimeSieveExponent R⌋₊

theorem mrPrimeSieveExponent_pos (R : ℕ) : 0 < mrPrimeSieveExponent R := by
  exact div_pos (savingExponent_pos R) (by norm_num)

theorem mrPrimeKernelSaving_pos (R : ℕ) : 0 < mrPrimeKernelSaving R := by
  exact div_pos (savingExponent_pos R) (by norm_num)

theorem mrPrimeSieveExponent_inv_eq (R : ℕ) :
    (mrPrimeSieveExponent R)⁻¹ = 128 * ((R : ℝ) + 1) * (2 : ℝ) ^ (R + 1) := by
  unfold mrPrimeSieveExponent savingExponent shiftExponent depth
  push_cast
  field_simp
  ring_nf

theorem mrPrimePowerCutoff_bounds {R : ℕ} {P : ℝ} (hP : 0 < P)
    (hbig : 4 ≤ P ^ mrPrimeSieveExponent R) :
    2 ≤ mrPrimePowerCutoff R P ∧
    P ^ mrPrimeSieveExponent R / 2 ≤ (mrPrimePowerCutoff R P : ℝ) ∧
    (mrPrimePowerCutoff R P : ℝ) ≤ P ^ mrPrimeSieveExponent R ∧
    mrPrimeSieveExponent R * Real.log P / 2 ≤ Real.log (mrPrimePowerCutoff R P : ℝ) := by
  have hD : 2 ≤ mrPrimePowerCutoff R P := Nat.le_floor (by norm_num; linarith)
  have hhalf : P ^ mrPrimeSieveExponent R / 2 ≤ (mrPrimePowerCutoff R P : ℝ) :=
    Erdos1149.AnalyticParameters.half_le_natFloor (by linarith)
  refine ⟨hD, hhalf, Nat.floor_le (Real.rpow_nonneg hP.le _), ?_⟩
  have hlog := Real.log_le_log (by positivity : 0 < P ^ mrPrimeSieveExponent R / 2) hhalf
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hP] at hlog
  have hlogBig := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hbig
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlogFour, Real.log_rpow hP] at hlogBig
  linarith

theorem mrPrimePowerCutoff_comparison {R : ℕ} {P : ℝ}
    (hP : 1 ≤ P) (hbig : 4 ≤ P ^ mrPrimeSieveExponent R)
    (hroom : 2 ≤ P ^ (1 / 2 - 2 * mrPrimeSieveExponent R)) :
    P ^ (1 / 2 : ℝ) ≤ P / (2 * (mrPrimePowerCutoff R P : ℝ) ^ 2) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  obtain ⟨hD, _, hupper, _⟩ := mrPrimePowerCutoff_bounds hPpos hbig
  have hDpos : (0 : ℝ) < mrPrimePowerCutoff R P := by
    exact_mod_cast (show 0 < mrPrimePowerCutoff R P by omega)
  have hsquare : (mrPrimePowerCutoff R P : ℝ) ^ 2 ≤ P ^ (2 * mrPrimeSieveExponent R) := by
    calc
      _ ≤ (P ^ mrPrimeSieveExponent R) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hupper _
      _ = P ^ (2 * mrPrimeSieveExponent R) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le]
        congr 1
        ring
  apply (le_div_iff₀ (by positivity : 0 < 2 * (mrPrimePowerCutoff R P : ℝ) ^ 2)).2
  have hprod : P ^ (1 / 2 : ℝ) * (2 * P ^ (2 * mrPrimeSieveExponent R)) ≤ P := by
    calc
      _ ≤ P ^ (1 / 2 : ℝ) *
          (P ^ (1 / 2 - 2 * mrPrimeSieveExponent R) * P ^ (2 * mrPrimeSieveExponent R)) := by
        gcongr
      _ = P := by
        rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
        rw [show (1 / 2 : ℝ) +
          (1 / 2 - 2 * mrPrimeSieveExponent R + 2 * mrPrimeSieveExponent R) = 1 by ring,
          Real.rpow_one]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsquare (by norm_num)) (by positivity)).trans hprod

theorem mrEventually_primePowerCutoff_geometry (R : ℕ) (hR : 2 ≤ R) (A₀ : ℕ) :
    ∀ᶠ P : ℝ in atTop,
      1 < P ∧ 2 ≤ mrPrimePowerCutoff R P ∧
      (mrPrimePowerCutoff R P : ℝ) ≤ P ^ mrPrimeSieveExponent R ∧
      mrPrimeSieveExponent R * Real.log P / 2 ≤ Real.log (mrPrimePowerCutoff R P : ℝ) ∧
      2 * (mrPrimePowerCutoff R P : ℝ) ^ 2 ≤ P ∧
      (A₀ : ℝ) ≤ P / (2 * (mrPrimePowerCutoff R P : ℝ) ^ 2) ∧
      P ^ (1 / 2 : ℝ) ≤ P / (2 * (mrPrimePowerCutoff R P : ℝ) ^ 2) := by
  have hdelta := mrSavingExponent_le_one_div_sixtyFour hR
  have hroomExp : 0 < 1 / 2 - 2 * mrPrimeSieveExponent R := by
    unfold mrPrimeSieveExponent
    linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (mrPrimeSieveExponent_pos R)).eventually (eventually_ge_atTop 4),
    (tendsto_rpow_atTop hroomExp).eventually (eventually_ge_atTop 2),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_ge_atTop (A₀ : ℝ))] with P hP hbig hroom hscale
  have hb := mrPrimePowerCutoff_bounds (by linarith : 0 < P) hbig
  have hcomp := mrPrimePowerCutoff_comparison hP.le hbig hroom
  have hroot : 1 ≤ P ^ (1 / 2 : ℝ) := Real.one_le_rpow hP.le (by norm_num)
  have hDpos : (0 : ℝ) < mrPrimePowerCutoff R P := by
    exact_mod_cast (show 0 < mrPrimePowerCutoff R P by omega)
  refine ⟨hP, hb.1, hb.2.2.1, hb.2.2.2, ?_, hscale.trans hcomp, hcomp⟩
  have hh := (le_div_iff₀ (by positivity : 0 < 2 * (mrPrimePowerCutoff R P : ℝ) ^ 2)).1
    (hroot.trans hcomp)
  simpa only [one_mul] using hh

theorem mrPrimePowerCutoff_height {R : ℕ} {P h t : ℝ}
    (hP : 1 < P) (hR : 2 * h ≤ (R : ℝ))
    (hcomp : P ^ (1 / 2 : ℝ) ≤ P / (2 * (mrPrimePowerCutoff R P : ℝ) ^ 2))
    (ht : |t| ≤ P ^ h) :
    positiveLogCoefficient t <
      (P / (2 * (mrPrimePowerCutoff R P : ℝ) ^ 2)) ^ (R + 1) := by
  have hPpos : 0 < P := by linarith
  have ha : positiveLogCoefficient t ≤ P ^ h := by
    unfold positiveLogCoefficient
    have hpi : 1 ≤ 2 * Real.pi := by have := Real.pi_gt_three; linarith
    exact (div_le_self (abs_nonneg t) hpi).trans ht
  apply ha.trans_lt
  calc
    P ^ h < P ^ ((1 / 2 : ℝ) * ((R : ℝ) + 1)) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hP
      linarith
    _ = (P ^ (1 / 2 : ℝ)) ^ (R + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le]
      push_cast
      rfl
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hcomp _

theorem mrPrimePowerCutoff_lt_scale {R : ℕ} (hR : 2 ≤ R) {P : ℝ} (hP : 1 < P) :
    (mrPrimePowerCutoff R P : ℝ) < P := by
  have hd := mrSavingExponent_le_one_div_sixtyFour hR
  calc
    _ ≤ P ^ mrPrimeSieveExponent R := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
    _ < P ^ (1 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hP
      unfold mrPrimeSieveExponent
      linarith
    _ = P := Real.rpow_one _

end

end Erdos67b

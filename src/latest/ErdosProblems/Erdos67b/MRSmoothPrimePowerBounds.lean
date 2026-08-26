import ErdosProblems.Erdos67b.MRPrimePowerCutoffGeometry

/-! # Explicit low- and high-frequency bounds with the power cutoff -/

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

def mrPrimeKernelErrorConstant (R : ℕ) : ℝ :=
  800 + 1400 * (6 * Real.pi + mrPrimeWeylConstant R + 20)

theorem mrPrimeKernelErrorConstant_pos (R : ℕ) : 0 < mrPrimeKernelErrorConstant R := by
  have := mrPrimeWeylConstant_pos R
  have := Real.pi_pos
  unfold mrPrimeKernelErrorConstant
  positivity

theorem mrSmoothPrime_kernel_low_power_bound {R : ℕ} (hR : 2 ≤ R) {P : ℝ}
    (hP : 1 < P) (hD : 2 ≤ mrPrimePowerCutoff R P)
    (hlog : mrPrimeSieveExponent R * Real.log P / 2 ≤
      Real.log (mrPrimePowerCutoff R P : ℝ))
    (hDP : 2 * (mrPrimePowerCutoff R P : ℝ) ^ 2 ≤ P)
    {t : ℝ} (ht : |t| ≤ P ^ (savingExponent R / 4)) :
    ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) (by omega) P t‖ ≤
      4000 * P / (mrPrimeSieveExponent R * Real.log P * (1 + t ^ 2)) +
        800 * P ^ (1 - mrPrimeKernelSaving R) := by
  have hPpos : 0 < P := by linarith
  have hk := mrPrimeSieveExponent_pos R
  have hlogP : 0 < Real.log P := Real.log_pos hP
  have hs : 0 < 1 + t ^ 2 := by positivity
  have hmain : 2000 * P / (Real.log (mrPrimePowerCutoff R P : ℝ) * (1 + t ^ 2)) ≤
      4000 * P / (mrPrimeSieveExponent R * Real.log P * (1 + t ^ 2)) := by
    calc
      _ ≤ 2000 * P / ((mrPrimeSieveExponent R * Real.log P / 2) * (1 + t ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hlog hs.le)
      _ = _ := by field_simp; ring
  have hupper : (mrPrimePowerCutoff R P : ℝ) ≤ P ^ mrPrimeSieveExponent R :=
    Nat.floor_le (Real.rpow_nonneg hPpos.le _)
  have hbeta : 1 ≤ P ^ (savingExponent R / 4) :=
    Real.one_le_rpow hP.le (by have := savingExponent_pos R; positivity)
  have herror : 400 * (mrPrimePowerCutoff R P : ℝ) ^ 2 * (1 + |t|) ≤
      800 * P ^ (1 - mrPrimeKernelSaving R) := by
    calc
      _ ≤ 400 * (P ^ mrPrimeSieveExponent R) ^ 2 * (2 * P ^ (savingExponent R / 4)) := by
        gcongr
        linarith
      _ = 800 * P ^ (2 * mrPrimeSieveExponent R + savingExponent R / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le]
        rw [Real.rpow_add hPpos]
        norm_num only [Nat.cast_ofNat]
        rw [mul_comm (mrPrimeSieveExponent R) (2 : ℝ)]
        ring
      _ ≤ 800 * P ^ (1 - mrPrimeKernelSaving R) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le hP.le
        have hd := mrSavingExponent_le_one_div_sixtyFour hR
        unfold mrPrimeSieveExponent mrPrimeKernelSaving
        linarith
  exact (norm_mrSmoothPrimeSelbergKernel_le _ hD hPpos hDP t).trans
    (add_le_add hmain herror)

theorem mrSmoothPrime_kernel_high_power_bound {R : ℕ} {P : ℝ}
    (hP : 1 ≤ P) (hD : 1 ≤ mrPrimePowerCutoff R P) {t : ℝ}
    (ht : P ^ (savingExponent R / 4) < |t|)
    (hbound : ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) hD P t‖ ≤
      1400 * (mrPrimePowerCutoff R P : ℝ) ^ 2 * (3 * P / positiveLogCoefficient t +
        (mrPrimeWeylConstant R + 20) * P ^ (1 - savingExponent R))) :
    ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) hD P t‖ ≤
      1400 * (6 * Real.pi + mrPrimeWeylConstant R + 20) *
        P ^ (1 - mrPrimeKernelSaving R) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have htpos : 0 < |t| := (Real.rpow_pos_of_pos hPpos _).trans ht
  have ha : 0 < positiveLogCoefficient t := by unfold positiveLogCoefficient; positivity
  have hC := mrPrimeWeylConstant_pos R
  have hupper : (mrPrimePowerCutoff R P : ℝ) ≤ P ^ mrPrimeSieveExponent R :=
    Nat.floor_le (Real.rpow_nonneg hPpos.le _)
  have hfirst : 3 * P / positiveLogCoefficient t ≤
      6 * Real.pi * P ^ (1 - savingExponent R / 4) := by
    calc
      _ = 6 * Real.pi * P / |t| := by unfold positiveLogCoefficient; field_simp; ring
      _ ≤ 6 * Real.pi * P / P ^ (savingExponent R / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) ht.le
      _ = 6 * Real.pi * P ^ (1 - savingExponent R / 4) := by
        rw [Real.rpow_sub hPpos, Real.rpow_one]
        ring
  have hcollapse (v : ℝ) : (P ^ mrPrimeSieveExponent R) ^ (2 : ℕ) * P ^ v =
      P ^ (2 * mrPrimeSieveExponent R + v) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le, ← Real.rpow_add hPpos]
    congr 1
    ring
  have hpowFirst : P ^ (2 * mrPrimeSieveExponent R + (1 - savingExponent R / 4)) =
      P ^ (1 - mrPrimeKernelSaving R) := by
    congr 1
    unfold mrPrimeSieveExponent mrPrimeKernelSaving
    ring
  have hpowSecond : P ^ (2 * mrPrimeSieveExponent R + (1 - savingExponent R)) ≤
      P ^ (1 - mrPrimeKernelSaving R) := by
    apply Real.rpow_le_rpow_of_exponent_le hP
    have := savingExponent_pos R
    unfold mrPrimeSieveExponent mrPrimeKernelSaving
    linarith
  apply hbound.trans
  calc
    _ ≤ 1400 * (P ^ mrPrimeSieveExponent R) ^ 2 *
        (6 * Real.pi * P ^ (1 - savingExponent R / 4) +
          (mrPrimeWeylConstant R + 20) * P ^ (1 - savingExponent R)) := by gcongr
    _ = 1400 * (6 * Real.pi * P ^ (2 * mrPrimeSieveExponent R + (1 - savingExponent R / 4)) +
        (mrPrimeWeylConstant R + 20) *
          P ^ (2 * mrPrimeSieveExponent R + (1 - savingExponent R))) := by
      rw [← hcollapse, ← hcollapse]
      ring
    _ ≤ 1400 * (6 * Real.pi * P ^ (1 - mrPrimeKernelSaving R) +
        (mrPrimeWeylConstant R + 20) * P ^ (1 - mrPrimeKernelSaving R)) := by
      rw [hpowFirst]
      gcongr
    _ = _ := by ring

end

end Erdos67b

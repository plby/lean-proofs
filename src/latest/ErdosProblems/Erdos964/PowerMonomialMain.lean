import ErdosProblems.Erdos964.PowerAbelMain
import ErdosProblems.Erdos964.NormalizedLogMonomial

/-!
# Exact Abel main terms for logarithmic monomials
-/

namespace Erdos964

open MeasureTheory

theorem generalAbelMain_log_power_monomial (Q : ℕ) (hQ : 1 ≤ Q)
    (c L : ℝ) (κ j : ℕ) (hκ : 0 < κ) :
    generalAbelMain Q (fun t => c * (Real.log t) ^ κ) (normalizedLogMonomial L j) =
      c * κ / ((κ + j : ℕ) : ℝ) * (Real.log Q) ^ (κ + j) / L ^ j := by
  let B : ℝ → ℝ := fun t => c * (Real.log t) ^ κ
  let f := normalizedLogMonomial L j
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : 0 < t := zero_lt_one.trans_le ht.1
  have hBderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) :
      HasDerivAt B (c * κ * (Real.log t) ^ (κ - 1) / t) t := by
    have h := ((Real.hasDerivAt_log (hpos t ht).ne').pow κ).const_mul c
    have hid : c * ((κ : ℝ) * (Real.log t) ^ (κ - 1) * t⁻¹) =
        c * κ * (Real.log t) ^ (κ - 1) / t := by ring
    rw [hid] at h
    simpa only [B, Pi.pow_apply] using h
  have hBcont : ContinuousOn (deriv B) (Set.Icc (1 : ℝ) Q) := by
    have hformula : ContinuousOn (fun t => c * κ * (Real.log t) ^ (κ - 1) / t)
        (Set.Icc (1 : ℝ) Q) :=
      (continuousOn_const.mul ((continuousOn_id.log
        (fun t ht => (hpos t ht).ne')).pow (κ - 1))).div continuousOn_id
        (fun t ht => (hpos t ht).ne')
    exact hformula.congr (fun t ht => (hBderiv t ht).deriv)
  have hfcont := normalizedLogMonomial_continuousOn L j Q
  have hfderivcont := normalizedLogMonomial_deriv_continuousOn L j Q
  have hB1 : B 1 = 0 := by simp only [B, Real.log_one, zero_pow hκ.ne', mul_zero]
  rw [generalAbelMain_eq_integral_deriv Q hQ B f hB1
    (fun t ht => (normalizedLogMonomial_hasDerivAt L j t (hpos t ht)).differentiableAt.hasDerivAt)
    (fun t ht => (hBderiv t ht).differentiableAt.hasDerivAt)
    (hfderivcont.intervalIntegrable_of_Icc hQR) (hBcont.intervalIntegrable_of_Icc hQR)]
  have hint : IntervalIntegrable (fun t => f t * deriv B t) volume 1 Q :=
    (hfcont.mul hBcont).intervalIntegrable_of_Icc hQR
  have hκj : κ + j ≠ 0 := by omega
  have hκjR : ((κ + j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hκj
  have hprimitive (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) Q) :
      HasDerivAt (fun t => (c * κ / ((κ + j : ℕ) : ℝ) / L ^ j) * (Real.log t) ^ (κ + j))
        (f t * deriv B t) t := by
    have ht' : t ∈ Set.Icc (1 : ℝ) Q := by simpa only [Set.uIcc_of_le hQR] using ht
    have h := ((Real.hasDerivAt_log (hpos t ht').ne').pow (κ + j)).const_mul
      (c * κ / ((κ + j : ℕ) : ℝ) / L ^ j)
    have hid : (c * κ / ((κ + j : ℕ) : ℝ) / L ^ j) *
        (((κ + j : ℕ) : ℝ) * (Real.log t) ^ (κ + j - 1) * t⁻¹) = f t * deriv B t := by
      rw [(hBderiv t ht').deriv]
      dsimp only [f, normalizedLogMonomial]
      rw [show κ + j - 1 = j + (κ - 1) by omega, pow_add]
      field_simp [hκjR]
    rw [hid] at h
    simpa only [Pi.pow_apply] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprimitive hint]
  simp only [Real.log_one, zero_pow hκj, mul_zero, sub_zero]
  ring

end Erdos964

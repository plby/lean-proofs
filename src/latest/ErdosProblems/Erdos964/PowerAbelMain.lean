import ErdosProblems.Erdos964.PowerAbelError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The derivative form of a general cumulative Abel main term
-/

namespace Erdos964

open MeasureTheory

theorem generalAbelMain_eq_integral_deriv (Q : ℕ) (hQ : 1 ≤ Q) (B f : ℝ → ℝ)
    (hB1 : B 1 = 0)
    (hfderiv : ∀ t ∈ Set.Icc (1 : ℝ) Q, HasDerivAt f (deriv f t) t)
    (hBderiv : ∀ t ∈ Set.Icc (1 : ℝ) Q, HasDerivAt B (deriv B t) t)
    (hfint : IntervalIntegrable (deriv f) volume 1 Q)
    (hBint : IntervalIntegrable (deriv B) volume 1 Q) :
    generalAbelMain Q B f = ∫ t in (1 : ℝ)..Q, f t * deriv B t := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hfU : ∀ t ∈ Set.uIcc (1 : ℝ) Q, HasDerivAt f (deriv f t) t := by
    simpa only [Set.uIcc_of_le hQR] using hfderiv
  have hBU : ∀ t ∈ Set.uIcc (1 : ℝ) Q, HasDerivAt B (deriv B t) t := by
    simpa only [Set.uIcc_of_le hQR] using hBderiv
  have hfcont : ContinuousOn f (Set.uIcc (1 : ℝ) Q) :=
    fun t ht => (hfU t ht).continuousAt.continuousWithinAt
  have hBcont : ContinuousOn B (Set.uIcc (1 : ℝ) Q) :=
    fun t ht => (hBU t ht).continuousAt.continuousWithinAt
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub hfU hBU hfint hBint
  rw [hB1, mul_zero, sub_zero, intervalIntegral.integral_add
    (hfint.mul_continuousOn hBcont) (hBint.continuousOn_mul hfcont)] at hparts
  unfold generalAbelMain
  rw [← intervalIntegral.integral_of_le hQR]
  linarith

end Erdos964

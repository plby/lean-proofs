import ErdosProblems.Erdos964.ScalarPrimeIntegrand

/-!
# The exact large-prime integral in the scalar positivity certificate
-/

namespace Erdos964

open MeasureTheory

theorem largePrimeIntegral_interval_bounds (a z : ℝ) (ha : 0 < a) (ha2 : a < 1 / 2)
    (hz : z ∈ Set.Icc (1 : ℝ) (1 / (2 * a))) :
    0 < z ∧ 0 < 1 - a * z := by
  have hab : a * (1 / (2 * a)) = 1 / 2 := by field_simp
  have haz : a * z ≤ 1 / 2 := by
    rw [← hab]
    exact mul_le_mul_of_nonneg_left hz.2 ha.le
  constructor <;> linarith [hz.1]

theorem hasDerivAt_primeLogPrimitive (a z : ℝ) (hz : z ≠ 0) (haz : 1 - a * z ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log u - Real.log (1 - a * u))
      (1 / (z * (1 - a * z))) z := by
  have hlin : HasDerivAt (fun u : ℝ => 1 - a * u) (-a) z := by
    exact ((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).const_mul a)).congr_deriv
      (by ring)
  have h := (Real.hasDerivAt_log hz).sub (hlin.log haz)
  have haz' : 1 - z * a ≠ 0 := by simpa only [mul_comm] using haz
  have hid : z⁻¹ - -a / (1 - a * z) = 1 / (z * (1 - a * z)) := by
    field_simp [hz, haz, haz']
    ring
  exact h.congr_deriv hid

theorem integral_primeLogKernel (a : ℝ) (ha : 0 < a) (ha2 : a < 1 / 2) :
    (∫ z in (1 : ℝ)..(1 / (2 * a)), 1 / (z * (1 - a * z))) =
      Real.log ((1 - a) / a) := by
  have hab : (1 : ℝ) ≤ 1 / (2 * a) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hbound (z : ℝ) (hz : z ∈ Set.uIcc (1 : ℝ) (1 / (2 * a))) :
      0 < z ∧ 0 < 1 - a * z :=
    largePrimeIntegral_interval_bounds a z ha ha2 (by simpa only [Set.uIcc_of_le hab] using hz)
  have hcont : ContinuousOn (fun z : ℝ => 1 / (z * (1 - a * z)))
      (Set.uIcc (1 : ℝ) (1 / (2 * a))) := by
    apply continuousOn_const.div (by fun_prop)
    intro z hz
    exact mul_ne_zero (hbound z hz).1.ne' (hbound z hz).2.ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z hz => hasDerivAt_primeLogPrimitive a z (hbound z hz).1.ne' (hbound z hz).2.ne')
    hcont.intervalIntegrable
  have hhalf : 1 - a * (1 / (2 * a)) = 1 / 2 := by field_simp; ring
  rw [hhalf] at h
  have ha1 : 0 < 1 - a := by linarith
  calc
    _ = (Real.log (1 / (2 * a)) - Real.log (1 / 2)) -
        (Real.log 1 - Real.log (1 - a * 1)) := h
    _ = _ := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (mul_ne_zero (by norm_num) ha.ne'),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne',
        Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_div ha1.ne' ha.ne']
      simp only [Real.log_one, mul_one]
      ring

theorem integral_scalarLargePrimeIntegrand (a : ℝ) (ha : 0 < a) (ha2 : a < 1 / 2) :
    (∫ z in (1 : ℝ)..(1 / (2 * a)), scalarLargePrimeIntegrand a z) =
      Real.log ((1 - a) / a) * truncatedSieveFace 1 := by
  have heq : scalarLargePrimeIntegrand a = fun z : ℝ =>
      (41 / 60) * (1 / (z * (1 - a * z))) := by
    funext z
    unfold scalarLargePrimeIntegrand
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_primeLogKernel a ha ha2]
  rw [truncatedSieveFace_eq]
  norm_num [sieveFaceKernel]
  ring

end Erdos964

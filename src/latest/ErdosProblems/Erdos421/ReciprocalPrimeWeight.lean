import ErdosProblems.Erdos421.WeightedPrimeLogSaving
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The reciprocal-prime weight and its logarithmic integral -/

namespace Erdos421

open MeasureTheory

noncomputable def reciprocalPrimeWeight (t : ℝ) : ℝ := 1 / (t * Real.log t)

theorem reciprocalPrimeWeight_pos {t : ℝ} (ht : 1 < t) : 0 < reciprocalPrimeWeight t :=
  div_pos zero_lt_one (mul_pos (by linarith) (Real.log_pos ht))

theorem reciprocalPrimeWeight_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt reciprocalPrimeWeight (-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
  have htp : 0 < t := by linarith
  have hLt := Real.log_pos ht
  have hden : t * Real.log t ≠ 0 := by positivity
  have hd := (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).mul (Real.hasDerivAt_log htp.ne')) hden
  dsimp only [Pi.mul_apply, id_eq] at hd
  convert hd using 1 <;> first | rfl | (field_simp; ring)

theorem reciprocalPrimeWeight_continuousOn : ContinuousOn reciprocalPrimeWeight (Set.Ioi 1) := by
  intro t ht
  exact (reciprocalPrimeWeight_hasDerivAt ht).continuousAt.continuousWithinAt

theorem reciprocalPrimeWeight_deriv_continuousOn :
    ContinuousOn (deriv reciprocalPrimeWeight) (Set.Ioi 1) := by
  have hc : ContinuousOn (fun t : ℝ ↦ -(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      (Set.Ioi 1) := by
    intro t ht
    have ht1 : 1 < t := ht
    have htp : t ≠ 0 := by linarith
    have hL : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hden : t ^ 2 * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 htp) (pow_ne_zero 2 hL)
    fun_prop
  apply hc.congr
  intro t ht
  exact (reciprocalPrimeWeight_hasDerivAt ht).deriv

theorem reciprocalPrimeWeight_integral {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, reciprocalPrimeWeight t) = Real.log (Real.log b / Real.log a) := by
  have heq : reciprocalPrimeWeight = (fun t : ℝ ↦ t⁻¹ / Real.log t) := by
    funext t
    dsimp only [reciprocalPrimeWeight]
    ring
  rw [heq, integral_inv_div_log ha hb,
    Real.log_div (Real.log_pos hb).ne' (Real.log_pos ha).ne']

theorem reciprocalPrimeWeight_endpoint_le {t : ℝ} (ht : 1 < t) (hlog : 1 ≤ Real.log t) :
    t * |reciprocalPrimeWeight t| ≤ 1 := by
  have htp : 0 < t := by linarith
  have hLt := Real.log_pos ht
  rw [abs_of_pos (reciprocalPrimeWeight_pos ht)]
  calc
    _ = 1 / Real.log t := by dsimp only [reciprocalPrimeWeight]; field_simp
    _ ≤ _ := (div_le_one hLt).mpr hlog

theorem reciprocalPrimeWeight_deriv_variation {t : ℝ} (ht : 1 < t) (hlog : 1 ≤ Real.log t) :
    t * |deriv reciprocalPrimeWeight t| ≤ 2 * reciprocalPrimeWeight t := by
  have htp : 0 < t := by linarith
  have hLt := Real.log_pos ht
  rw [(reciprocalPrimeWeight_hasDerivAt ht).deriv, abs_div, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ Real.log t + 1),
    abs_of_pos (by positivity : 0 < t ^ 2 * (Real.log t) ^ 2)]
  calc
    _ = (Real.log t + 1) / (t * (Real.log t) ^ 2) := by field_simp
    _ ≤ (2 * Real.log t) / (t * (Real.log t) ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by dsimp only [reciprocalPrimeWeight]; field_simp

end Erdos421

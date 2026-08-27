/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueModel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Numerical local logarithm errors for the random residue sieve -/

namespace Erdos4b.FGKMT

theorem log_one_sub_remainder_bound {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2) :
    |Real.log (1 - v) + v| ≤ 2 * v ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (by rw [abs_of_nonneg hv0]; linarith : |v| < 1) 1
  norm_num [Finset.sum_range_one, abs_of_nonneg hv0] at h
  have hden : 0 < 1 - v := by linarith
  have hb : v ^ 2 / (1 - v) ≤ 2 * v ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_right hv (sq_nonneg v)]
  simpa only [add_comm] using h.trans hb

theorem ordinary_residue_log_error {t p : ℝ}
    (ht : 1 ≤ t) (hp : 0 < p) (hsmall : t / p ≤ 1 / 2) :
    |Real.log (1 - t / p) - t * Real.log (1 - 1 / p)| ≤ 4 * t ^ 2 / p ^ 2 := by
  have ht0 : 0 ≤ t := by linarith
  have htp0 : 0 ≤ t / p := div_nonneg ht0 hp.le
  have hone : 1 / p ≤ 1 / 2 := (div_le_div_of_nonneg_right ht hp.le).trans hsmall
  have hA := log_one_sub_remainder_bound htp0 hsmall
  have hB := log_one_sub_remainder_bound (by positivity : 0 ≤ 1 / p) hone
  have hid : Real.log (1 - t / p) - t * Real.log (1 - 1 / p) =
      (Real.log (1 - t / p) + t / p) - t * (Real.log (1 - 1 / p) + 1 / p) := by ring
  rw [hid]
  calc
    _ ≤ |Real.log (1 - t / p) + t / p| + |t * (Real.log (1 - 1 / p) + 1 / p)| :=
      abs_sub _ _
    _ = |Real.log (1 - t / p) + t / p| + t * |Real.log (1 - 1 / p) + 1 / p| := by
      rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ 2 * (t / p) ^ 2 + t * (2 * (1 / p) ^ 2) :=
      add_le_add hA (mul_le_mul_of_nonneg_left hB ht0)
    _ = (2 * t ^ 2 + 2 * t) / p ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg p)

theorem exceptional_residue_log_error {v t p : ℝ}
    (hv : 0 ≤ v) (hvt : v ≤ t) (hp : 0 < p) (hsmall : t / p ≤ 1 / 2) :
    |Real.log (1 - v / p) - Real.log (1 - t / p)| ≤ 2 * t / p := by
  have ht : 0 ≤ t := hv.trans hvt
  have htp : 0 ≤ t / p := div_nonneg ht hp.le
  have hvp : 0 ≤ v / p := div_nonneg hv hp.le
  have hle : v / p ≤ t / p := div_le_div_of_nonneg_right hvt hp.le
  have hb : 0 < 1 - t / p := by linarith
  have ha : 0 < 1 - v / p := by linarith
  have hlog := Real.log_le_log hb (by linarith : 1 - t / p ≤ 1 - v / p)
  rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  apply h.trans
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hb).mpr
  have hh := mul_le_mul_of_nonneg_left hsmall htp
  simp only [mul_div_assoc]
  nlinarith

theorem residue_local_log_error {v t p : ℝ}
    (ht : 1 ≤ t) (hv : 0 ≤ v) (hvt : v ≤ t) (hp : 0 < p)
    (hsmall : t / p ≤ 1 / 2) :
    |Real.log (1 - v / p) - t * Real.log (1 - 1 / p)| ≤
      4 * t ^ 2 / p ^ 2 + if v = t then 0 else 2 * t / p := by
  by_cases heq : v = t
  · subst v
    rw [if_pos rfl, add_zero]
    exact ordinary_residue_log_error ht hp hsmall
  · rw [if_neg heq]
    calc
      _ ≤ |Real.log (1 - v / p) - Real.log (1 - t / p)| +
          |Real.log (1 - t / p) - t * Real.log (1 - 1 / p)| := abs_sub_le _ _ _
      _ ≤ 2 * t / p + 4 * t ^ 2 / p ^ 2 :=
        add_le_add (exceptional_residue_log_error hv hvt hp hsmall)
          (ordinary_residue_log_error ht hp hsmall)
      _ = _ := by ring

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.log_one_sub_remainder_bound
#print axioms Erdos4b.FGKMT.residue_local_log_error

import ErdosProblems.Erdos69.ConstructionBounds
import ErdosProblems.Erdos69.ParameterLimits

/-! # Comparisons and exact logarithms of the integer cutoffs -/

namespace Erdos69.Elementary

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem log_log_two_nonpos : Real.log (Real.log (2 : ℝ)) ≤ 0 :=
  Real.log_nonpos (Real.log_pos (by norm_num)).le log_two_le_one

theorem log_dilationPrimeCutoff (m : ℕ) :
    Real.log (dilationPrimeCutoff m : ℝ) = (patternSize m : ℝ) ^ 2 * Real.log 2 := by
  simp [dilationPrimeCutoff, Real.log_pow]

theorem log_smallPrimeCutoff (m : ℕ) :
    Real.log (smallPrimeCutoff m : ℝ) = (2 : ℝ) ^ fluctuationScale m * Real.log 2 := by
  simp [smallPrimeCutoff, Real.log_pow]

theorem log_progressionLength (m : ℕ) :
    Real.log (progressionLength m : ℝ) =
      40 * fluctuationScale m * (2 : ℝ) ^ fluctuationScale m * Real.log 2 := by
  simp [progressionLength, Real.log_pow, log_smallPrimeCutoff, mul_assoc]

theorem log_intermediatePrimeCutoff (m : ℕ) :
    Real.log (intermediatePrimeCutoff m : ℝ) =
      20 * fluctuationScale m * (2 : ℝ) ^ fluctuationScale m * Real.log 2 := by
  simp [intermediatePrimeCutoff, Real.log_pow, log_smallPrimeCutoff, mul_assoc]

theorem log_excludedPrimeCutoff (m : ℕ) :
    Real.log (excludedPrimeCutoff m : ℝ) = (patternSize m : ℝ) ^ 3 * Real.log 2 := by
  simp [excludedPrimeCutoff, Real.log_pow]

theorem smallPrimeCutoff_ge_two (m : ℕ) : 2 ≤ smallPrimeCutoff m := by
  unfold smallPrimeCutoff
  have h : 0 < 2 ^ fluctuationScale m := by positivity
  exact Nat.one_lt_two_pow h.ne'

theorem excludedPrimeCutoff_ge_two (m : ℕ) : 2 ≤ excludedPrimeCutoff m := by
  unfold excludedPrimeCutoff
  exact Nat.one_lt_two_pow (Nat.pow_pos (patternSize_pos m)).ne'

theorem log_log_smallPrimeCutoff (m : ℕ) :
    Real.log (Real.log (smallPrimeCutoff m : ℝ)) =
      (fluctuationScale m : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  rw [log_smallPrimeCutoff, Real.log_mul (by positivity)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', Real.log_pow]

theorem log_log_intermediate_sub_small (m : ℕ) :
    Real.log (Real.log (intermediatePrimeCutoff m : ℝ)) -
      Real.log (Real.log (smallPrimeCutoff m : ℝ)) =
        Real.log (20 : ℝ) + 4 * m * Real.log 36 := by
  have hscale : (0 : ℝ) < fluctuationScale m := by exact_mod_cast fluctuationScale_pos m
  have hlogy : 0 < Real.log (smallPrimeCutoff m : ℝ) :=
    Real.log_pos (by exact_mod_cast smallPrimeCutoff_ge_two m)
  have hlogR : Real.log (intermediatePrimeCutoff m : ℝ) =
      (20 * fluctuationScale m : ℝ) * Real.log (smallPrimeCutoff m : ℝ) := by
    simp [intermediatePrimeCutoff, Real.log_pow]
  rw [hlogR, Real.log_mul (by positivity) hlogy.ne', add_sub_cancel_right,
    Real.log_mul (by norm_num) hscale.ne']
  simp only [fluctuationScale, patternSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring

theorem twice_excluded_le_two_pow_scale {m : ℕ} (hm : 0 < m) :
    2 * excludedPrimeCutoff m ≤ 2 ^ fluctuationScale m := by
  have hN := patternSize_ge_thirtysix hm
  have hexp : patternSize m ^ 3 + 1 ≤ patternSize m ^ 4 := by
    have hp := Nat.pow_pos (patternSize_pos m) (n := 3)
    have hmul := Nat.mul_le_mul_right (patternSize m ^ 3) (show 2 ≤ patternSize m by omega)
    nlinarith
  unfold excludedPrimeCutoff fluctuationScale
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hexp

theorem constructionModulus_le_smallPrimeCutoff {m : ℕ} (hm : 0 < m) :
    constructionModulus m ≤ smallPrimeCutoff m := by
  have hbound := log_constructionModulus_le_excluded hm
  have htwo : (2 : ℝ) * excludedPrimeCutoff m ≤ (2 : ℝ) ^ fluctuationScale m := by
    exact_mod_cast twice_excluded_le_two_pow_scale hm
  have hlog : Real.log (constructionModulus m : ℝ) ≤ Real.log (smallPrimeCutoff m : ℝ) := by
    rw [log_smallPrimeCutoff]
    have hp : 0 ≤ (2 : ℝ) ^ fluctuationScale m := by positivity
    nlinarith [mul_le_mul_of_nonneg_right half_le_log_two hp]
  have hQ : (0 : ℝ) < constructionModulus m := by exact_mod_cast constructionModulus_pos m
  have hy : (0 : ℝ) < smallPrimeCutoff m := by exact_mod_cast smallPrimeCutoff_pos m
  exact_mod_cast (Real.log_le_log_iff hQ hy).mp hlog

theorem twice_shift_card_le_excluded {m : ℕ} (hm : 0 < m) :
    2 * Fintype.card (ConstructionShift m) ≤ excludedPrimeCutoff m := by
  have hcard := constructionShift_card_le m
  have hN := patternSize_ge_thirtysix hm
  have hexp : patternSize m * 5 + 2 ≤ patternSize m ^ 3 := by
    have hmul := Nat.mul_le_mul_right (patternSize m ^ 2) (show 2 ≤ patternSize m by omega)
    nlinarith
  calc
    _ ≤ 4 * patternSize m ^ 5 := by
      unfold retainedLength fluctuationScale at hcard
      calc
        _ ≤ 2 * (patternSize m * (2 * patternSize m ^ 4)) := Nat.mul_le_mul_left 2 hcard
        _ = _ := by ring
    _ ≤ 4 * (2 ^ patternSize m) ^ 5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = 2 ^ (patternSize m * 5 + 2) := by rw [pow_add, pow_mul]; ring
    _ ≤ excludedPrimeCutoff m := Nat.pow_le_pow_right (by norm_num) hexp

end Erdos69.Elementary

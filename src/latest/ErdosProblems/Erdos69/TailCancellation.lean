import ErdosProblems.Erdos69.PatternCoefficients

/-! # Applying the cancellation pattern to arithmetic tails -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem pattern_shift_int_identity (m P n h : ℕ) (i : PatternLabel m) :
    (n : ℤ) + (patternDilation m P i : ℤ) * h - patternOffset m P i =
      n + ((primorial P : ℤ) + 1) * h + (primorial P : ℤ) * patternPhase m i h := by
  simp only [patternDilation, roughDilation, patternOffset, patternPhase,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

theorem pattern_shift_toNat (m P n h : ℕ) (i : PatternLabel m) :
    ((n : ℤ) + ((primorial P : ℤ) + 1) * h +
      (primorial P : ℤ) * patternPhase m i h).toNat =
        n + patternDilation m P i * h - patternOffset m P i := by
  rw [← pattern_shift_int_identity]
  rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_sub]

theorem initial_arithmetic_cancellation (m P n h : ℕ) (hpos : 1 ≤ h) (hle : h ≤ 6 * m)
    (f : ℕ → ℝ) :
    (∑ i : PatternLabel m, (patternSign m i : ℝ) *
      f (n + patternDilation m P i * h - patternOffset m P i)) = 0 := by
  have hs := patternSignedSum_vanish m hpos hle
    (fun t ↦ f (((n : ℤ) + ((primorial P : ℤ) + 1) * h + (primorial P : ℤ) * t).toNat))
  simpa only [patternSignedSum, pattern_shift_toNat] using hs

theorem dilation_quotient_shift {a b n : ℕ} (ha : 0 < a) (hb : b ≤ n)
    (hn : n ≡ b [MOD a]) (h : ℕ) :
    a * ((n - b) / a + h) = n + a * h - b := by
  have hd : a ∣ n - b := (Nat.modEq_iff_dvd' hb).mp hn.symm
  rw [Nat.mul_add, Nat.mul_div_cancel' hd]
  omega

theorem corrected_signed_tail_integer {ι : Type*} [Fintype ι]
    {q : ℕ} {z : ℤ} (h : (q : ℝ) * binaryOmegaSum = z)
    (a m : ι → ℕ) (ha : ∀ i, a i ≠ 0) (s : ι → ℤ) :
    ∃ t : ℤ, (q : ℝ) * (∑ i, (s i : ℝ) * dilatedPositiveTail (a i) (m i)) +
      (q : ℝ) * (∑ i, (s i : ℝ) * compositeCorrection (a i) (m i)) = t := by
  classical
  choose t ht using fun i ↦ integer_mul_corrected_dilatedTail h (ha i) (m i)
  refine ⟨∑ i, s i * t i, ?_⟩
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (s i : ℝ) * ((q : ℝ) * (dilatedPositiveTail (a i) (m i) +
        compositeCorrection (a i) (m i))) := by ring
    _ = _ := by rw [ht i]

end Erdos69.Elementary

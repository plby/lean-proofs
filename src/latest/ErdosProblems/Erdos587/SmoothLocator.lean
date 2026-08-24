import ErdosProblems.Erdos587.LocatorFourier
import ErdosProblems.Erdos587.LocatorWeight
import ErdosProblems.Erdos587.CountWitness

/-! A one-sided integer locator from one-sixth harmonic estimates. -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_integer_above_of_harmonic_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : ℕ → ℝ) (N : ℕ) (δ E : ℝ),
      0 < δ → δ ≤ 1 → 0 ≤ E →
      (∀ m : ℤ, m ≠ 0 →
        ‖∑ n ∈ Finset.range N, phase ((m : ℝ) * f n)‖ ≤ E * |(m : ℝ)| ^ (1 / 6 : ℝ)) →
      D * E * δ ^ (-(1 / 6 : ℝ)) < (N : ℝ) * δ →
      ∃ n < N, ∃ k : ℤ, 0 < (k : ℝ) - f n ∧ (k : ℝ) - f n < δ := by
  obtain ⟨C, hC, hmoment⟩ := exists_scaledFourierCoeff_sixth_moment physicalSquareWeight
  refine ⟨16 * C, by positivity, ?_⟩
  intro f N δ E hδ hδ1 hE hharmonic hbudget
  have hnegative (m : ℤ) (hm : m ≠ 0) :
      ‖∑ n ∈ Finset.range N, phase ((m : ℝ) * (-f n))‖ ≤ E * |(m : ℝ)| ^ (1 / 6 : ℝ) := by
    simpa only [Int.cast_neg, neg_mul, mul_neg, abs_neg] using hharmonic (-m) (neg_ne_zero.mpr hm)
  have herror := finite_periodization_error_bound physicalSquareWeight hδ hE
    (fun n => -f n) N hnegative (hmoment δ hδ hδ1).1 (hmoment δ hδ hδ1).2
  let Z : ℂ := ∑ n ∈ Finset.range N, periodizedSchwartz physicalSquareWeight δ (-f n)
  let W : ℂ := (N : ℂ) * scaledFourierCoeff physicalSquareWeight δ 0
  have hmain : (N : ℝ) * δ / 16 ≤ W.re := by
    dsimp only [W]
    rw [Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (physicalSquareWeight_scaled_zero_lower hδ.le) (Nat.cast_nonneg N)
  have hstrict : ‖Z - W‖ < W.re := by
    change ‖Z - W‖ ≤ E * (C * δ ^ (-(1 / 6 : ℝ))) at herror
    have hh : E * (C * δ ^ (-(1 / 6 : ℝ))) < (N : ℝ) * δ / 16 := by nlinarith [hbudget]
    exact herror.trans_lt (hh.trans_le hmain)
  have hZ : Z ≠ 0 := by
    intro hz
    rw [hz, zero_sub, norm_neg] at hstrict
    exact (Complex.re_le_norm W).not_gt hstrict
  have hexists : ∃ n ∈ Finset.range N, periodizedSchwartz physicalSquareWeight δ (-f n) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hZ (Finset.sum_eq_zero hh)
  obtain ⟨n, hn, hp⟩ := hexists
  obtain ⟨k, hk⟩ := periodizedSchwartz_ne_zero_witness physicalSquareWeight δ (-f n) hp
  obtain ⟨hlo, hhi⟩ := physicalSquareWeight_support hk
  have hlo' := mul_lt_mul_of_pos_left hlo hδ
  have hhi' := mul_lt_mul_of_pos_left hhi hδ
  have hcancel : δ * (δ⁻¹ * (-f n + k)) = (k : ℝ) - f n := by
    rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
    ring
  rw [hcancel] at hlo' hhi'
  exact ⟨n, Finset.mem_range.mp hn, k, by linarith, by linarith⟩

end Erdos587

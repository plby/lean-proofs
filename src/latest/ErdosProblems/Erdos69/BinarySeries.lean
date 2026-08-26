import ErdosProblems.Erdos69.ElementaryArithmetic

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable section

/-- The binary tail starting at `n`, with its first term unscaled. -/
def binaryTail (n : ℕ) : ℝ := ∑' k : ℕ, (omegaCount (n + k) : ℝ) / 2 ^ k

private theorem scaled_shift_term (n k : ℕ) :
    (2 : ℝ) ^ n * ((omegaCount (k + n) : ℝ) / 2 ^ (k + n)) =
      (omegaCount (n + k) : ℝ) / 2 ^ k := by
  rw [pow_add, Nat.add_comm k n]
  field_simp

theorem summable_binaryTail (n : ℕ) :
    Summable (fun k : ℕ ↦ (omegaCount (n + k) : ℝ) / 2 ^ k) := by
  have h := ((summable_nat_add_iff n).2 summable_omegaCount_div_two_pow).mul_left
    ((2 : ℝ) ^ n)
  exact h.congr (scaled_shift_term n)

theorem binaryTail_eq_scaled_shift (n : ℕ) :
    binaryTail n = (2 : ℝ) ^ n *
      ∑' k : ℕ, (omegaCount (k + n) : ℝ) / 2 ^ (k + n) := by
  rw [binaryTail, ← tsum_mul_left]
  exact tsum_congr fun k ↦ (scaled_shift_term n k).symm

theorem binaryTail_add_prefix (n : ℕ) :
    (∑ i ∈ Finset.range n, (omegaCount i : ℝ) * 2 ^ (n - i)) + binaryTail n =
      (2 : ℝ) ^ n * binaryOmegaSum := by
  have hsplit := summable_omegaCount_div_two_pow.sum_add_tsum_nat_add n
  have hprefix : (2 : ℝ) ^ n *
      (∑ i ∈ Finset.range n, (omegaCount i : ℝ) / 2 ^ i) =
      ∑ i ∈ Finset.range n, (omegaCount i : ℝ) * 2 ^ (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_sub₀ (2 : ℝ) (by norm_num) (Finset.mem_range.mp hi).le]
    ring
  rw [binaryTail_eq_scaled_shift, ← hprefix, ← mul_add, hsplit, binaryOmegaSum]

/-- The positive-index tail occurring in the irrationality argument. -/
def positiveBinaryTail (n : ℕ) : ℝ := binaryTail n - omegaCount n

theorem positiveBinaryTail_eq_tsum (n : ℕ) :
    positiveBinaryTail n =
      ∑' k : ℕ, (omegaCount (n + (k + 1)) : ℝ) / 2 ^ (k + 1) := by
  have h := (summable_binaryTail n).tsum_eq_zero_add
  simp only [Nat.add_zero, pow_zero, div_one] at h
  change binaryTail n = _ at h
  unfold positiveBinaryTail
  linarith

theorem integer_mul_binaryTail {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (n : ℕ) :
    ∃ t : ℤ, (q : ℝ) * binaryTail n = t := by
  let t : ℤ := (2 : ℤ) ^ n * z -
    (q : ℤ) * ∑ i ∈ Finset.range n, (omegaCount i : ℤ) * 2 ^ (n - i)
  refine ⟨t, ?_⟩
  have hp := congrArg (fun x : ℝ ↦ (q : ℝ) * x) (binaryTail_add_prefix n)
  have hr : (q : ℝ) * ((2 : ℝ) ^ n * binaryOmegaSum) = (2 : ℝ) ^ n * z := by
    rw [mul_left_comm, h]
  rw [hr] at hp
  dsimp [t]
  push_cast
  nlinarith only [hp]

theorem integer_mul_positiveBinaryTail {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (n : ℕ) :
    ∃ t : ℤ, (q : ℝ) * positiveBinaryTail n = t := by
  obtain ⟨t, ht⟩ := integer_mul_binaryTail h n
  refine ⟨t - (q : ℤ) * omegaCount n, ?_⟩
  simp only [positiveBinaryTail, mul_sub, ht, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]

theorem exists_integer_multiple_of_not_irrational
    (h : ¬ Irrational binaryOmegaSum) :
    ∃ q : ℕ, 0 < q ∧ ∃ z : ℤ, (q : ℝ) * binaryOmegaSum = z := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational h
  refine ⟨r.den, r.den_pos, r.num, ?_⟩
  rw [hr, Rat.cast_def]
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
  field_simp

theorem binaryOmegaSum_eq_tsum_from_two :
    binaryOmegaSum =
      ∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2) := by
  have h := summable_omegaCount_div_two_pow.sum_add_tsum_nat_add 2
  simpa [binaryOmegaSum, Finset.sum_range_succ, omegaCount_eq_cardDistinctFactors] using
    h.symm

end

end Erdos69.Elementary

import ErdosProblems.Erdos69.BinarySeries

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable section

def divisibilityTail (p m : ℕ) : ℝ :=
  ∑' k : ℕ, (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)

def compositeCorrection (a m : ℕ) : ℝ := ∑ p ∈ a.primeFactors, divisibilityTail p m

def dilatedPositiveTail (a m : ℕ) : ℝ :=
  ∑' k : ℕ, (omegaCount (a * (m + (k + 1))) : ℝ) / 2 ^ (k + 1)

theorem summable_binary_weights : Summable (fun k : ℕ ↦ (1 : ℝ) / 2 ^ (k + 1)) := by
  simpa [pow_succ', div_mul_eq_div_div] using summable_geometric_two' (1 : ℝ)

theorem tsum_binary_weights : (∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1)) = 1 := by
  simpa [pow_succ', div_mul_eq_div_div] using tsum_geometric_two' (1 : ℝ)

theorem summable_divisibilityTail (p m : ℕ) :
    Summable (fun k : ℕ ↦
      (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)) := by
  apply Summable.of_nonneg_of_le (fun k ↦ by positivity) _ summable_binary_weights
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

theorem divisibilityTail_nonneg (p m : ℕ) : 0 ≤ divisibilityTail p m := by
  unfold divisibilityTail
  exact tsum_nonneg fun k ↦ by positivity

theorem divisibilityTail_le_one (p m : ℕ) : divisibilityTail p m ≤ 1 := by
  rw [← tsum_binary_weights]
  apply Summable.tsum_le_tsum _ (summable_divisibilityTail p m) summable_binary_weights
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

theorem compositeCorrection_nonneg (a m : ℕ) : 0 ≤ compositeCorrection a m := by
  exact Finset.sum_nonneg fun p _ ↦ divisibilityTail_nonneg p m

theorem summable_constant_binary_weights (a : ℝ) :
    Summable (fun k : ℕ ↦ a / 2 ^ (k + 1)) := by
  simpa [pow_succ', div_mul_eq_div_div] using summable_geometric_two' a

theorem tsum_constant_binary_weights (a : ℝ) :
    (∑' k : ℕ, a / 2 ^ (k + 1)) = a := by
  simpa [pow_succ', div_mul_eq_div_div] using tsum_geometric_two' a

theorem summable_positiveBinaryTail (m : ℕ) :
    Summable (fun k : ℕ ↦ (omegaCount (m + (k + 1)) : ℝ) / 2 ^ (k + 1)) :=
  (summable_nat_add_iff 1).2 (summable_binaryTail m)

theorem compositeCorrection_eq_tsum (a m : ℕ) :
    compositeCorrection a m =
      ∑' k : ℕ, ∑ p ∈ a.primeFactors,
        (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
  exact (Summable.tsum_finsetSum fun p _ ↦ summable_divisibilityTail p m).symm

/-- Exact correction formula for an arbitrary positive composite dilation. -/
theorem dilatedPositiveTail_eq {a : ℕ} (ha : a ≠ 0) (m : ℕ) :
    dilatedPositiveTail a m =
      positiveBinaryTail m + omegaCount a - compositeCorrection a m := by
  have hconst := summable_constant_binary_weights (omegaCount a : ℝ)
  have htail := summable_positiveBinaryTail m
  have hcorr := summable_sum (s := a.primeFactors)
    (fun p _ ↦ summable_divisibilityTail p m)
  have hpoint (k : ℕ) :
      (omegaCount (a * (m + (k + 1))) : ℝ) / 2 ^ (k + 1) =
        (omegaCount a : ℝ) / 2 ^ (k + 1) +
          (omegaCount (m + (k + 1)) : ℝ) / 2 ^ (k + 1) -
            ∑ p ∈ a.primeFactors,
              (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
    rw [omegaCount_mul_indicator ha (by omega), sub_div, add_div, Finset.sum_div]
  unfold dilatedPositiveTail
  simp_rw [hpoint]
  rw [(hconst.add htail).tsum_sub hcorr, hconst.tsum_add htail,
    tsum_constant_binary_weights, ← positiveBinaryTail_eq_tsum,
    ← compositeCorrection_eq_tsum]
  ring

theorem summable_dilatedPositiveTail {a : ℕ} (ha : a ≠ 0) (m : ℕ) :
    Summable (fun k : ℕ ↦ (omegaCount (a * (m + (k + 1))) : ℝ) / 2 ^ (k + 1)) := by
  have hconst := summable_constant_binary_weights (omegaCount a : ℝ)
  have htail := summable_positiveBinaryTail m
  have hcorr := summable_sum (s := a.primeFactors)
    (fun p _ ↦ summable_divisibilityTail p m)
  apply ((hconst.add htail).sub hcorr).congr
  intro k
  rw [omegaCount_mul_indicator ha (by omega), sub_div, add_div, Finset.sum_div]

/-- Rationality of the original series gives an integer after adding the
explicit composite correction; primality of the dilation is unnecessary. -/
theorem integer_mul_corrected_dilatedTail {q a : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (ha : a ≠ 0) (m : ℕ) :
    ∃ t : ℤ, (q : ℝ) *
      (dilatedPositiveTail a m + compositeCorrection a m) = t := by
  obtain ⟨t, ht⟩ := integer_mul_positiveBinaryTail h m
  refine ⟨t + (q : ℤ) * omegaCount a, ?_⟩
  rw [dilatedPositiveTail_eq ha, sub_add_cancel, mul_add, ht]
  push_cast
  rfl

end

end Erdos69.Elementary

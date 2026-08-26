import ErdosProblems.Erdos67.StationaryFinitePrimeEnergy

/-! # Grouping the finite correlation energy by prime differences -/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem sum_forward_difference_weights (A : Finset ℕ) (N : ℕ)
    (hA : ∀ a ∈ A, a ≤ N) (g : ℕ → ℝ) :
    (∑ p ∈ A, ∑ q ∈ A, if p ≤ q then g (q - p) else 0) =
      ∑ h ∈ range (N + 1), ((forwardDifferencePairs A h).card : ℝ) * g h := by
  classical
  let S := (A ×ˢ A).filter (fun x ↦ x.1 ≤ x.2)
  have hm : ∀ x ∈ S, x.2 - x.1 ∈ range (N + 1) := by
    intro x hx
    have hq := (mem_product.mp (mem_filter.mp hx).1).2
    exact mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le (hA _ hq)))
  have hf (h : ℕ) : S.filter (fun x ↦ x.2 - x.1 = h) = forwardDifferencePairs A h := by
    ext x
    simp only [S, mem_filter, mem_product, mem_forwardDifferencePairs]
    constructor
    · rintro ⟨⟨⟨hp, hq⟩, hle⟩, he⟩
      exact ⟨hp, hq, by omega⟩
    · rintro ⟨hp, hq, he⟩
      exact ⟨⟨⟨hp, hq⟩, by omega⟩, by omega⟩
  calc
    _ = ∑ x ∈ S, g (x.2 - x.1) := by
      simp only [S, sum_filter, sum_product]
    _ = ∑ h ∈ range (N + 1), ∑ x ∈ S.filter (fun x ↦ x.2 - x.1 = h),
        g (x.2 - x.1) := (sum_fiberwise_of_maps_to hm _).symm
    _ = _ := by
      apply sum_congr rfl
      intro h _
      rw [hf]
      calc
        _ = ∑ _x ∈ forwardDifferencePairs A h, g h := by
          apply sum_congr rfl
          intro x hx
          have hh := (mem_forwardDifferencePairs.mp hx).2.2
          rw [hh, Nat.add_sub_cancel_left]
        _ = _ := by simp

theorem correlation_sum_le_forward_differences (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (A : Finset ℕ) (N d : ℕ) (hA : ∀ a ∈ A, a ≤ N) :
    (∑ p ∈ A, ∑ q ∈ A, correlation Q (((d * p : ℕ) : ℤ) - ((d * q : ℕ) : ℤ))) ≤
      2 * ∑ h ∈ range (N + 1), ((forwardDifferencePairs A h).card : ℝ) *
        |correlation Q ((d * h : ℕ) : ℤ)| := by
  let g : ℕ → ℝ := fun h ↦ |correlation Q ((d * h : ℕ) : ℤ)|
  have hpoint (p q : ℕ) :
      correlation Q (((d * p : ℕ) : ℤ) - ((d * q : ℕ) : ℤ)) ≤
        (if p ≤ q then g (q - p) else 0) + (if q ≤ p then g (p - q) else 0) := by
    by_cases hpq : p ≤ q
    · have he : (((d * p : ℕ) : ℤ) - ((d * q : ℕ) : ℤ)) = -((d * (q - p) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hpq]
        ring
      rw [he, correlation_neg_nat Q hQ, if_pos hpq]
      have hn : 0 ≤ (if q ≤ p then g (p - q) else 0) := by split_ifs <;> positivity
      exact (le_abs_self _).trans (le_add_of_nonneg_right hn)
    · have hqp : q ≤ p := le_of_lt (lt_of_not_ge hpq)
      have he : (((d * p : ℕ) : ℤ) - ((d * q : ℕ) : ℤ)) = ((d * (p - q) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hqp]
        ring
      rw [he, if_neg hpq, if_pos hqp, zero_add]
      exact le_abs_self _
  calc
    _ ≤ ∑ p ∈ A, ∑ q ∈ A,
        ((if p ≤ q then g (q - p) else 0) + (if q ≤ p then g (p - q) else 0)) := by
      exact sum_le_sum fun p _ ↦ sum_le_sum fun q _ ↦ hpoint p q
    _ = 2 * (∑ p ∈ A, ∑ q ∈ A, if p ≤ q then g (q - p) else 0) := by
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun p q ↦ if q ≤ p then g (p - q) else 0)]
      ring
    _ = _ := by rw [sum_forward_difference_weights A N hA g]

theorem prime_correlation_fourth_power_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (P d : ℕ) :
    (∑ p ∈ Nat.primesLE (2 * P), correlation Q ((d * p : ℕ) : ℤ)) ^ 4 ≤
      4 * (∑ h ∈ range (2 * P + 1),
        ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ) ^ 2) *
      (∑ h ∈ range (2 * P + 1), correlation Q ((d * h : ℕ) : ℤ) ^ 2) := by
  have hfirst := finite_correlation_sum_square_le Q hQ (Nat.primesLE (2 * P)) d
  have hsecond := correlation_sum_le_forward_differences Q hQ (Nat.primesLE (2 * P))
    (2 * P) d (fun p hp ↦ (Nat.mem_primesLE.mp hp).1)
  have hcs := sum_mul_sq_le_sq_mul_sq (range (2 * P + 1))
    (fun h ↦ ((forwardDifferencePairs (Nat.primesLE (2 * P)) h).card : ℝ))
    (fun h ↦ |correlation Q ((d * h : ℕ) : ℤ)|)
  simp only [sq_abs] at hcs
  have hs := pow_le_pow_left₀ (sq_nonneg _) (hfirst.trans hsecond) 2
  nlinarith only [hs, hcs]

end Erdos67.StationaryModel

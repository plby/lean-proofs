import ErdosProblems.Erdos587.FrequencyWeights

/-! A nonnegative series is bounded by one prefix and its summable tail. -/

open scoped BigOperators

namespace Erdos587

lemma sum_range_le_prefix_add_tail (f : ℕ → ℝ) (N K : ℕ) (hf : ∀ n, 0 ≤ f n)
    (htail : Summable (fun n => if N < n + 1 then f n else 0)) :
    (∑ n ∈ Finset.range K, f n) ≤
      (∑ n ∈ Finset.range N, f n) + ∑' n : ℕ, if N < n + 1 then f n else 0 := by
  classical
  have hsplit : (∑ n ∈ Finset.range K, f n) =
      (∑ n ∈ Finset.range K, if n < N then f n else 0) +
        ∑ n ∈ Finset.range K, if N < n + 1 then f n else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n < N
    · simp only [if_pos h, if_neg (by omega : ¬ N < n + 1), add_zero]
    · simp only [if_neg h, if_pos (by omega : N < n + 1), zero_add]
  rw [hsplit]
  apply add_le_add
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    · intro n hn hnot
      exact hf n
  · exact htail.sum_le_tsum (Finset.range K) (fun n hn => by split_ifs <;> simp [hf])

theorem summable_and_tsum_le_prefix_add_tail (f : ℕ → ℝ) (N : ℕ) (hf : ∀ n, 0 ≤ f n)
    (htail : Summable (fun n => if N < n + 1 then f n else 0)) :
    Summable f ∧ (∑' n, f n) ≤
      (∑ n ∈ Finset.range N, f n) + ∑' n : ℕ, if N < n + 1 then f n else 0 := by
  have hb := sum_range_le_prefix_add_tail f N
  exact ⟨summable_of_sum_range_le hf (fun K => hb K hf htail),
    Real.tsum_le_of_sum_range_le hf (fun K => hb K hf htail)⟩

end Erdos587

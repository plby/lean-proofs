import ErdosProblems.Erdos587.HooleyApproximationSmallShell

/-! # Short signed error intervals, including a possible zero error -/

open scoped BigOperators

namespace Erdos587

lemma delta_int_card_le_two_mul_add_one (E : Finset ℤ) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ E, |(t : ℝ)| ≤ T) : (E.card : ℝ) ≤ 2 * T + 1 := by
  have hzero : ∀ t ∈ E.erase 0, t ≠ 0 := fun t ht => (Finset.mem_erase.mp ht).1
  have hbounds (t : ℤ) (ht : t ∈ E.erase 0) : (t.natAbs : ℝ) ≤ T := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hbound t (Finset.mem_of_mem_erase ht)
  have h := delta_nonzero_int_card_le_two_mul (E.erase 0) hT hzero hbounds
  have hcard : E.card ≤ (E.erase 0).card + 1 := by
    by_cases hzero : 0 ∈ E
    · exact (Finset.card_erase_add_one hzero).symm.le
    · rw [Finset.erase_eq_of_notMem hzero]
      omega
  have hcardR : (E.card : ℝ) ≤ (E.erase 0).card + 1 := by exact_mod_cast hcard
  linarith

theorem exists_delta_pointwise_subpower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (hooleyDelta n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hdiv⟩ := Erdos1148.DukeArithmetic.exists_card_divisors_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [hooleyDelta_zero, Nat.cast_zero]
    positivity
  · exact (show (hooleyDelta n : ℝ) ≤ n.divisors.card by
      exact_mod_cast hooleyDelta_le_card_divisors n).trans (hdiv n hn)

theorem exists_delta_sparse_error_mean {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ) (X : ℕ) (T : ℝ), 0 ≤ T →
      ∀ E : Finset ℤ, (∀ t ∈ E, |(t : ℝ)| ≤ T) →
      (∀ t ∈ E, (A + B * t).natAbs ≤ X) →
      (∑ t ∈ E, (hooleyDelta (A + B * t).natAbs : ℝ)) ≤ C * (2 * T + 1) * (X : ℝ) ^ ε := by
  obtain ⟨C, hC, hpoint⟩ := exists_delta_pointwise_subpower_bound hε
  refine ⟨C, hC, ?_⟩
  intro A B X T hT E hbound hvalue
  have hcard := delta_int_card_le_two_mul_add_one E hT hbound
  have hvalues (t : ℤ) (ht : t ∈ E) : (hooleyDelta (A + B * t).natAbs : ℝ) ≤ C * (X : ℝ) ^ ε := by
    apply (hpoint _).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hvalue t ht) hε.le) hC.le
  calc
    _ ≤ ∑ _t ∈ E, C * (X : ℝ) ^ ε := Finset.sum_le_sum hvalues
    _ = (E.card : ℝ) * (C * (X : ℝ) ^ ε) := by simp
    _ ≤ (2 * T + 1) * (C * (X : ℝ) ^ ε) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end Erdos587

import ErdosProblems.Erdos321.UniformDepthUpperTerms

namespace Erdos321

/-- The unexpanded remainder after `d` applications of the positive operator. -/
noncomputable def adaptiveNeumannRemainder (A : ℕ) : ℕ → ℕ → ℝ
  | 0, n => adaptiveNeumannModel A n
  | d + 1, n => truncatedLogOperator A (adaptiveNeumannRemainder A d)
      (safeAdaptiveEndpoint n)

/-- The stopped model obeys its source-plus-operator equation for every natural
argument, including below the stopping threshold. -/
theorem adaptiveNeumannModel_eq_one_add_safe_total
    {A n : ℕ} (hA : 1 ≤ A) :
    adaptiveNeumannModel A n = 1 +
      truncatedLogOperator A (adaptiveNeumannModel A)
        (safeAdaptiveEndpoint n) := by
  by_cases hnA : A ≤ n
  · have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < A) hnA
    exact adaptiveNeumannModel_eq_safe hnA hnpos
  · have hnlt : n < A := by omega
    rw [adaptiveNeumannModel_eq_one hnlt]
    have hsA : safeAdaptiveEndpoint n < A := by
      have hs : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
      exact lt_of_le_of_lt (hs.trans (Nat.sub_le n 1)) hnlt
    have hempty : Finset.Icc A (safeAdaptiveEndpoint n) = ∅ := by
      ext t
      simp only [Finset.mem_Icc]
      constructor
      · intro ht
        exfalso
        omega
      · intro ht
        simp at ht
    simp [truncatedLogOperator, hempty]

/-- Every remainder splits into the term at its current depth and the next
remainder. -/
theorem adaptiveNeumannRemainder_split
    {A : ℕ} (hA : 1 ≤ A) (d n : ℕ) :
    adaptiveNeumannRemainder A d n =
      adaptiveNeumannTerm A d n + adaptiveNeumannRemainder A (d + 1) n := by
  induction d generalizing n with
  | zero =>
      simpa [adaptiveNeumannRemainder, adaptiveNeumannTerm] using
        adaptiveNeumannModel_eq_one_add_safe_total (A := A) (n := n) hA
  | succ d ih =>
      change truncatedLogOperator A (adaptiveNeumannRemainder A d)
          (safeAdaptiveEndpoint n) =
        truncatedLogOperator A (adaptiveNeumannTerm A d)
            (safeAdaptiveEndpoint n) +
          truncatedLogOperator A (adaptiveNeumannRemainder A (d + 1))
            (safeAdaptiveEndpoint n)
      dsimp [truncatedLogOperator]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      rw [ih t]
      ring

/-- Exact finite expansion with a single positive unexpanded remainder. -/
theorem adaptiveNeumannModel_eq_sum_terms_add_remainder
    {A : ℕ} (hA : 1 ≤ A) (d n : ℕ) :
    adaptiveNeumannModel A n =
      (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) +
        adaptiveNeumannRemainder A d n := by
  induction d with
  | zero => simp [adaptiveNeumannRemainder]
  | succ d ih =>
      rw [Finset.sum_range_succ]
      calc
        adaptiveNeumannModel A n =
            (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) +
              adaptiveNeumannRemainder A d n := ih
        _ = (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) +
              (adaptiveNeumannTerm A d n +
                adaptiveNeumannRemainder A (d + 1) n) := by
                  rw [adaptiveNeumannRemainder_split hA d n]
        _ = ((∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) +
              adaptiveNeumannTerm A d n) +
                adaptiveNeumannRemainder A (d + 1) n := by ring

/-- Every remainder is nonnegative. -/
theorem adaptiveNeumannRemainder_nonneg
    {A : ℕ} (hA : 2 ≤ A) (d n : ℕ) :
    0 ≤ adaptiveNeumannRemainder A d n := by
  induction d generalizing n with
  | zero =>
      exact (by norm_num : (0 : ℝ) ≤ 1).trans
        (one_le_adaptiveNeumannModel hA n)
  | succ d ih =>
      dsimp [adaptiveNeumannRemainder, truncatedLogOperator]
      apply Finset.sum_nonneg
      intro t ht
      have htA := (Finset.mem_Icc.mp ht).1
      have hlog : 0 < Real.log (t : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < t by omega))
      exact div_nonneg (ih t) (mul_pos (by positivity) hlog).le

end Erdos321

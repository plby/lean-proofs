import ErdosProblems.Erdos321.IteratedLogProduct

namespace Erdos321

/-- The depth-`k` term in the finite positive Neumann expansion. -/
noncomputable def adaptiveNeumannTerm (A : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, n =>
      truncatedLogOperator A (adaptiveNeumannTerm A k) (safeAdaptiveEndpoint n)

@[simp] theorem adaptiveNeumannTerm_zero (A n : ℕ) :
    adaptiveNeumannTerm A 0 n = 1 := rfl

@[simp] theorem adaptiveNeumannTerm_succ (A k n : ℕ) :
    adaptiveNeumannTerm A (k + 1) n =
      truncatedLogOperator A (adaptiveNeumannTerm A k)
        (safeAdaptiveEndpoint n) := rfl

/-- A depth exceeding the natural argument cannot occur. -/
theorem adaptiveNeumannTerm_eq_zero_of_lt_depth
    {A k n : ℕ} (hA : 1 ≤ A) (hnk : n < k) :
    adaptiveNeumannTerm A k n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      rw [adaptiveNeumannTerm_succ]
      dsimp [truncatedLogOperator]
      apply Finset.sum_eq_zero
      intro t ht
      have htmem := Finset.mem_Icc.mp ht
      have hsafe : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
      have hnpos : 0 < n := by
        by_contra hn0
        have hnzero : n = 0 := by omega
        subst n
        simp [safeAdaptiveEndpoint] at htmem
        omega
      have htn : t < n := by omega
      have htk : t < k := by omega
      rw [ih htk]
      simp

/-- Every finite-depth term is nonnegative. -/
theorem adaptiveNeumannTerm_nonneg
    {A : ℕ} (hA : 2 ≤ A) (k n : ℕ) :
    0 ≤ adaptiveNeumannTerm A k n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [adaptiveNeumannTerm_succ]
      dsimp [truncatedLogOperator]
      apply Finset.sum_nonneg
      intro t ht
      have htA := (Finset.mem_Icc.mp ht).1
      have hlog : 0 < Real.log (t : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < t by omega))
      exact div_nonneg (ih t) (mul_pos (by positivity) hlog).le

/-- Below the stopping threshold, every positive-depth term vanishes. -/
theorem adaptiveNeumannTerm_succ_eq_zero_of_lt_threshold
    {A k n : ℕ} (hnA : n < A) :
    adaptiveNeumannTerm A (k + 1) n = 0 := by
  rw [adaptiveNeumannTerm_succ]
  dsimp [truncatedLogOperator]
  apply Finset.sum_eq_zero
  intro t ht
  have htmem := Finset.mem_Icc.mp ht
  have hsafe : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
  exfalso
  omega

/-- Padding the depth sum past the argument adds only zero terms. -/
theorem adaptiveNeumannTerm_sum_pad
    {A m n : ℕ} (hA : 1 ≤ A) (hmn : m + 1 ≤ n) :
    (∑ k ∈ Finset.range (m + 1), adaptiveNeumannTerm A k m) =
      ∑ k ∈ Finset.range n, adaptiveNeumannTerm A k m := by
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro k hkn hkm
  have hmk : m < k := by
    simp only [Finset.mem_range] at hkn
    simp only [Finset.mem_range, not_lt] at hkm
    omega
  exact adaptiveNeumannTerm_eq_zero_of_lt_depth hA hmk

/-- Exact finite Neumann expansion of the stopped model.  There are no terms
beyond depth `n`, since every recursion edge strictly decreases its argument. -/
theorem adaptiveNeumannModel_eq_sum_terms
    {A n : ℕ} (hA : 2 ≤ A) :
    adaptiveNeumannModel A n =
      ∑ k ∈ Finset.range (n + 1), adaptiveNeumannTerm A k n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnA : n < A
      · rw [adaptiveNeumannModel_eq_one hnA, Finset.sum_range_succ']
        simp only [adaptiveNeumannTerm_zero]
        have hz : (∑ k ∈ Finset.range n,
            adaptiveNeumannTerm A (k + 1) n) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          exact adaptiveNeumannTerm_succ_eq_zero_of_lt_threshold hnA
        rw [hz]
        norm_num
      · have hAn : A ≤ n := by omega
        have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < A) hAn
        rw [adaptiveNeumannModel_eq_safe hAn hnpos, Finset.sum_range_succ']
        simp only [adaptiveNeumannTerm_zero]
        rw [add_comm _ (1 : ℝ)]
        congr 1
        dsimp [truncatedLogOperator]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t ht
        have hsafe : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
        have htn : t < n := by
          have := (Finset.mem_Icc.mp ht).2
          omega
        have hMt := ih t htn
        have hpad := adaptiveNeumannTerm_sum_pad (show 1 ≤ A by omega)
          (show t + 1 ≤ n by omega)
        rw [hMt, hpad, Finset.sum_div]

end Erdos321

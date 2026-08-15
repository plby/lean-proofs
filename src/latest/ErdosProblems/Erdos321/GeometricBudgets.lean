import ErdosProblems.Erdos321.NeumannTerms

namespace Erdos321

/-- Exact partial sum for the geometric block fractions
`2^{-(r+2)}`. -/
theorem blockFraction_sum_eq (k : ℕ) :
    (∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 2)) =
      1 / 2 - 1 / (2 : ℝ) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show k + 1 + 1 = k + 2 by omega]
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring

/-- The total budget of all geometric block fractions is at most one half. -/
theorem blockFraction_sum_le_half (k : ℕ) :
    (∑ r ∈ Finset.range k, 1 / (2 : ℝ) ^ (r + 2)) ≤ 1 / 2 := by
  rw [blockFraction_sum_eq]
  have hnonneg : 0 ≤ 1 / (2 : ℝ) ^ (k + 1) := by positivity
  linarith

/-- Exact arithmetico-geometric partial sum used for shifted-coordinate
errors. -/
theorem weighted_geometric_sum_eq (k : ℕ) :
    (∑ r ∈ Finset.range k, ((r : ℝ) + 3) / (2 : ℝ) ^ r) =
      8 - (2 * (k : ℝ) + 8) / (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

/-- Uniform bound for the shifted-coordinate error series. -/
theorem weighted_geometric_sum_le_eight (k : ℕ) :
    (∑ r ∈ Finset.range k, ((r : ℝ) + 3) / (2 : ℝ) ^ r) ≤ 8 := by
  rw [weighted_geometric_sum_eq]
  have hnonneg : 0 ≤ (2 * (k : ℝ) + 8) / (2 : ℝ) ^ k := by positivity
  linarith

/-- A finite product of factors `1-eᵢ` loses at most the sum of nonnegative
errors `eᵢ`. -/
theorem one_sub_sum_le_prod_one_sub
    {s : Finset ℕ} {e : ℕ → ℝ}
    (he0 : ∀ i ∈ s, 0 ≤ e i) (he1 : ∀ i ∈ s, e i ≤ 1) :
    1 - ∑ i ∈ s, e i ≤ ∏ i ∈ s, (1 - e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have ha0 := he0 a (Finset.mem_insert_self a s)
      have ha1 := he1 a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∑ i ∈ s, e i := Finset.sum_nonneg fun i hi =>
        he0 i (Finset.mem_insert_of_mem hi)
      have hih := ih
        (fun i hi => he0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => he1 i (Finset.mem_insert_of_mem hi))
      have hfac : 0 ≤ 1 - e a := by linarith
      have hmul := mul_le_mul_of_nonneg_right hih hfac
      calc
        1 - (e a + ∑ i ∈ s, e i) ≤
            (1 - ∑ i ∈ s, e i) * (1 - e a) := by nlinarith
        _ ≤ (∏ i ∈ s, (1 - e i)) * (1 - e a) := hmul
        _ = (1 - e a) * ∏ i ∈ s, (1 - e i) := by ring

end Erdos321

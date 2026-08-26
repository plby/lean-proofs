import ErdosProblems.Erdos547.RegularityManyTypical

/-!
# Finite weighted choices and the quadratic potential identity

These are finite-sum statements; no measure or probabilistic input is assumed.
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem exists_positive_weight_le_mean (p f : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) :
    ∃ i, 0 < p i ∧ f i ≤ ∑ j, p j * f j := by
  classical
  have hne : ((Finset.univ : Finset I).filter (fun i ↦ 0 < p i)).Nonempty := by
    by_contra hn
    have hpzero (i : I) : p i = 0 := by
      apply le_antisymm _ (hp i)
      by_contra hi
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hi⟩⟩
    simp only [hpzero, Finset.sum_const_zero, zero_ne_one] at hmass
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ f hne
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  calc
    f i = ∑ j, p j * f i := by rw [← Finset.sum_mul, hmass, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : 0 < p j
      · exact mul_le_mul_of_nonneg_left
          (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)) (hp j)
      · have hz : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
        simp only [hz, zero_mul, le_refl]

theorem weighted_shift_square (p b : I → ℝ) (x : ℝ)
    (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i * b i = 0) :
    (∑ i, p i * (x + b i) ^ 2) = x ^ 2 + ∑ i, p i * (b i) ^ 2 := by
  calc
    _ = (∑ i, p i) * x ^ 2 + 2 * x * (∑ i, p i * b i) +
        ∑ i, p i * (b i) ^ 2 := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hmass, hmean]; ring

theorem weighted_vector_shift_square (p : I → ℝ) (b : I → J → ℝ) (x : J → ℝ)
    (hmass : ∑ i, p i = 1) (hmean : ∀ j, ∑ i, p i * b i j = 0) :
    (∑ i, p i * ∑ j, (x j + b i j) ^ 2) =
      (∑ j, (x j) ^ 2) + ∑ j, ∑ i, p i * (b i j) ^ 2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [weighted_shift_square p _ _ hmass (hmean _)]
  exact Finset.sum_add_distrib

theorem weighted_centered_mean (p a : I → ℝ) (hmass : ∑ i, p i = 1) :
    (∑ i, p i * (a i - ∑ j, p j * a j)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul, sub_self]

theorem weighted_centered_square_le (p a : I → ℝ) (hmass : ∑ i, p i = 1) :
    (∑ i, p i * (a i - ∑ j, p j * a j) ^ 2) ≤ ∑ i, p i * (a i) ^ 2 := by
  have hh := weighted_shift_square p (fun i ↦ a i - ∑ j, p j * a j)
    (∑ j, p j * a j) hmass (weighted_centered_mean p a hmass)
  have hcancel (i : I) : (∑ j, p j * a j) + (a i - ∑ j, p j * a j) = a i := by ring
  simp only [hcancel] at hh
  linarith only [hh, sq_nonneg (∑ j, p j * a j)]

end Erdos547

#print axioms Erdos547.exists_positive_weight_le_mean
#print axioms Erdos547.weighted_vector_shift_square

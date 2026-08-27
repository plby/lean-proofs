import Mathlib

/-! # Finite cover summation for the short-progression ranges -/

open scoped BigOperators

namespace Erdos587

lemma delta_sum_indicator_of_subset (S T : Finset ℕ) (hT : T ⊆ S) (f : ℕ → ℝ) :
    (∑ n ∈ S, if n ∈ T then f n else 0) = ∑ n ∈ T, f n := by
  classical
  calc
    _ = ∑ n ∈ T, if n ∈ T then f n else 0 := by
      symm
      apply Finset.sum_subset hT
      intro n hn hnot
      simp only [if_neg hnot]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos hn]

lemma delta_sum_cover_three_le (S S₀ S₁ J : Finset ℕ) (F : ℕ → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hS₀ : S₀ ⊆ S) (hS₁ : S₁ ⊆ S)
    (hF : ∀ j ∈ J, F j ⊆ S)
    (hcover : ∀ n ∈ S, n ∈ S₀ ∨ n ∈ S₁ ∨ ∃ j ∈ J, n ∈ F j) :
    (∑ n ∈ S, f n) ≤ (∑ n ∈ S₀, f n) + (∑ n ∈ S₁, f n) +
      ∑ j ∈ J, ∑ n ∈ F j, f n := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ S) : f n ≤
      (if n ∈ S₀ then f n else 0) + (if n ∈ S₁ then f n else 0) +
        ∑ j ∈ J, if n ∈ F j then f n else 0 := by
    have hfn := hf n
    have h₀ : 0 ≤ if n ∈ S₀ then f n else 0 := by split_ifs <;> positivity
    have h₁ : 0 ≤ if n ∈ S₁ then f n else 0 := by split_ifs <;> positivity
    have hsum : 0 ≤ ∑ j ∈ J, if n ∈ F j then f n else 0 :=
      Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
    rcases hcover n hn with h | h | ⟨j, hj, hnj⟩
    · rw [if_pos h]
      linarith
    · rw [if_pos h]
      linarith
    · have hsingle := Finset.single_le_sum (s := J)
        (f := fun j => if n ∈ F j then f n else 0)
        (fun j _ => by split_ifs <;> positivity) hj
      rw [if_pos hnj] at hsingle
      linarith
  calc
    _ ≤ ∑ n ∈ S, ((if n ∈ S₀ then f n else 0) + (if n ∈ S₁ then f n else 0) +
        ∑ j ∈ J, if n ∈ F j then f n else 0) := Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        delta_sum_indicator_of_subset S S₀ hS₀ f, delta_sum_indicator_of_subset S S₁ hS₁ f,
        Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact delta_sum_indicator_of_subset S (F j) (hF j hj) f

lemma delta_sum_exp_neg_le_two (J : ℕ) :
    (∑ j ∈ Finset.range J, Real.exp (-(j : ℝ))) ≤ 2 := by
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hexp : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hexp1
  calc
    _ ≤ ∑ j ∈ Finset.range J, (1 / (2 : ℝ)) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [show -(j : ℝ) = (j : ℝ) * (-1) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_nonneg _) hexp j
    _ ≤ 2 := sum_geometric_two_le J

end Erdos587

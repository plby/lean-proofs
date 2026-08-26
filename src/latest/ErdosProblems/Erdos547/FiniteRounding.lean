import ErdosProblems.Erdos547.FiniteQuadraticChoice

/-!
# Rounding finite assignments with simultaneous bounds on all loads
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

theorem exists_choices_sq_error_le (S : Finset F) (p : F → I → ℝ) (a : F → I → J → ℝ)
    (hp : ∀ x i, 0 ≤ p x i) (hmass : ∀ x, ∑ i, p x i = 1) :
    ∃ f : F → I, (∀ x ∈ S, 0 < p x (f x)) ∧
      (∑ j, ((∑ x ∈ S, a x (f x) j) - ∑ x ∈ S, ∑ i, p x i * a x i j) ^ 2) ≤
        ∑ x ∈ S, ∑ j, ∑ i, p x i * (a x i j) ^ 2 := by
  let b : F → I → J → ℝ := fun x i j ↦ a x i j - ∑ l, p x l * a x l j
  have hmean (x : F) (j : J) : ∑ i, p x i * b x i j = 0 :=
    weighted_centered_mean (p x) (fun i ↦ a x i j) (hmass x)
  obtain ⟨f, hf, hbound⟩ := exists_choices_sq_sum_le S p b hp hmass hmean
  refine ⟨f, hf, ?_⟩
  have hmoment : (∑ x ∈ S, ∑ j, ∑ i, p x i * (b x i j) ^ 2) ≤
      ∑ x ∈ S, ∑ j, ∑ i, p x i * (a x i j) ^ 2 := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro j _
    exact weighted_centered_square_le (p x) (fun i ↦ a x i j) (hmass x)
  simpa only [b, Finset.sum_sub_distrib] using hbound.trans hmoment

theorem exists_choices_load_lt (S : Finset F) (p : F → I → ℝ) (a : F → I → J → ℝ)
    (hp : ∀ x i, 0 ≤ p x i) (hmass : ∀ x, ∑ i, p x i = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hmoment : (∑ x ∈ S, ∑ j, ∑ i, p x i * (a x i j) ^ 2) < C ^ 2) :
    ∃ f : F → I, (∀ x ∈ S, 0 < p x (f x)) ∧
      ∀ j, (∑ x ∈ S, a x (f x) j) < (∑ x ∈ S, ∑ i, p x i * a x i j) + C := by
  obtain ⟨f, hf, hbound⟩ := exists_choices_sq_error_le S p a hp hmass
  refine ⟨f, hf, ?_⟩
  intro j
  have hj : ((∑ x ∈ S, a x (f x) j) - ∑ x ∈ S, ∑ i, p x i * a x i j) ^ 2 ≤
      ∑ l, ((∑ x ∈ S, a x (f x) l) - ∑ x ∈ S, ∑ i, p x i * a x i l) ^ 2 :=
    Finset.single_le_sum
      (fun l _ ↦ sq_nonneg ((∑ x ∈ S, a x (f x) l) - ∑ x ∈ S, ∑ i, p x i * a x i l))
      (Finset.mem_univ j)
  have hsq := (hj.trans hbound).trans_lt hmoment
  by_contra hn
  have hdiff : C ≤ (∑ x ∈ S, a x (f x) j) - ∑ x ∈ S, ∑ i, p x i * a x i j := by
    linarith only [le_of_not_gt hn]
  nlinarith only [hsq, hdiff, hC]

end Erdos547

#print axioms Erdos547.exists_choices_load_lt

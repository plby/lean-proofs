import ErdosProblems.Erdos547.FiniteVariance

/-!
# Simultaneous finite choices controlled by a quadratic potential
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

theorem exists_choices_sq_sum_le (S : Finset F) (p : F → I → ℝ) (b : F → I → J → ℝ)
    (hp : ∀ x i, 0 ≤ p x i) (hmass : ∀ x, ∑ i, p x i = 1)
    (hmean : ∀ x j, ∑ i, p x i * b x i j = 0) :
    ∃ f : F → I, (∀ x ∈ S, 0 < p x (f x)) ∧
      (∑ j, (∑ x ∈ S, b x (f x) j) ^ 2) ≤
        ∑ x ∈ S, ∑ j, ∑ i, p x i * (b x i j) ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun _ ↦ Classical.choice ‹Nonempty I›, by simp, by simp⟩
  | @insert x S hx ih =>
    obtain ⟨f, hf, hquad⟩ := ih
    let z : J → ℝ := fun j ↦ ∑ y ∈ S, b y (f y) j
    obtain ⟨i, hi, hchoice⟩ := exists_positive_weight_le_mean (p x)
      (fun i ↦ ∑ j, (z j + b x i j) ^ 2) (hp x) (hmass x)
    rw [weighted_vector_shift_square (p x) (b x) z (hmass x) (hmean x)] at hchoice
    let g : F → I := Function.update f x i
    have hgx : g x = i := by simp [g]
    have hgy (y : F) (hy : y ∈ S) : g y = f y := by
      have hne : y ≠ x := fun he ↦ hx (he ▸ hy)
      exact Function.update_of_ne hne i f
    refine ⟨g, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyS
      · rwa [hgx]
      · rw [hgy y hyS]
        exact hf y hyS
    · have hsum (j : J) : (∑ y ∈ insert x S, b y (g y) j) = z j + b x i j := by
        rw [Finset.sum_insert hx, hgx]
        have hs : (∑ y ∈ S, b y (g y) j) = z j := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hgy y hy]
        rw [hs]
        ring
      simp only [hsum, Finset.sum_insert hx]
      change (∑ j, (z j + b x i j) ^ 2) ≤
        (∑ j, ∑ i, p x i * (b x i j) ^ 2) +
          ∑ y ∈ S, ∑ j, ∑ i, p y i * (b y i j) ^ 2
      change (∑ j, (z j) ^ 2) ≤ ∑ y ∈ S, ∑ j, ∑ i, p y i * (b y i j) ^ 2 at hquad
      linarith only [hchoice, hquad]

end Erdos547

#print axioms Erdos547.exists_choices_sq_sum_le

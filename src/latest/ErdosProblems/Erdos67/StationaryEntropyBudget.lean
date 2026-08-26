import ErdosProblems.Erdos67.StationaryConditionalEntropy

/-!
# Conditional exponential estimates and finite entropy budgets

This file proves the finite variational estimate and telescoping calculation
used in the stationary proof. No stationary or number-theoretic result is assumed
as an axiom or asserted by this module.
-/

open scoped BigOperators
open Finset

namespace Erdos67.FiniteEntropy

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Mutual information of the first two coordinates, conditional on the third. -/
noncomputable def conditionalMutualInfo (p : FinProb ((α × β) × γ)) : ℝ :=
  ∑ c, sndMarginal p c * mutualInfo (conditionalLaw p c)

theorem conditionalMutualInfo_nonneg (p : FinProb ((α × β) × γ)) :
    0 ≤ conditionalMutualInfo p := by
  exact Finset.sum_nonneg fun c _ ↦
    mul_nonneg (prob_nonneg (sndMarginal p) c) (mutualInfo_nonneg (conditionalLaw p c))

theorem conditionalMutualInfo_eq_condEntropy (p : FinProb ((α × β) × γ)) :
    conditionalMutualInfo p = condEntropy (mapLeft p Prod.fst) +
      condEntropy (mapLeft p Prod.snd) - condEntropy p := by
  simp only [conditionalMutualInfo, condEntropy_eq_weighted_conditional,
    sndMarginal_mapLeft, conditionalLaw_map_fst, conditionalLaw_map_snd,
    mutualInfo, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Averaging conditional expectations recovers the expectation of a joint law. -/
theorem expectation_eq_weighted_conditional (p : FinProb (α × β)) (F : α → β → ℝ) :
    (∑ z, p z * F z.1 z.2) =
      ∑ b, sndMarginal p b * ∑ a, conditionalLaw p b a * F a b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [joint_eq_marginal_mul_conditional p a b, mul_assoc]

/-- The conditional variational bound. Zero-probability conditioning values
require no exponential-moment estimate. -/
theorem conditional_expectation_le_mutualInfo_add
    (p : FinProb ((α × β) × γ)) (F : α → β → γ → ℝ) (K : ℝ)
    (hF : ∀ c, 0 < sndMarginal p c → ∀ a,
      (∑ b, sndMarginal (conditionalLaw p c) b * Real.exp (F a b c)) ≤ Real.exp K) :
    (∑ z, p z * F z.1.1 z.1.2 z.2) ≤ conditionalMutualInfo p + K := by
  rw [expectation_eq_weighted_conditional p (fun ab c ↦ F ab.1 ab.2 c)]
  calc
    (∑ c, sndMarginal p c * ∑ ab, conditionalLaw p c ab * F ab.1 ab.2 c) ≤
        ∑ c, sndMarginal p c * (mutualInfo (conditionalLaw p c) + K) := by
      apply Finset.sum_le_sum
      intro c _
      rcases (prob_nonneg (sndMarginal p) c).eq_or_lt with hc | hc
      · rw [← hc, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left
          (joint_expectation_le_mutualInfo_add (conditionalLaw p c)
            (fun a b ↦ F a b c) K (hF c hc)) hc.le
    _ = conditionalMutualInfo p + K := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        stdSimplex.sum_eq_one, one_mul, conditionalMutualInfo]

/-- The numerical entropy cost used for each dyadic block of primes. -/
theorem square_error_le_eighteen_conditionalMutualInfo
    (p : FinProb ((α × β) × γ)) (F : α → β → γ → ℝ) (S : ℝ)
    (hmean : (∑ z, p z * F z.1.1 z.1.2 z.2) = S)
    (hmgf : ∀ c, 0 < sndMarginal p c → ∀ a,
      (∑ b, sndMarginal (conditionalLaw p c) b * Real.exp (F a b c / 9)) ≤
        Real.exp (S / 18)) :
    S ≤ 18 * conditionalMutualInfo p := by
  have h := conditional_expectation_le_mutualInfo_add p
    (fun a b c ↦ F a b c / 9) (S / 18) hmgf
  have he : (∑ z, p z * (F z.1.1 z.1.2 z.2 / 9)) = S / 9 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, hmean]
  rw [he] at h
  linarith

end Erdos67.FiniteEntropy

namespace Erdos67.StationaryEntropyBudget

/-- Telescoping a nonnegative information loss, retaining the terminal entropy. -/
theorem sum_le_initial_sub_terminal (u a : ℕ → ℝ)
    (hstep : ∀ n, u (n + 1) ≤ u n - a n) (N : ℕ) :
    (∑ n ∈ range N, a n) ≤ u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep N]

theorem sum_le_initial (u a : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hstep : ∀ n, u (n + 1) ≤ u n - a n) (N : ℕ) :
    (∑ n ∈ range N, a n) ≤ u 0 :=
  (sum_le_initial_sub_terminal u a hstep N).trans (sub_le_self _ (hu N))

/-- The finite dyadic information budget. -/
theorem dyadic_information_sum_le (u I : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, u (n + 1) ≤ u n - I n / (2 : ℝ) ^ n) (N : ℕ) :
    (∑ n ∈ range N, I n / (2 : ℝ) ^ n) ≤ u 0 :=
  sum_le_initial u (fun n ↦ I n / (2 : ℝ) ^ n) hu hstep N

end Erdos67.StationaryEntropyBudget

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib

/-!
# Finite probability tools for Erdős Problem 182

The probabilistic arguments used in the regular-subgraph proof have finite sample
spaces.  This file records them as finite sums.  In particular, it supplies a
Bernoulli law on `Finset α`, exact first-moment identities, Markov's inequality,
and the elementary principle that some outcome attains at least the weighted
average.
-/

namespace Erdos182

open scoped BigOperators NNReal

noncomputable section

section WeightedFiniteSpace

variable {Ω : Type*} [Fintype Ω]

/-- The mass of a decidable event in a finite weighted space. -/
def weightedProbability (weight : Ω → ℝ≥0) (P : Ω → Prop) : ℝ≥0 := by
  classical
  exact ∑ ω, if P ω then weight ω else 0

/-- Event mass as a sum over the filtered sample space. -/
theorem weightedProbability_eq_filter (weight : Ω → ℝ≥0) (P : Ω → Prop)
    [DecidablePred P] :
    weightedProbability weight P =
      ∑ ω ∈ Finset.univ.filter P, weight ω := by
  classical
  unfold weightedProbability
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hP : P ω <;> simp [hP]

/-- Expectation of a nonnegative random variable in a finite weighted space. -/
def weightedExpectation (weight : Ω → ℝ≥0) (X : Ω → ℝ≥0) : ℝ≥0 :=
  ∑ ω, weight ω * X ω

/-- Expectation of a real-valued random variable with nonnegative finite weights. -/
def realWeightedExpectation (weight : Ω → ℝ≥0) (X : Ω → ℝ) : ℝ :=
  ∑ ω, (weight ω : ℝ) * X ω

@[simp]
theorem weightedProbability_false (weight : Ω → ℝ≥0) :
    weightedProbability weight (fun _ ↦ False) = 0 := by
  simp [weightedProbability]

@[simp]
theorem weightedProbability_true (weight : Ω → ℝ≥0)
    (hsum : ∑ ω, weight ω = 1) :
    weightedProbability weight (fun _ ↦ True) = 1 := by
  simpa [weightedProbability] using hsum

/-- Event probability is monotone under implication. -/
theorem weightedProbability_mono (weight : Ω → ℝ≥0) {P Q : Ω → Prop}
    (hPQ : ∀ ω, P ω → Q ω) :
    weightedProbability weight P ≤ weightedProbability weight Q := by
  classical
  unfold weightedProbability
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω
  · simp [hP, hPQ ω hP]
  · simp [hP]

/-- Union bound for two events. -/
theorem weightedProbability_or_le (weight : Ω → ℝ≥0) (P Q : Ω → Prop) :
    weightedProbability weight (fun ω ↦ P ω ∨ Q ω) ≤
      weightedProbability weight P + weightedProbability weight Q := by
  classical
  unfold weightedProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]

/-- Union bound over a finite family of events. -/
theorem weightedProbability_exists_le {I : Type*} [DecidableEq I]
    (weight : Ω → ℝ≥0) (S : Finset I) (P : I → Ω → Prop) :
    weightedProbability weight (fun ω ↦ ∃ i ∈ S, P i ω) ≤
      ∑ i ∈ S, weightedProbability weight (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [weightedProbability]
  | @insert i S hi ih =>
      have hor := weightedProbability_or_le weight (P i) (fun ω ↦ ∃ j ∈ S, P j ω)
      have hadd := add_le_add_right ih (weightedProbability weight (P i))
      simpa [hi, or_assoc, add_comm] using hor.trans hadd

/-- Pointwise comparison implies comparison of nonnegative expectations. -/
theorem weightedExpectation_mono (weight : Ω → ℝ≥0) {X Y : Ω → ℝ≥0}
    (hXY : ∀ ω, X ω ≤ Y ω) :
    weightedExpectation weight X ≤ weightedExpectation weight Y := by
  unfold weightedExpectation
  exact Finset.sum_le_sum fun ω _ ↦
    mul_le_mul_of_nonneg_left (hXY ω) (by positivity)

@[simp]
theorem weightedExpectation_zero (weight : Ω → ℝ≥0) :
    weightedExpectation weight (fun _ ↦ 0) = 0 := by
  simp [weightedExpectation]

theorem weightedExpectation_add (weight : Ω → ℝ≥0) (X Y : Ω → ℝ≥0) :
    weightedExpectation weight (fun ω ↦ X ω + Y ω) =
      weightedExpectation weight X + weightedExpectation weight Y := by
  simp [weightedExpectation, mul_add, Finset.sum_add_distrib]

/-- Multiplication form of Markov's inequality.  This form remains meaningful
when the threshold is zero. -/
theorem weighted_markov_mul (weight : Ω → ℝ≥0) (X : Ω → ℝ≥0) (a : ℝ≥0) :
    weightedProbability weight (fun ω ↦ a ≤ X ω) * a ≤
      weightedExpectation weight X := by
  classical
  unfold weightedProbability weightedExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : a ≤ X ω
  · simpa [hω, mul_assoc] using
      mul_le_mul_of_nonneg_left hω (by positivity)
  · simp [hω]

/-- Quotient form of Markov's inequality. -/
theorem weighted_markov (weight : Ω → ℝ≥0) (X : Ω → ℝ≥0)
    {a : ℝ≥0} (ha : 0 < a) :
    weightedProbability weight (fun ω ↦ a ≤ X ω) ≤
      weightedExpectation weight X / a := by
  rw [le_div_iff₀ ha]
  exact weighted_markov_mul weight X a

/-- Some outcome is at least the expectation of a nonnegative random variable. -/
theorem exists_weightedExpectation_le [Nonempty Ω]
    (weight : Ω → ℝ≥0) (hsum : ∑ ω, weight ω = 1) (X : Ω → ℝ≥0) :
    ∃ ω, weightedExpectation weight X ≤ X ω := by
  classical
  obtain ⟨ω, _hω, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Ω) X Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  calc
    weightedExpectation weight X ≤ ∑ x, weight x * X ω := by
      unfold weightedExpectation
      exact Finset.sum_le_sum fun x _ ↦
        mul_le_mul_of_nonneg_left (hmax x (Finset.mem_univ x)) (by positivity)
    _ = (∑ x, weight x) * X ω := by rw [Finset.sum_mul]
    _ = X ω := by rw [hsum, one_mul]

/-- Some outcome is at least the real weighted average.  This signed version is
the convenient form of the alteration/positive-expectation argument. -/
theorem exists_realWeightedExpectation_le [Nonempty Ω]
    (weight : Ω → ℝ≥0) (hsum : ∑ ω, weight ω = 1) (X : Ω → ℝ) :
    ∃ ω, realWeightedExpectation weight X ≤ X ω := by
  classical
  obtain ⟨ω, _hω, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Ω) X Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  calc
    realWeightedExpectation weight X ≤ ∑ x, (weight x : ℝ) * X ω := by
      unfold realWeightedExpectation
      exact Finset.sum_le_sum fun x _ ↦
        mul_le_mul_of_nonneg_left (hmax x (Finset.mem_univ x)) (NNReal.coe_nonneg _)
    _ = (∑ x, (weight x : ℝ)) * X ω := by rw [Finset.sum_mul]
    _ = X ω := by
      rw [← NNReal.coe_sum, hsum]
      norm_num

/-- Positive real expectation produces an outcome of positive score. -/
theorem exists_pos_of_realWeightedExpectation_pos [Nonempty Ω]
    (weight : Ω → ℝ≥0) (hsum : ∑ ω, weight ω = 1) (X : Ω → ℝ)
    (hpos : 0 < realWeightedExpectation weight X) :
    ∃ ω, 0 < X ω := by
  obtain ⟨ω, hω⟩ := exists_realWeightedExpectation_le weight hsum X
  exact ⟨ω, hpos.trans_le hω⟩

end WeightedFiniteSpace

section BernoulliSubsets

variable {α : Type*} [Fintype α]

/-- Product weight for the law which independently retains every element with
probability `p`. -/
def bernoulliWeight (p : ℝ≥0) (S : Finset α) : ℝ≥0 :=
  p ^ S.card * (1 - p) ^ (Fintype.card α - S.card)

/-- Bernoulli product weights have total mass one. -/
theorem sum_bernoulliWeight (p : ℝ≥0) (hp : p ≤ 1) :
    ∑ S : Finset α, bernoulliWeight p S = 1 := by
  have h := Fintype.sum_pow_mul_eq_add_pow α p (1 - p)
  simpa [bernoulliWeight, add_tsub_cancel_of_le hp] using h

/-- The total Bernoulli mass of the subsets containing a specified element is
exactly `p`. -/
theorem bernoulli_probability_mem (p : ℝ≥0) (hp : p ≤ 1) (a : α) :
    weightedProbability (bernoulliWeight p) (fun S : Finset α ↦ a ∈ S) = p := by
  classical
  have hsmall :
      ∑ S ∈ Finset.powerset (Finset.univ.erase a),
          p ^ S.card * (1 - p) ^ ((Finset.univ.erase a).card - S.card) = 1 := by
    simpa [add_tsub_cancel_of_le hp] using
      (Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ.erase a))
  have hwith :
      ∑ S ∈ Finset.powerset (Finset.univ.erase a),
          p ^ (S.card + 1) *
            (1 - p) ^ (Fintype.card α - (S.card + 1)) = p := by
    calc
      _ = p * ∑ S ∈ Finset.powerset (Finset.univ.erase a),
          p ^ S.card * (1 - p) ^ ((Finset.univ.erase a).card - S.card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        have hSa : a ∉ S :=
          Finset.notMem_mono (Finset.mem_powerset.mp hS) (Finset.notMem_erase a Finset.univ)
        have hcarda : (Finset.univ.erase a).card = Fintype.card α - 1 := by simp
        rw [hcarda]
        have hScard : S.card ≤ Fintype.card α - 1 := by
          simpa [hcarda] using Finset.card_le_card (Finset.mem_powerset.mp hS)
        have hexponent :
            Fintype.card α - (S.card + 1) = Fintype.card α - 1 - S.card := by
          omega
        rw [hexponent]
        simp only [pow_succ']
        ring
      _ = p := by rw [hsmall, mul_one]
  rw [weightedProbability_eq_filter]
  calc
    _ = ∑ S ∈ Finset.powerset (Finset.univ.erase a),
          p ^ (S.card + 1) *
            (1 - p) ^ (Fintype.card α - (S.card + 1)) := by
      refine Finset.sum_bij (fun S _hS ↦ S.erase a) ?_ ?_ ?_ ?_
      · intro S hS
        exact Finset.mem_powerset.mpr
          (Finset.erase_subset_erase _ (Finset.subset_univ S))
      · intro S₁ hS₁ S₂ hS₂ heq
        have ha₁ := (Finset.mem_filter.mp hS₁).2
        have ha₂ := (Finset.mem_filter.mp hS₂).2
        rw [← Finset.insert_erase ha₁, ← Finset.insert_erase ha₂, heq]
      · intro S hS
        refine ⟨insert a S, ?_, ?_⟩
        · simp
        · rw [Finset.erase_insert]
          exact Finset.notMem_mono (Finset.mem_powerset.mp hS)
            (Finset.notMem_erase a Finset.univ)
      · intro S hS
        simp only [bernoulliWeight]
        rw [Finset.card_erase_add_one (Finset.mem_filter.mp hS).2]
    _ = p := hwith

/-- Exact joint-inclusion probability.  This is the finite-sum expression of
independence: every element of `T` is retained with probability `p ^ |T|`. -/
theorem bernoulli_probability_subset (p : ℝ≥0) (hp : p ≤ 1) (T : Finset α) :
    weightedProbability (bernoulliWeight p) (fun S : Finset α ↦ T ⊆ S) =
      p ^ T.card := by
  classical
  let U : Finset α := Finset.univ \ T
  have hUT : Disjoint U T := by
    simp [U, Finset.disjoint_left]
  have hUcard : U.card = Fintype.card α - T.card := by
    simp [U, Finset.card_sdiff]
  have hsmall :
      ∑ A ∈ U.powerset,
          p ^ A.card * (1 - p) ^ (U.card - A.card) = 1 := by
    simpa [add_tsub_cancel_of_le hp] using
      (Finset.sum_pow_mul_eq_add_pow p (1 - p) U)
  have hunion :
      ∑ A ∈ U.powerset, bernoulliWeight p (T ∪ A) = p ^ T.card := by
    calc
      _ = p ^ T.card * ∑ A ∈ U.powerset,
          p ^ A.card * (1 - p) ^ (U.card - A.card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        have hAT : Disjoint A T :=
          (Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hA) hUT)
        have hcard : (T ∪ A).card = T.card + A.card := by
          rw [Finset.card_union_of_disjoint hAT.symm]
        simp only [bernoulliWeight, hcard, pow_add]
        have hAcard : A.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
        have hexponent :
            Fintype.card α - (T.card + A.card) = U.card - A.card := by
          rw [hUcard]
          omega
        rw [hexponent]
        ac_rfl
      _ = p ^ T.card := by rw [hsmall, mul_one]
  rw [weightedProbability_eq_filter]
  calc
    _ = ∑ A ∈ U.powerset, bernoulliWeight p (T ∪ A) := by
      refine Finset.sum_bij (fun S _hS ↦ S \ T) ?_ ?_ ?_ ?_
      · intro S hS
        exact Finset.mem_powerset.mpr <| by
          intro a ha
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ a, (Finset.mem_sdiff.mp ha).2⟩
      · intro S₁ hS₁ S₂ hS₂ heq
        have hT₁ := (Finset.mem_filter.mp hS₁).2
        have hT₂ := (Finset.mem_filter.mp hS₂).2
        rw [← Finset.union_sdiff_of_subset hT₁, ← Finset.union_sdiff_of_subset hT₂, heq]
      · intro A hA
        refine ⟨T ∪ A, ?_, ?_⟩
        · simp
        · have hAT : Disjoint A T :=
            Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hA) hUT
          rw [Finset.union_sdiff_left]
          exact Finset.sdiff_eq_self_of_disjoint hAT
      · intro S hS
        congr 1
        exact (Finset.union_sdiff_of_subset (Finset.mem_filter.mp hS).2).symm
    _ = p ^ T.card := hunion

/-- The first moment of the size of a Bernoulli subset. -/
theorem bernoulli_expect_card (p : ℝ≥0) (hp : p ≤ 1) :
    weightedExpectation (bernoulliWeight p)
      (fun S : Finset α ↦ (S.card : ℝ≥0)) = p * Fintype.card α := by
  classical
  calc
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset α ↦ (S.card : ℝ≥0)) =
        ∑ a : α, weightedProbability (bernoulliWeight p)
          (fun S : Finset α ↦ a ∈ S) := by
      calc
        (weightedExpectation (bernoulliWeight p)
            (fun S : Finset α ↦ (S.card : ℝ≥0))) =
            ∑ a : α, ∑ S : Finset α,
              if a ∈ S then bernoulliWeight p S else 0 := by
          unfold weightedExpectation
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro S _
          simp only
          rw [show (S.card : ℝ≥0) = ∑ _a ∈ S, (1 : ℝ≥0) by simp]
          rw [Finset.mul_sum]
          simp only [mul_one]
          calc
            (∑ _a ∈ S, bernoulliWeight p S) =
                ∑ a ∈ Finset.univ.filter (fun a : α ↦ a ∈ S),
                  bernoulliWeight p S := by simp
            _ = ∑ x : α, if x ∈ S then bernoulliWeight p S else 0 := by
              rw [Finset.sum_filter]
        _ = ∑ a : α, weightedProbability (bernoulliWeight p)
              (fun S : Finset α ↦ a ∈ S) := by
          apply Finset.sum_congr rfl
          intro a _
          unfold weightedProbability
          apply Finset.sum_congr rfl
          intro S _
          by_cases ha : a ∈ S <;> simp [ha]
    _ = ∑ _a : α, p := by
      apply Finset.sum_congr rfl
      intro a _
      exact bernoulli_probability_mem p hp a
    _ = p * Fintype.card α := by simp [mul_comm]

/-- First moment of an arbitrary nonnegative vertex weight under Bernoulli
sampling. -/
theorem bernoulli_expect_sum (p : ℝ≥0) (hp : p ≤ 1) (w : α → ℝ≥0) :
    weightedExpectation (bernoulliWeight p)
      (fun S : Finset α ↦ ∑ a ∈ S, w a) = p * ∑ a, w a := by
  classical
  calc
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset α ↦ ∑ a ∈ S, w a) =
        ∑ a : α, w a * weightedProbability (bernoulliWeight p)
          (fun S : Finset α ↦ a ∈ S) := by
      unfold weightedExpectation
      calc
        (∑ S : Finset α, bernoulliWeight p S * ∑ a ∈ S, w a) =
            ∑ S : Finset α, ∑ a : α,
              if a ∈ S then w a * bernoulliWeight p S else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.mul_sum]
          simp [mul_comm]
        _ = ∑ a : α, ∑ S : Finset α,
              if a ∈ S then w a * bernoulliWeight p S else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ a : α, w a * ∑ S : Finset α,
              if a ∈ S then bernoulliWeight p S else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          by_cases ha : a ∈ S <;> simp [ha]
        _ = ∑ a : α, w a * weightedProbability (bernoulliWeight p)
              (fun S : Finset α ↦ a ∈ S) := by
          apply Finset.sum_congr rfl
          intro a _
          congr 1
          unfold weightedProbability
          apply Finset.sum_congr rfl
          intro S _
          by_cases ha : a ∈ S <;> simp [ha]
    _ = ∑ a : α, w a * p := by
      apply Finset.sum_congr rfl
      intro a _
      rw [bernoulli_probability_mem p hp a]
    _ = p * ∑ a, w a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _

/-- First moment of the number of sampled elements belonging to a fixed set. -/
theorem bernoulli_expect_inter_card [DecidableEq α]
    (p : ℝ≥0) (hp : p ≤ 1) (T : Finset α) :
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset α ↦ ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0)) =
      p * T.card := by
  unfold weightedExpectation
  calc
    (∑ S : Finset α, bernoulliWeight p S *
        ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0)) =
        ∑ S : Finset α, bernoulliWeight p S *
          (∑ a ∈ T, if a ∈ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      congr 1
      norm_cast
      rw [Finset.card_filter]
    _ = ∑ a ∈ T, weightedProbability (bernoulliWeight p)
          (fun S : Finset α ↦ a ∈ S) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      unfold weightedProbability
      apply Finset.sum_congr rfl
      intro S _
      by_cases haS : a ∈ S <;> simp [haS]
    _ = ∑ _a ∈ T, p := by
      apply Finset.sum_congr rfl
      intro a _
      exact bernoulli_probability_mem p hp a
    _ = p * T.card := by simp [mul_comm]

omit [Fintype α] in
/-- The square of an intersection cardinality counts ordered pairs of retained
elements. -/
theorem interCard_sq_eq_sum_pairs [DecidableEq α] (T S : Finset α) :
    ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0) ^ 2 =
      ∑ a ∈ T, ∑ b ∈ T,
        if ({a, b} : Finset α) ⊆ S then 1 else 0 := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  rw [show ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0) =
      ∑ a ∈ T, if a ∈ S then 1 else 0 by
    norm_cast
    rw [Finset.card_filter]]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;> simp [haS, hbS]

/-- Pair-sum form of the Bernoulli second moment. -/
theorem bernoulli_expect_inter_card_sq_pairs [DecidableEq α]
    (p : ℝ≥0) (hp : p ≤ 1) (T : Finset α) :
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset α ↦
          ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0) ^ 2) =
      ∑ a ∈ T, ∑ b ∈ T, p ^ ({a, b} : Finset α).card := by
  unfold weightedExpectation
  calc
    (∑ S : Finset α, bernoulliWeight p S *
        ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0) ^ 2) =
        ∑ S : Finset α, bernoulliWeight p S *
          (∑ a ∈ T, ∑ b ∈ T,
            if ({a, b} : Finset α) ⊆ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [interCard_sq_eq_sum_pairs]
    _ = ∑ a ∈ T, ∑ b ∈ T,
          weightedProbability (bernoulliWeight p)
            (fun S : Finset α ↦ ({a, b} : Finset α) ⊆ S) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      unfold weightedProbability
      apply Finset.sum_congr rfl
      intro S _
      by_cases hab : ({a, b} : Finset α) ⊆ S <;> simp [hab]
    _ = ∑ a ∈ T, ∑ b ∈ T, p ^ ({a, b} : Finset α).card := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact bernoulli_probability_subset p hp {a, b}

omit [Fintype α] in
/-- Evaluation of the diagonal/off-diagonal ordered-pair sum. -/
theorem sum_pair_bernoulli_power [DecidableEq α] (p : ℝ≥0) (T : Finset α) :
    (∑ a ∈ T, ∑ b ∈ T, p ^ ({a, b} : Finset α).card) =
      p * T.card + p ^ 2 * T.card * (T.card - 1) := by
  calc
    _ = ∑ a ∈ T, (p + p ^ 2 * (T.card - 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ b ∈ T, p ^ ({a, b} : Finset α).card) =
            (∑ b ∈ T.erase a, p ^ ({a, b} : Finset α).card) +
              p ^ ({a, a} : Finset α).card := by
          rw [Finset.sum_erase_add _ _ ha]
        _ = (∑ _b ∈ T.erase a, p ^ 2) + p := by
          congr 1
          · apply Finset.sum_congr rfl
            intro b hb
            have hba : b ≠ a := (Finset.mem_erase.mp hb).1
            simp [Ne.symm hba]
          · simp
        _ = p + p ^ 2 * (T.card - 1) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem ha]
          simp [nsmul_eq_mul, mul_comm, add_comm]
    _ = p * T.card + p ^ 2 * T.card * (T.card - 1) := by
      simp [nsmul_eq_mul]
      ring

/-- Exact second moment of the size of the intersection of a Bernoulli sample
with a fixed finite set. -/
theorem bernoulli_expect_inter_card_sq [DecidableEq α]
    (p : ℝ≥0) (hp : p ≤ 1) (T : Finset α) :
    weightedExpectation (bernoulliWeight p)
        (fun S : Finset α ↦
          ((T.filter (fun a ↦ a ∈ S)).card : ℝ≥0) ^ 2) =
      p * T.card + p ^ 2 * T.card * (T.card - 1) := by
  rw [bernoulli_expect_inter_card_sq_pairs p hp T,
    sum_pair_bernoulli_power]

end BernoulliSubsets

end

end Erdos182

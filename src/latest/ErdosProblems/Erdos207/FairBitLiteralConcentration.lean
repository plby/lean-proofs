/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBlockConcentration

/-!
# Lower tails for prescribed literals of independent fair bits

The paired-bisection argument needs a fair bit to take a prescribed value
which depends on the link vertex and on the fixed pairing.  Negating selected
coordinates does not change the fair product law.  Here that invariance is
proved directly by calculating the exact finite probability of every set of
matched literals, followed by the same generating-function estimate used for
active blocks.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Coordinates in `S` at which `ω` agrees with the prescribed literal. -/
def matchedBits
    {I : Type*} [DecidableEq I]
    (σ ω : I → Bool) (S : Finset I) : Finset I :=
  S.filter fun i ↦ ω i = σ i

@[simp]
lemma mem_matchedBits_iff
    {I : Type*} [DecidableEq I]
    {σ ω : I → Bool} {S : Finset I} {i : I} :
    i ∈ matchedBits σ ω S ↔ i ∈ S ∧ ω i = σ i := by
  simp [matchedBits]

/-- Assignment which agrees with `σ` exactly on `T` among the coordinates
of `S`. -/
def exactMatchAssignment
    {I : Type*} [DecidableEq I]
    (σ : I → Bool) (T : Finset I) (i : I) : Bool :=
  if i ∈ T then σ i else !(σ i)

lemma matchedBits_eq_iff_agrees_exactMatchAssignment
    {I : Type*} [DecidableEq I]
    (σ ω : I → Bool) (S T : Finset I) (hTS : T ⊆ S) :
    matchedBits σ ω S = T ↔
      ∀ i ∈ S, ω i = exactMatchAssignment σ T i := by
  constructor
  · intro heq i hiS
    by_cases hiT : i ∈ T
    · have hiMatch : i ∈ matchedBits σ ω S := heq.symm ▸ hiT
      simpa [exactMatchAssignment, hiT] using
        (mem_matchedBits_iff.mp hiMatch).2
    · have hiNotMatch : i ∉ matchedBits σ ω S := by
        intro hi
        exact hiT (heq ▸ hi)
      have hne : ω i ≠ σ i := by
        intro h
        exact hiNotMatch (mem_matchedBits_iff.mpr ⟨hiS, h⟩)
      cases hω : ω i <;> cases hσ : σ i <;>
        simp_all [exactMatchAssignment, hiT]
  · intro hagree
    ext i
    by_cases hiT : i ∈ T
    · have hiS := hTS hiT
      have hiAgree := hagree i hiS
      simp only [exactMatchAssignment, hiT, if_true] at hiAgree
      simp [mem_matchedBits_iff, hiS, hiT, hiAgree]
    · by_cases hiS : i ∈ S
      · have hiAgree := hagree i hiS
        simp only [exactMatchAssignment, hiT, if_false] at hiAgree
        cases hσ : σ i <;> simp_all [mem_matchedBits_iff]
      · simp [mem_matchedBits_iff, hiS, hiT]

/-- Every exact matched-literal set has the fair binomial probability. -/
theorem fairBits_probability_matchedBits_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (σ : I → Bool) (S T : Finset I) (hTS : T ⊆ S) :
    (FiniteLaw.independentBits (fun _ : I ↦ (1 / 2 : ℝ≥0))
      (fun _ ↦ by norm_num)).probability
        (fun ω ↦ matchedBits σ ω S = T) =
      (1 / 2 : ℝ≥0) ^ T.card *
        (1 - (1 / 2 : ℝ≥0)) ^ (S.card - T.card) := by
  let τ : I → Bool := exactMatchAssignment σ T
  rw [show (fun ω : I → Bool ↦ matchedBits σ ω S = T) =
      (fun ω ↦ ∀ i ∈ S, ω i = τ i) by
    funext ω
    exact propext (matchedBits_eq_iff_agrees_exactMatchAssignment
      σ ω S T hTS)]
  rw [FiniteLaw.independentBits_probability_agrees]
  have hmass : ∀ i : I,
      FiniteLaw.bernoulliBitMass (1 / 2 : ℝ≥0) (τ i) = 1 / 2 := by
    intro i
    cases hτ : τ i
    · simp only [FiniteLaw.bernoulliBitMass, hτ, Bool.false_eq_true,
        if_false]
      apply NNReal.eq
      norm_num
    · simp [FiniteLaw.bernoulliBitMass, hτ]
  simp_rw [hmass]
  simp only [prod_const]
  have hhalf : (1 - (1 / 2 : ℝ≥0)) = 1 / 2 := by
    apply NNReal.eq
    norm_num
  rw [hhalf, ← pow_add, Nat.add_sub_of_le (card_le_card hTS)]

/-- Generating-function lower tail for a prescribed family of fair
literals. -/
theorem fairBits_probability_matchedBits_card_le_le_generating
    {I : Type*} [Fintype I] [DecidableEq I]
    (σ : I → Bool) (S : Finset I) (k : ℕ) :
    (FiniteLaw.independentBits (fun _ : I ↦ (1 / 2 : ℝ≥0))
      (fun _ ↦ by norm_num)).probability
        (fun ω ↦ (matchedBits σ ω S).card ≤ k) ≤
      (2 : ℝ≥0) ^ k * (3 / 4 : ℝ≥0) ^ S.card := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : I ↦ (1 / 2 : ℝ≥0)) (fun _ ↦ by norm_num)
  let Bad : Finset (Finset I) :=
    S.powerset.filter fun T ↦ T.card ≤ k
  let P : Finset I → (I → Bool) → Prop :=
    fun T ω ↦ matchedBits σ ω S = T
  calc
    L.probability (fun ω ↦ (matchedBits σ ω S).card ≤ k) ≤
        L.probability (fun ω ↦ ∃ T ∈ Bad, P T ω) := by
      apply L.probability_mono
      intro ω hcard
      exact ⟨matchedBits σ ω S,
        mem_filter.mpr ⟨mem_powerset.mpr (fun i hi ↦
          (mem_matchedBits_iff.mp hi).1), hcard⟩, rfl⟩
    _ ≤ ∑ T ∈ Bad, L.probability (P T) :=
      L.probability_exists_le Bad P
    _ = ∑ T ∈ Bad,
          (1 / 2 : ℝ≥0) ^ T.card *
            (1 - (1 / 2 : ℝ≥0)) ^ (S.card - T.card) := by
      apply sum_congr rfl
      intro T hT
      exact fairBits_probability_matchedBits_eq σ S T
        (mem_powerset.mp (mem_filter.mp hT).1)
    _ ≤ ∑ T ∈ Bad,
          (2 : ℝ≥0) ^ k *
            ((1 / 4 : ℝ≥0) ^ T.card *
              (1 / 2 : ℝ≥0) ^ (S.card - T.card)) := by
      apply sum_le_sum
      intro T hT
      have hTk : T.card ≤ k := (mem_filter.mp hT).2
      have hhalf : (1 - (1 / 2 : ℝ≥0)) = 1 / 2 := by
        apply NNReal.eq
        norm_num
      calc
        (1 / 2 : ℝ≥0) ^ T.card *
              (1 - (1 / 2 : ℝ≥0)) ^ (S.card - T.card) =
            (2 : ℝ≥0) ^ T.card *
              ((1 / 4 : ℝ≥0) ^ T.card *
                (1 / 2 : ℝ≥0) ^ (S.card - T.card)) := by
          rw [hhalf]
          rw [← mul_assoc, ← mul_pow]
          norm_num
        _ ≤ (2 : ℝ≥0) ^ k *
              ((1 / 4 : ℝ≥0) ^ T.card *
                (1 / 2 : ℝ≥0) ^ (S.card - T.card)) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right' (by norm_num : (1 : ℝ≥0) ≤ 2) hTk)
              (by positivity)
    _ = (2 : ℝ≥0) ^ k *
          ∑ T ∈ Bad,
            (1 / 4 : ℝ≥0) ^ T.card *
              (1 / 2 : ℝ≥0) ^ (S.card - T.card) := by
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ≥0) ^ k *
          ∑ T ∈ S.powerset,
            (1 / 4 : ℝ≥0) ^ T.card *
              (1 / 2 : ℝ≥0) ^ (S.card - T.card) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (fun T hT ↦ (mem_filter.mp hT).1)
          (fun _ _ _ ↦ by positivity)) (by positivity)
    _ = (2 : ℝ≥0) ^ k * (3 / 4 : ℝ≥0) ^ S.card := by
      rw [sum_powerset_split_probabilities]
      congr 2
      norm_num

end

end Erdos207

import Arxiv.Arxiv2411_18291.IndependentFiniteChoices
import Arxiv.Arxiv2411_18291.IndependentMeanBound

/-!
# Simultaneously balancing weighted representative counts

One independent uniform choice is made in each finite coordinate. Weighting
a successful choice by its coordinate size preserves the total expected
count. A union bound supplies one choice balancing every prescribed test.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.RandomFiniteChoice

variable {I T : Type*} [Fintype I] {A : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
variable [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)]

theorem weighted_sum_mean (s : ∀ i, Finset (A i)) :
    (∫ ω, ∑ i, weightedMember i (s i) ω ∂probability A) = ∑ i, ((s i).card : ℝ) := by
  rw [integral_finsetSum univ (fun i _ => weightedMember_integrable i (s i))]
  simp only [weightedMember_mean]

theorem weighted_sum_upper_tail (s : ∀ i, Finset (A i)) {C B : ℝ} (hC : 0 < C)
    (hcard : ∀ i, (Fintype.card (A i) : ℝ) ≤ C) (hB : (∑ i, ((s i).card : ℝ)) ≤ B) :
    (probability A).real {ω | 2 * B < ∑ i, weightedMember i (s i) ω} ≤
      Real.exp (-(B / (3 * C))) := by
  apply independent_nonnegative_upper_tail_of_mean_le univ hC
    (fun i => weightedMember_measurable i (s i)) (weightedMember_independent s)
  · intro i _
    exact Filter.Eventually.of_forall fun ω =>
      ⟨(weightedMember_bounds i (s i) ω).1, (weightedMember_bounds i (s i) ω).2.trans (hcard i)⟩
  · rw [weighted_sum_mean]
    exact hB

theorem exists_balanced_choices (tests : Finset T) (s : T → ∀ i, Finset (A i))
    {C B : ℝ} (hC : 0 < C) (hcard : ∀ i, (Fintype.card (A i) : ℝ) ≤ C)
    (hB : ∀ t ∈ tests, (∑ i, ((s t i).card : ℝ)) ≤ B)
    (hsmall : tests.card * Real.exp (-(B / (3 * C))) < 1) :
    ∃ ω : Sample A, ∀ t ∈ tests, ∑ i, weightedMember i (s t i) ω ≤ 2 * B := by
  classical
  let bad (t : T) := {ω : Sample A | 2 * B < ∑ i, weightedMember i (s t i) ω}
  have hprob : (probability A).real (⋃ t ∈ tests, bad t) ≤
      tests.card * Real.exp (-(B / (3 * C))) := by
    calc
      _ ≤ ∑ t ∈ tests, (probability A).real (bad t) := measureReal_biUnion_finset_le tests _
      _ ≤ ∑ _t ∈ tests, Real.exp (-(B / (3 * C))) :=
        sum_le_sum fun t ht => weighted_sum_upper_tail (s t) hC hcard (hB t ht)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  by_contra h
  push Not at h
  have hall : (⋃ t ∈ tests, bad t) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨t, ht, hω⟩ := h ω
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hω⟩⟩
  rw [hall, probReal_univ] at hprob
  linarith only [hprob, hsmall]

end Arxiv2411_18291.RandomFiniteChoice

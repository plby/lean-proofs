/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Basic
import ErdosProblems.Erdos285.Proposition7
import UnitFractions.AuxiliaryLemmas

/-!
# Erdős Problem 284: exact-cardinality padding

The identity used by Croot's variable-cardinality-to-all-cardinalities bridge
is already formalized in the Proposition 7 infrastructure for Erdős 285.
This file packages that operation with the lower-denominator invariant needed
for Erdős 284.
-/

namespace Erdos284

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem shortIntervalWitness_nonempty
    {N X : ℕ} {A : Finset ℕ} (hA : ShortIntervalWitness N X A) :
    A.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hsum := hA.sum_eq
  simp [hne, UnitFractions.rec_sum] at hsum

/-- A set contained in `(N, X]` has at most `X - N` elements. -/
theorem ShortIntervalWitness.card_le_sub
    {N X : ℕ} {A : Finset ℕ} (hA : ShortIntervalWitness N X A) :
    A.card ≤ X - N := by
  calc
    A.card ≤ (Finset.Ioc N X).card := by
      apply Finset.card_le_card
      intro n hn
      exact Finset.mem_Ioc.mpr (hA.interval n hn)
    _ = X - N := by simp

/-- A reciprocal-sum-one set lying strictly above `N` has at least `N + 1`
elements.  This elementary estimate is also what makes one-shot padding
possible in the asymptotic range used below. -/
theorem ShortIntervalWitness.succ_le_card
    {N X : ℕ} {A : Finset ℕ} (hA : ShortIntervalWitness N X A) :
    N + 1 ≤ A.card := by
  have hM : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hbound := UnitFractions.rec_sum_le_card_div (A := A)
    (M := ((N + 1 : ℕ) : ℝ)) hM (fun n hn ↦ by
      exact_mod_cast (Nat.succ_le_iff.mpr (hA.interval n hn).1))
  have hsumR : (UnitFractions.rec_sum A : ℝ) = 1 := by
    rw [hA.sum_eq]
    norm_num
  rw [hsumR, le_div_iff₀ hM] at hbound
  norm_num at hbound
  exact_mod_cast hbound

private lemma paddingTerms_at_le
    {n m a : ℕ} (hn : 0 < n) (ha : a ∈ Erdos285.Proposition7.paddingTerms n m) :
    n ≤ a := by
  by_cases hm : m = 0
  · subst m
    simp [Erdos285.Proposition7.paddingTerms] at ha
    exact ha.ge
  · exact (Erdos285.Proposition7.paddingTerms_above hn
      (Nat.pos_of_ne_zero hm) ha).le

/-- Pad a Croot short-interval witness to exactly `K` terms without lowering
any denominator.  The numerical side condition is precisely the condition
needed by the one-shot telescoping padding operation. -/
theorem padShortIntervalWitnessToCard
    {N X K : ℕ} {A : Finset ℕ}
    (hA : ShortIntervalWitness N X A)
    (hcard : A.card ≤ K)
    (hdeficit : K - A.card < A.max' (shortIntervalWitness_nonempty hA)) :
    ∃ E : Finset ℕ,
      FinsetRepresentation K E ∧ ∀ a ∈ E, N < a := by
  let hAne : A.Nonempty := shortIntervalWitness_nonempty hA
  let n : ℕ := A.max' hAne
  let m : ℕ := K - A.card
  have hnA : n ∈ A := Finset.max'_mem A hAne
  have hnmax : ∀ a ∈ A, a ≤ n := fun a ha ↦ Finset.le_max' A a ha
  have hnpos : 0 < n := by
    have := (hA.interval n hnA).1
    omega
  have hspec := Erdos285.Proposition7.padAt_spec
    hnA hnmax hA.zero_not_mem hdeficit
  refine ⟨Erdos285.Proposition7.padAt A n m, ?_, ?_⟩
  · refine ⟨?_, hspec.2.2.1, ?_⟩
    · rw [hspec.1]
      omega
    · simpa [m] using hspec.2.1.trans hA.sum_eq
  · intro a ha
    rw [Erdos285.Proposition7.padAt, Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact (hA.interval a (Finset.mem_of_mem_erase ha)).1
    · exact (hA.interval n hnA).1.trans_le (paddingTerms_at_le hnpos ha)

/-- A convenient numerical wrapper around
`padShortIntervalWitnessToCard`.  The lower cardinality bound supplied by a
short-interval witness turns `K < 2(N+1)` into the required padding-deficit
bound. -/
theorem padShortIntervalWitnessToCard_of_lt_two_mul
    {N X K : ℕ} {A : Finset ℕ}
    (hA : ShortIntervalWitness N X A)
    (hcard : A.card ≤ K)
    (hK : K < 2 * (N + 1)) :
    ∃ E : Finset ℕ,
      FinsetRepresentation K E ∧ ∀ a ∈ E, N < a := by
  have hAne := shortIntervalWitness_nonempty hA
  have hmaxmem : A.max' hAne ∈ A := Finset.max'_mem A hAne
  have hmax : N + 1 ≤ A.max' hAne :=
    Nat.succ_le_iff.mpr (hA.interval _ hmaxmem).1
  apply padShortIntervalWitnessToCard hA hcard
  have hlower := hA.succ_le_card
  omega

end

end Erdos284

#print axioms Erdos284.padShortIntervalWitnessToCard
#print axioms Erdos284.ShortIntervalWitness.card_le_sub
#print axioms Erdos284.ShortIntervalWitness.succ_le_card
#print axioms Erdos284.padShortIntervalWitnessToCard_of_lt_two_mul

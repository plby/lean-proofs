import Mathlib

/-!
# Measurable first-small-block frequency partition

Mathlib's `disjointed` construction supplies the first successful level.
Level zero is empty in the prime-block application. The residual class
has no small block, and the finite integral decomposition is exact.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-- All prime subblocks at a positive level are small. The unused level
zero is empty so that the first successful positive level is unchanged. -/
def mrSmallPrimeBlockSet (I : ℕ → Finset ℕ) (Q : ℕ → ℕ → ℝ → ℂ)
    (V : ℕ → ℕ → ℝ) (j : ℕ) : Set ℝ :=
  if j = 0 then ∅ else {t | ∀ r ∈ I j, ‖Q j r t‖ ≤ V j r}

theorem measurableSet_mrSmallPrimeBlockSet
    (I : ℕ → Finset ℕ) (Q : ℕ → ℕ → ℝ → ℂ) (V : ℕ → ℕ → ℝ)
    (hQ : ∀ j r, r ∈ I j → Continuous (Q j r)) (j : ℕ) :
    MeasurableSet (mrSmallPrimeBlockSet I Q V j) := by
  by_cases hj : j = 0
  · simp [mrSmallPrimeBlockSet, hj]
  · rw [mrSmallPrimeBlockSet, if_neg hj]
    have heq : {t : ℝ | ∀ r ∈ I j, ‖Q j r t‖ ≤ V j r} =
        ⋂ r, ⋂ (_hr : r ∈ I j), {t : ℝ | ‖Q j r t‖ ≤ V j r} := by ext t; simp
    rw [heq]
    exact MeasurableSet.iInter (fun r ↦ MeasurableSet.iInter (fun hr ↦
      measurableSet_le (hQ j r hr).norm.measurable measurable_const))

theorem mrFirstSmall_current_small
    (I : ℕ → Finset ℕ) (Q : ℕ → ℕ → ℝ → ℂ) (V : ℕ → ℕ → ℝ)
    {j : ℕ} (hj : 1 ≤ j) {t : ℝ}
    (ht : t ∈ disjointed (mrSmallPrimeBlockSet I Q V) j) :
    ∀ r ∈ I j, ‖Q j r t‖ ≤ V j r := by
  have hm := disjointed_subset (mrSmallPrimeBlockSet I Q V) j ht
  simpa only [mrSmallPrimeBlockSet, if_neg (by omega : j ≠ 0), Set.mem_ofPred_eq] using hm

/-- A first-small level after the first has a genuinely large preceding
subblock. This is the covering property, not an extra assumption. -/
theorem mrFirstSmall_preceding_large
    (I : ℕ → Finset ℕ) (Q : ℕ → ℕ → ℝ → ℂ) (V : ℕ → ℕ → ℝ)
    {j : ℕ} (hj : 2 ≤ j) {t : ℝ}
    (ht : t ∈ disjointed (mrSmallPrimeBlockSet I Q V) j) :
    ∃ r ∈ I (j - 1), V (j - 1) r < ‖Q (j - 1) r t‖ := by
  rw [disjointed_eq_inter_compl] at ht
  have hn : t ∉ mrSmallPrimeBlockSet I Q V (j - 1) :=
    Set.mem_iInter.mp (Set.mem_iInter.mp ht.2 (j - 1)) (by omega)
  have hnot : ¬ ∀ r ∈ I (j - 1), ‖Q (j - 1) r t‖ ≤ V (j - 1) r := by
    simpa only [mrSmallPrimeBlockSet, if_neg (by omega : j - 1 ≠ 0), Set.mem_ofPred_eq] using hn
  push Not at hnot
  exact hnot

/-- Frequencies with no small block through level `J`. -/
def mrNoSmallFrequencyClass (small : ℕ → Set ℝ) (J : ℕ) : Set ℝ :=
  (partialSups small J)ᶜ

theorem measurableSet_mrNoSmallFrequencyClass {small : ℕ → Set ℝ}
    (hsmall : ∀ j, MeasurableSet (small j)) (J : ℕ) :
    MeasurableSet (mrNoSmallFrequencyClass small J) := by
  unfold mrNoSmallFrequencyClass
  rw [← biUnion_range_succ_disjointed small J]
  exact (MeasurableSet.iUnion (fun j ↦ MeasurableSet.iUnion
    (fun _hj ↦ MeasurableSet.disjointed hsmall j))).compl

theorem mrFirstSmall_not_noSmall {small : ℕ → Set ℝ} {J j : ℕ}
    (hj : j ∈ Finset.range (J + 1)) {t : ℝ} (ht : t ∈ disjointed small j) :
    t ∉ mrNoSmallFrequencyClass small J := by
  have hm : t ∈ ⋃ i ∈ Finset.range (J + 1), disjointed small i :=
    Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, ht⟩⟩
  rw [biUnion_range_succ_disjointed] at hm
  simpa only [mrNoSmallFrequencyClass, Set.mem_compl_iff, not_not] using hm

theorem exists_firstSmall_of_not_noSmall {small : ℕ → Set ℝ} {J : ℕ} {t : ℝ}
    (ht : t ∉ mrNoSmallFrequencyClass small J) :
    ∃ j ∈ Finset.range (J + 1), t ∈ disjointed small j := by
  have hm : t ∈ partialSups small J := by
    simpa only [mrNoSmallFrequencyClass, Set.mem_compl_iff, not_not] using ht
  rw [← biUnion_range_succ_disjointed small J] at hm
  obtain ⟨j, hjmem⟩ := Set.mem_iUnion.mp hm
  obtain ⟨hj, htj⟩ := Set.mem_iUnion.mp hjmem
  exact ⟨j, hj, htj⟩

/-- The residual class has a large subblock at every selected positive
level, as needed for the exceptional-frequency argument. -/
theorem mrNoSmall_primeBlock_large
    (I : ℕ → Finset ℕ) (Q : ℕ → ℕ → ℝ → ℂ) (V : ℕ → ℕ → ℝ)
    {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) {t : ℝ}
    (ht : t ∈ mrNoSmallFrequencyClass (mrSmallPrimeBlockSet I Q V) J) :
    ∃ r ∈ I j, V j r < ‖Q j r t‖ := by
  change t ∉ partialSups (mrSmallPrimeBlockSet I Q V) J at ht
  have hn : t ∉ mrSmallPrimeBlockSet I Q V j :=
    fun hm ↦ ht (le_partialSups_of_le (mrSmallPrimeBlockSet I Q V) hjJ hm)
  have hnot : ¬ ∀ r ∈ I j, ‖Q j r t‖ ≤ V j r := by
    simpa only [mrSmallPrimeBlockSet, if_neg (by omega : j ≠ 0), Set.mem_ofPred_eq] using hn
  push Not at hnot
  exact hnot

/-- The finite indicator partition holds pointwise, including `J=0`. -/
theorem mrFrequencyClass_indicator_partition
    (small : ℕ → Set ℝ) (g : ℝ → ℝ) (J : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (J + 1), (disjointed small j).indicator g t) +
      (mrNoSmallFrequencyClass small J).indicator g t = g t := by
  classical
  by_cases ht : t ∈ mrNoSmallFrequencyClass small J
  · rw [Set.indicator_of_mem ht]
    have hzero : (∑ j ∈ Finset.range (J + 1), (disjointed small j).indicator g t) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply Set.indicator_of_notMem
      exact fun hfirst ↦ mrFirstSmall_not_noSmall hj hfirst ht
    rw [hzero, zero_add]
  · obtain ⟨j, hj, htj⟩ := exists_firstSmall_of_not_noSmall ht
    rw [Set.indicator_of_notMem ht, add_zero, Finset.sum_eq_single j]
    · exact Set.indicator_of_mem htj g
    · intro i hi hij
      apply Set.indicator_of_notMem
      intro hti
      exact Set.disjoint_left.mp (disjoint_disjointed small hij) hti htj
    · intro hjnot
      exact (hjnot hj).elim

/-- Exact finite decomposition for every interval-integrable function,
so a prior measurable high-frequency restriction is allowed. -/
theorem intervalIntegral_eq_firstSmall_add_noSmall
    {small : ℕ → Set ℝ} (hsmall : ∀ j, MeasurableSet (small j)) (J : ℕ)
    {g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, g t) =
      (∑ j ∈ Finset.range (J + 1), ∫ t in a..b, (disjointed small j).indicator g t) +
        ∫ t in a..b, (mrNoSmallFrequencyClass small J).indicator g t := by
  have hint (B : Set ℝ) (hB : MeasurableSet B) : IntervalIntegrable (B.indicator g) volume a b := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp hg).indicator hB
  have hfirst (j : ℕ) := hint (disjointed small j) (MeasurableSet.disjointed hsmall j)
  have hlast := hint (mrNoSmallFrequencyClass small J) (measurableSet_mrNoSmallFrequencyClass hsmall J)
  have hsum := IntervalIntegrable.sum (Finset.range (J + 1)) (fun j _ ↦ hfirst j)
  have heq : g = (∑ j ∈ Finset.range (J + 1), (disjointed small j).indicator g) +
      (mrNoSmallFrequencyClass small J).indicator g := by
    funext t
    simp only [Pi.add_apply, Finset.sum_apply]
    exact (mrFrequencyClass_indicator_partition small g J t).symm
  calc
    (∫ t in a..b, g t) = ∫ t in a..b,
        ((∑ j ∈ Finset.range (J + 1), (disjointed small j).indicator g) +
          (mrNoSmallFrequencyClass small J).indicator g) t := by rw [← heq]
    _ = _ := by
      simp only [Pi.add_apply]
      rw [intervalIntegral.integral_add hsum hlast]
      congr 1
      simp only [Finset.sum_apply]
      exact intervalIntegral.integral_finsetSum (fun j _ ↦ hfirst j)

end

end Erdos67b

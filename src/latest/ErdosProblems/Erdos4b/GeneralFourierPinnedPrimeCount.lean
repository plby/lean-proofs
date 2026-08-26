/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedIntegerCrt

/-!
# The literal pinned prime count and its exact totient main term

Unsupported graph states contribute zero. Every supported compatible
state is a reduced progression modulo the actual flat lcm. The error
is bounded by the two endpoint maximum progression discrepancies.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

open Classical in
def pinnedIntegerDivisorPrimeCount {K : ℕ} (h : Fin K) (w m p₀ A B : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : ℕ :=
  ((auxiliaryPrimeInterval A B).filter fun q ↦ PinnedIntegerDivisorCondition h w m p₀ q d).card

open Classical in
def pinnedIntegerDivisorPrimeExpected {K : ℕ} (h : Fin K) (P : Finset ℕ)
    (w m p₀ Y A B : ℕ) (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : ℝ :=
  if d ∈ doubledCutoffDivisorTuples (PinnedShiftIndex h) P ∧
      DoubledDivisorPrimeCompatible P (roughPinnedFourierEdges h w m p₀ Y)
        (truncatedPinnedFourierCompanion m Y) d then
    ((auxiliaryPrimeInterval A B).card : ℝ) / (Nat.totient (pinnedFlatDivisorModulus h d) : ℝ)
  else 0

theorem pinnedIntegerDivisorPrimeCount_eq_progression
    {K w m p₀ A B r : ℕ} (h : Fin K)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hr : ∀ q : ℕ, PinnedIntegerDivisorCondition h w m p₀ q d ↔
      q ≡ r [MOD pinnedFlatDivisorModulus h d]) :
    pinnedIntegerDivisorPrimeCount h w m p₀ A B d =
      BoundedGaps.Maynard.primeVariableProgressionCount A B (pinnedFlatDivisorModulus h d) r := by
  classical
  unfold pinnedIntegerDivisorPrimeCount auxiliaryPrimeInterval
    BoundedGaps.Maynard.primeVariableProgressionCount
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter, hr, and_assoc]

theorem abs_pinnedIntegerDivisorPrimeCount_sub_expected_le
    {K w m p₀ Y A B : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hA : 0 < A) (hAB : A ≤ B)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ p ∈ P, p)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y) :
    |(pinnedIntegerDivisorPrimeCount h w m p₀ A B d : ℝ) -
      pinnedIntegerDivisorPrimeExpected h P w m p₀ Y A B d| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) (pinnedFlatDivisorModulus h d) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1) (pinnedFlatDivisorModulus h d) := by
  classical
  by_cases hallowed : d ∈ doubledCutoffDivisorTuples (PinnedShiftIndex h) P ∧
      DoubledDivisorPrimeCompatible P (roughPinnedFourierEdges h w m p₀ Y)
        (truncatedPinnedFourierCompanion m Y) d
  · obtain ⟨r, hrlt, hrcop, hr⟩ := exists_pinnedIntegerCrt_reduced_class_of_graph
      h P hP hrough hKw hm hp₀ hcop d hallowed.1 hDsmall hEsmall hallowed.2
    have hQpos := (pinnedFlatDivisorModulus_squarefree h P hP d hdiv).ne_zero.bot_lt
    have hrmem : r ∈ BoundedGaps.Maynard.coprimeResidues (pinnedFlatDivisorModulus h d) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hrcop⟩
    rw [pinnedIntegerDivisorPrimeCount_eq_progression h d hr,
      pinnedIntegerDivisorPrimeExpected, if_pos hallowed, cast_auxiliaryPrimeInterval_card hA hAB]
    exact (BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
      (q := pinnedFlatDivisorModulus h d) (r := r) hA hAB).trans
        (add_le_add (BoundedGaps.Maynard.progressionDiscrepancy_le_max hQpos hrmem)
          (BoundedGaps.Maynard.progressionDiscrepancy_le_max hQpos hrmem))
  · have hzero : pinnedIntegerDivisorPrimeCount h w m p₀ A B d = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro q hq hcond
      exact hallowed (pinnedIntegerDivisorCondition_implies_cutoff_graph h P hP hrough hKw
        hm hp₀ hcop d hdiv hDsmall hEsmall hcond)
    rw [hzero, Nat.cast_zero, pinnedIntegerDivisorPrimeExpected, if_neg hallowed,
      sub_zero, abs_zero]
    exact add_nonneg (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)

end

end Erdos4b

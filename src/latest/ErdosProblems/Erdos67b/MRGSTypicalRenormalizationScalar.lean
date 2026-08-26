import ErdosProblems.Erdos67b.MRGSTypicalPrefixRenormalization

/-!
# Quantitative error for full-family GS renormalization

A half-mass bound for the full deleted union applies to every submask.
The number of inclusion-exclusion terms is explicit, and on the central
window a small power bound on that count gives a decaying error.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrGS_primeMaskMass_mono {ι : Type*} {S J : Finset ι}
    (B : ι → Finset ℕ) (hSJ : S ⊆ J) (N : ℕ) :
    primeBandReciprocalMass (fun p ↦ p ∈ S.biUnion B) N ≤
      primeBandReciprocalMass (fun p ↦ p ∈ J.biUnion B) N := by
  classical
  unfold primeBandReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpN, hpS⟩ := Finset.mem_filter.mp hp
    obtain ⟨j, hj, hpB⟩ := Finset.mem_biUnion.mp hpS
    exact Finset.mem_filter.mpr ⟨hpN, Finset.mem_biUnion.mpr ⟨j, hSJ hj, hpB⟩⟩
  · intro p hp hnot
    positivity

theorem mrGS_norm_indexedTypical_centered_prefix_error_le_count
    {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (hbound : ∀ n, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hu : u ≠ 0)
    (hmass : primeBandReciprocalMass (fun p ↦ p ∈ J.biUnion B) N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) (t₁ + u) N / (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) t₁ N / (N : ℂ))‖ ≤
      (2 : ℝ) ^ J.card * gsA8DeletedErrorConstant * (1 + |u|) *
        (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
  classical
  apply (mrGS_norm_indexedTypical_centered_prefix_error_le_sum J B hB hmul hbound
    t₁ u hN hu).trans
  calc
    _ ≤ ∑ _S ∈ J.powerset,
        gsA8DeletedErrorConstant * (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      exact gsPrefixRenormalizationLinearError_deletePrimeBand_le_log_rpow hbound
        (fun p ↦ p ∈ S.biUnion B) t₁ u hN
        ((mrGS_primeMaskMass_mono B (Finset.mem_powerset.mp hS) N).trans hmass) hdist
    _ = _ := by simp [Finset.card_powerset, mul_assoc]

theorem mrGS_norm_indexedTypical_central_error_le_log_rpow
    {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (hbound : ∀ n, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hu : u ≠ 0)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hwindow : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hcount : (2 : ℝ) ^ J.card ≤ (Real.log (N : ℝ)) ^ (1 / 80 : ℝ))
    (hmass : primeBandReciprocalMass (fun p ↦ p ∈ J.biUnion B) N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    ‖gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) (t₁ + u) N / (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          (gsTwistedPositivePrefixSum (mrIndexedTypicalCoefficient J B f) t₁ N / (N : ℂ))‖ ≤
      2 * gsA8DeletedErrorConstant * (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
  have hbase := mrGS_norm_indexedTypical_centered_prefix_error_le_count J B hB hmul hbound
    t₁ u hN hu hmass hdist
  have hC := gsA8DeletedErrorConstant_nonneg
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hpowers : (Real.log (N : ℝ)) ^ (1 / 80 : ℝ) *
      (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) = (Real.log (N : ℝ)) ^ (-1 / 20 : ℝ) := by
    rw [← Real.rpow_add hLpos]
    norm_num
  calc
    _ ≤ (2 : ℝ) ^ J.card * gsA8DeletedErrorConstant *
        ((1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ)) := by
      simpa only [mul_assoc] using hbase
    _ ≤ (2 : ℝ) ^ J.card * gsA8DeletedErrorConstant *
        (2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_add_abs_mul_log_rpow_neg_eighth_le hlog hwindow)
        (mul_nonneg (by positivity) hC)
    _ ≤ (Real.log (N : ℝ)) ^ (1 / 80 : ℝ) * gsA8DeletedErrorConstant *
        (2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hC) (by positivity)
    _ = 2 * gsA8DeletedErrorConstant *
        ((Real.log (N : ℝ)) ^ (1 / 80 : ℝ) * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) := by ring
    _ = _ := by rw [hpowers]

end

end Erdos67b

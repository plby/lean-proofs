import ErdosProblems.Erdos421.ClippedBuchstabWindows

/-! # Total cutoff-error mass for the exact clipped prime partition -/

namespace Erdos421

open MeasureTheory

theorem clippedRoughError_integral_le {W Z : ℕ} (hW : 0 < W) (K N B : ℕ)
    (hZ : Z ≤ B + 1) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, clippedRoughError W Z K N B δ y) ≤
      ((N : ℝ)⁻¹ + 2 / (W : ℝ)) * (harmonic B : ℝ) ^ 2 :=
  partitioned_rough_cutoff_mass (clippedPrimeIndices W Z K N)
    (clippedPrimeLower W N) (clippedPrimeUpper Z N) B (by positivity) hδ
    (fun i _ ↦ clippedPrimeBlock_subset_Icc W Z N B hZ i)
    (clippedPrimePartition_disjoint W Z K N)
    (fun i hi ↦ clippedPrimeBlock_reciprocal_le hW hi)

theorem clippedCofactorError_integral_le (P : Finset ℕ) {W Z : ℕ} (hW : 0 < W) (K N B : ℕ)
    (hZ : Z ≤ B + 1) (hP : P ⊆ Finset.Icc 1 B) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, clippedCofactorError P W Z K N B δ y) ≤
      ((N : ℝ)⁻¹ + 2 / (W : ℝ)) * (harmonic B : ℝ) ^ 3 :=
  partitioned_cofactor_cutoff_mass (clippedPrimeIndices W Z K N)
    (clippedPrimeLower W N) (clippedPrimeUpper Z N) P B (by positivity) hδ hP
    (fun i _ ↦ clippedPrimeBlock_subset_Icc W Z N B hZ i)
    (clippedPrimePartition_disjoint W Z K N)
    (fun i hi ↦ clippedPrimeBlock_reciprocal_le hW hi)

end Erdos421

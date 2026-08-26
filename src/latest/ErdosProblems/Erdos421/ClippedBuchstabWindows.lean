import ErdosProblems.Erdos421.ClippedPrimeBounds
import ErdosProblems.Erdos421.PartitionedBuchstab
import ErdosProblems.Erdos421.RealProductWindowEnergy

/-! # Exact frozen-cutoff windows for the clipped prime partition -/

namespace Erdos421

open MeasureTheory

noncomputable def frozenRoughBuchstabWindow (W Z K N B : ℕ) (δ y : ℝ) : ℝ :=
  ∑ i ∈ clippedPrimeIndices W Z K N,
    logarithmicPrimeCofactorWindow (clippedPrimeBlock W Z N i) B (clippedPrimeLower W N i) δ y

noncomputable def frozenCofactorBuchstabWindow (P : Finset ℕ) (W Z K N B : ℕ) (δ y : ℝ) : ℝ :=
  ∑ i ∈ clippedPrimeIndices W Z K N,
    logarithmicDoubleCofactorWindow P (clippedPrimeBlock W Z N i) B (clippedPrimeLower W N i) δ y

noncomputable def clippedRoughError (W Z K N B : ℕ) (δ y : ℝ) : ℝ :=
  ∑ i ∈ clippedPrimeIndices W Z K N,
    logarithmicRoughBlockError B (clippedPrimeLower W N i) (clippedPrimeUpper Z N i) δ y

noncomputable def clippedCofactorError (P : Finset ℕ) (W Z K N B : ℕ) (δ y : ℝ) : ℝ :=
  ∑ i ∈ clippedPrimeIndices W Z K N,
    logarithmicCofactorBlockError P B (clippedPrimeLower W N i) (clippedPrimeUpper Z N i) δ y

theorem logarithmicRoughWindow_clipped_buchstab {W Z K N : ℕ} (hWZ : W ≤ Z)
    (hW : 2 ≤ W) (hZ : Z ≤ 2 ^ K + 1) (hN : 0 < N) (B : ℕ) (δ y : ℝ) :
    logarithmicRoughWindow B W δ y - logarithmicRoughWindow B Z δ y =
      frozenRoughBuchstabWindow W Z K N B δ y - clippedRoughError W Z K N B δ y :=
  logarithmicRoughWindow_partitioned_buchstab (clippedPrimeIndices W Z K N)
    (clippedPrimeLower W N) (clippedPrimeUpper Z N) B hWZ
    (clippedPrimePartition_disjoint W Z K N) (clippedPrimePartition_cover hW hZ hN) δ y

theorem logarithmicPrimeCofactorWindow_clipped_buchstab (P : Finset ℕ) {W Z K N : ℕ}
    (hWZ : W ≤ Z) (hW : 2 ≤ W) (hZ : Z ≤ 2 ^ K + 1) (hN : 0 < N) (B : ℕ) (δ y : ℝ) :
    logarithmicPrimeCofactorWindow P B W δ y - logarithmicPrimeCofactorWindow P B Z δ y =
      frozenCofactorBuchstabWindow P W Z K N B δ y - clippedCofactorError P W Z K N B δ y :=
  logarithmicPrimeCofactorWindow_partitioned_buchstab (clippedPrimeIndices W Z K N)
    (clippedPrimeLower W N) (clippedPrimeUpper Z N) P B hWZ
    (clippedPrimePartition_disjoint W Z K N) (clippedPrimePartition_cover hW hZ hN) δ y

theorem clippedRoughError_nonneg (W Z K N B : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ clippedRoughError W Z K N B δ y :=
  Finset.sum_nonneg (fun _ _ ↦ logarithmicRoughBlockError_nonneg B _ _ hδ y)

theorem clippedCofactorError_nonneg (P : Finset ℕ) (W Z K N B : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) : 0 ≤ clippedCofactorError P W Z K N B δ y :=
  Finset.sum_nonneg (fun _ _ ↦ logarithmicCofactorBlockError_nonneg P B _ _ hδ y)

theorem clippedRoughError_integrable (W Z K N B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (clippedRoughError W Z K N B δ) :=
  integrable_finsetSum _ (fun _ _ ↦ logarithmicRoughBlockError_integrable B _ _ hδ)

theorem clippedCofactorError_integrable (P : Finset ℕ) (W Z K N B : ℕ)
    {δ : ℝ} (hδ : 0 < δ) : Integrable (clippedCofactorError P W Z K N B δ) :=
  integrable_finsetSum _ (fun _ _ ↦ logarithmicCofactorBlockError_integrable P B _ _ hδ)

theorem frozenRoughBuchstabWindow_continuous (W Z K N B : ℕ) (δ : ℝ) :
    Continuous (frozenRoughBuchstabWindow W Z K N B δ) :=
  continuous_finsetSum _ (fun _ _ ↦ logarithmicPrimeCofactorWindow_continuous _ B _ δ)

theorem frozenCofactorBuchstabWindow_continuous (P : Finset ℕ) (W Z K N B : ℕ) (δ : ℝ) :
    Continuous (frozenCofactorBuchstabWindow P W Z K N B δ) :=
  continuous_finsetSum _ (fun _ _ ↦ logarithmicDoubleCofactorWindow_continuous P _ B _ δ)

end Erdos421

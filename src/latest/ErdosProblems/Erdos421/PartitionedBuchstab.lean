import ErdosProblems.Erdos421.PartitionedCutoffMass

/-! # Buchstab's identity with frozen prime-block cutoffs and exact errors -/

namespace Erdos421

theorem logarithmicRoughWindow_partitioned_buchstab {ι : Type*}
    (I : Finset ι) (w z : ι → ℕ) (B : ℕ) {W Z : ℕ} (hWZ : W ≤ Z)
    (hdisj : (I : Set ι).PairwiseDisjoint (fun i ↦ sievePrimes (w i) (z i)))
    (hcover : I.biUnion (fun i ↦ sievePrimes (w i) (z i)) = sievePrimes W Z)
    (δ y : ℝ) :
    logarithmicRoughWindow B W δ y - logarithmicRoughWindow B Z δ y =
      (∑ i ∈ I, logarithmicPrimeCofactorWindow (sievePrimes (w i) (z i)) B (w i) δ y) -
        ∑ i ∈ I, logarithmicRoughBlockError B (w i) (z i) δ y := by
  rw [logarithmicRoughWindow_buchstab B hWZ, add_sub_cancel_left,
    ← hcover, Finset.sum_biUnion hdisj, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [logarithmicPrimeCofactorWindow, logarithmicRoughBlockError, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem logarithmicPrimeCofactorWindow_partitioned_buchstab {ι : Type*}
    (I : Finset ι) (w z : ι → ℕ) (P : Finset ℕ) (B : ℕ) {W Z : ℕ} (hWZ : W ≤ Z)
    (hdisj : (I : Set ι).PairwiseDisjoint (fun i ↦ sievePrimes (w i) (z i)))
    (hcover : I.biUnion (fun i ↦ sievePrimes (w i) (z i)) = sievePrimes W Z)
    (δ y : ℝ) :
    logarithmicPrimeCofactorWindow P B W δ y - logarithmicPrimeCofactorWindow P B Z δ y =
      (∑ i ∈ I, ∑ q ∈ sievePrimes (w i) (z i), (q : ℝ)⁻¹ *
        logarithmicPrimeCofactorWindow P (B / q) (w i) δ (y - Real.log q)) -
          ∑ i ∈ I, logarithmicCofactorBlockError P B (w i) (z i) δ y := by
  rw [logarithmicPrimeCofactorWindow_buchstab P B hWZ, add_sub_cancel_left,
    ← hcover, Finset.sum_biUnion hdisj, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [logarithmicCofactorBlockError, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

end Erdos421

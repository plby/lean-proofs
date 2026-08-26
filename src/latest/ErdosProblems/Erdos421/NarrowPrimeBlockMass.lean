import ErdosProblems.Erdos421.NarrowPrimePartition
import ErdosProblems.Erdos421.PartitionedCutoffMass

/-! # Cutoff errors on the explicit subdivision of a dyadic interval -/

namespace Erdos421

open MeasureTheory

theorem primeSubdivision_subset_Icc {H N B j : ℕ} (hj : j < N) (hB : 2 * H ≤ B) :
    sievePrimes (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1)) ⊆
      Finset.Icc 1 B := by
  intro p hp
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp
    (Finset.mem_filter.mp (primeSubdivision_subset H N hj hp)).1
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem primeSubdivision_rough_cutoff_mass {H N B : ℕ} (hH : 0 < H) (hN : 0 < N)
    (hB : 2 * H ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, ∑ j ∈ Finset.range N, logarithmicRoughBlockError B
      (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1)) δ y) ≤
        ((N : ℝ)⁻¹ + (H : ℝ)⁻¹) * (harmonic B : ℝ) ^ 2 := by
  apply partitioned_rough_cutoff_mass (Finset.range N) _ _ B (by positivity) hδ
  · intro j hj
    exact primeSubdivision_subset_Icc (Finset.mem_range.mp hj) hB
  · exact sievePrimes_partition_disjoint _ (primeSubdivisionPoint_mono H N) N
  · intro j hj
    exact primeSubdivision_reciprocal_le hH hN j

theorem primeSubdivision_cofactor_cutoff_mass (P : Finset ℕ) {H N B : ℕ}
    (hH : 0 < H) (hN : 0 < N) (hB : 2 * H ≤ B) (hP : P ⊆ Finset.Icc 1 B)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, ∑ j ∈ Finset.range N, logarithmicCofactorBlockError P B
      (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1)) δ y) ≤
        ((N : ℝ)⁻¹ + (H : ℝ)⁻¹) * (harmonic B : ℝ) ^ 3 := by
  apply partitioned_cofactor_cutoff_mass (Finset.range N) _ _ P B (by positivity) hδ hP
  · intro j hj
    exact primeSubdivision_subset_Icc (Finset.mem_range.mp hj) hB
  · exact sievePrimes_partition_disjoint _ (primeSubdivisionPoint_mono H N) N
  · intro j hj
    exact primeSubdivision_reciprocal_le hH hN j

end Erdos421

import ErdosProblems.Erdos421.ClippedPrimeBlocks

/-! # The clipped blocks form a disjoint partition of the exact prime cutoff range -/

namespace Erdos421

theorem dyadic_prime_points_monotone : Monotone (fun k : ℕ ↦ 2 ^ k + 1) := by
  intro i j hij
  exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hij) 1

theorem clippedPrimePartition_cover {W Z K N : ℕ} (hW : 2 ≤ W)
    (hZ : Z ≤ 2 ^ K + 1) (hN : 0 < N) :
    (clippedPrimeIndices W Z K N).biUnion (clippedPrimeBlock W Z N) = sievePrimes W Z := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact clippedPrimeBlock_subset W Z N i hp
  · intro hp
    obtain ⟨⟨hpW, hpZ⟩, hpprime⟩ :=
      (show (W ≤ p ∧ p < Z) ∧ p.Prime from
        ⟨Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
    have hpbase : p ∈ sievePrimes (2 ^ 0 + 1) (2 ^ K + 1) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨by norm_num; omega, hpZ.trans_le hZ⟩, hpprime⟩
    rw [← sievePrimes_partition (fun k ↦ 2 ^ k + 1) dyadic_prime_points_monotone K] at hpbase
    obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hpbase
    have hpk' : p ∈ sievePrimes (2 ^ k + 1) (2 * 2 ^ k + 1) := by
      simpa only [pow_succ, mul_comm (2 ^ k) 2] using hpk
    rw [← primeSubdivision_partition (2 ^ k) hN] at hpk'
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpk'
    have hpclip : p ∈ clippedPrimeBlock W Z N (k, j) := by
      rw [clippedPrimeBlock_eq_inter]
      exact Finset.mem_inter.mpr ⟨hpj, hp⟩
    have hi : (k, j) ∈ clippedPrimeIndices W Z K N :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk, hj⟩, ⟨p, hpclip⟩⟩
    exact Finset.mem_biUnion.mpr ⟨(k, j), hi, hpclip⟩

theorem clippedPrimePartition_disjoint (W Z K N : ℕ) :
    (↑(clippedPrimeIndices W Z K N) : Set (ℕ × ℕ)).PairwiseDisjoint
      (clippedPrimeBlock W Z N) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hiB := clippedPrimeIndices_mem hi
  have hjB := clippedPrimeIndices_mem hj
  by_cases hfirst : i.1 = j.1
  · have hsecond : i.2 ≠ j.2 := by
      intro h
      exact hij (Prod.ext hfirst h)
    have hinner := sievePrimes_partition_disjoint (primeSubdivisionPoint (2 ^ i.1) N)
      (primeSubdivisionPoint_mono (2 ^ i.1) N) N
    have hpifull := clippedPrimeBlock_subset_subdivision W Z N i hpi
    have hpjfull := clippedPrimeBlock_subset_subdivision W Z N j hpj
    rw [← hfirst] at hpjfull
    exact Finset.disjoint_left.mp (hinner (Finset.mem_range.mpr hiB.2.1)
      (Finset.mem_range.mpr hjB.2.1) hsecond) hpifull hpjfull
  · have houter := sievePrimes_partition_disjoint (fun k ↦ 2 ^ k + 1)
      dyadic_prime_points_monotone K
    exact Finset.disjoint_left.mp (houter (Finset.mem_range.mpr hiB.1)
      (Finset.mem_range.mpr hjB.1) hfirst)
      (clippedPrimeBlock_subset_dyadic hi hpi) (clippedPrimeBlock_subset_dyadic hj hpj)

end Erdos421

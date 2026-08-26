import ErdosProblems.Erdos421.NarrowPrimePartition

/-! # Clipping the dyadic prime subdivision to an arbitrary cutoff interval -/

namespace Erdos421

def clippedPrimeLower (W N : ℕ) (i : ℕ × ℕ) : ℕ :=
  max W (primeSubdivisionPoint (2 ^ i.1) N i.2)

def clippedPrimeUpper (Z N : ℕ) (i : ℕ × ℕ) : ℕ :=
  min Z (primeSubdivisionPoint (2 ^ i.1) N (i.2 + 1))

def clippedPrimeBlock (W Z N : ℕ) (i : ℕ × ℕ) : Finset ℕ :=
  sievePrimes (clippedPrimeLower W N i) (clippedPrimeUpper Z N i)

def clippedPrimeIndices (W Z K N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range K) ×ˢ (Finset.range N)).filter (fun i ↦ (clippedPrimeBlock W Z N i).Nonempty)

theorem clippedPrimeBlock_eq_inter (W Z N : ℕ) (i : ℕ × ℕ) :
    clippedPrimeBlock W Z N i =
      sievePrimes (primeSubdivisionPoint (2 ^ i.1) N i.2)
        (primeSubdivisionPoint (2 ^ i.1) N (i.2 + 1)) ∩ sievePrimes W Z := by
  ext p
  simp only [clippedPrimeBlock, clippedPrimeLower, clippedPrimeUpper, sievePrimes,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_Ico, max_le_iff, lt_min_iff]
  tauto

theorem clippedPrimeBlock_subset (W Z N : ℕ) (i : ℕ × ℕ) :
    clippedPrimeBlock W Z N i ⊆ sievePrimes W Z := by
  rw [clippedPrimeBlock_eq_inter]
  exact Finset.inter_subset_right

theorem clippedPrimeBlock_subset_subdivision (W Z N : ℕ) (i : ℕ × ℕ) :
    clippedPrimeBlock W Z N i ⊆
      sievePrimes (primeSubdivisionPoint (2 ^ i.1) N i.2)
        (primeSubdivisionPoint (2 ^ i.1) N (i.2 + 1)) := by
  rw [clippedPrimeBlock_eq_inter]
  exact Finset.inter_subset_left

theorem clippedPrimeIndices_mem {W Z K N : ℕ} {i : ℕ × ℕ}
    (hi : i ∈ clippedPrimeIndices W Z K N) :
    i.1 < K ∧ i.2 < N ∧ (clippedPrimeBlock W Z N i).Nonempty := by
  obtain ⟨hi, hn⟩ := Finset.mem_filter.mp hi
  obtain ⟨hi₁, hi₂⟩ := Finset.mem_product.mp hi
  exact ⟨Finset.mem_range.mp hi₁, Finset.mem_range.mp hi₂, hn⟩

theorem clippedPrimeIndices_card_le (W Z K N : ℕ) :
    (clippedPrimeIndices W Z K N).card ≤ K * N := by
  apply (Finset.card_filter_le _ _).trans_eq
  rw [Finset.card_product, Finset.card_range, Finset.card_range]

theorem clippedPrimeBlock_subset_dyadic {W Z K N : ℕ} {i : ℕ × ℕ}
    (hi : i ∈ clippedPrimeIndices W Z K N) :
    clippedPrimeBlock W Z N i ⊆ sievePrimes (2 ^ i.1 + 1) (2 ^ (i.1 + 1) + 1) := by
  have hsub := (clippedPrimeBlock_subset_subdivision W Z N i).trans
    (primeSubdivision_subset (2 ^ i.1) N (clippedPrimeIndices_mem hi).2.1)
  simpa only [pow_succ, mul_comm (2 ^ i.1) 2] using hsub

end Erdos421

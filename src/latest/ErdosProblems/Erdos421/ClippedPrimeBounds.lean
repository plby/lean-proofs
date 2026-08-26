import ErdosProblems.Erdos421.ClippedPrimePartition

/-! # Uniform size and reciprocal bounds for the nonempty clipped prime blocks -/

namespace Erdos421

theorem clippedPrimeBlock_subset_Icc (W Z N B : ℕ) (hZ : Z ≤ B + 1) (i : ℕ × ℕ) :
    clippedPrimeBlock W Z N i ⊆ Finset.Icc 1 B := by
  intro p hp
  have hp' := clippedPrimeBlock_subset W Z N i hp
  have hprime := (Finset.mem_filter.mp hp').2
  have hpZ := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp').1).2
  exact Finset.mem_Icc.mpr ⟨hprime.pos, by omega⟩

theorem clippedPrimeBlock_parameters {W Z K N : ℕ} {i : ℕ × ℕ}
    (hi : i ∈ clippedPrimeIndices W Z K N) :
    ∃ H J : ℕ, 0 < H ∧ W ≤ H + 1 ∧ H < Z ∧ J ≤ H ∧
      clippedPrimeBlock W Z N i = primeBlockSupport H J := by
  have hiB := clippedPrimeIndices_mem hi
  have hN : 0 < N := by omega
  obtain ⟨p, hp⟩ := hiB.2.2
  let l := clippedPrimeLower W N i
  let u := clippedPrimeUpper Z N i
  have hpu : l ≤ p ∧ p < u := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
  have hWl : W ≤ l := le_max_left _ _
  have huZ : u ≤ Z := min_le_left _ _
  have hhead : 2 ^ i.1 + 1 ≤ l := by
    apply le_trans _ (le_max_right _ _)
    rw [← primeSubdivisionPoint_zero (2 ^ i.1) N]
    exact primeSubdivisionPoint_mono _ _ (Nat.zero_le i.2)
  have htail : u ≤ 2 * 2 ^ i.1 + 1 := by
    apply le_trans (min_le_right _ _) _
    rw [← primeSubdivisionPoint_last (2 ^ i.1) hN]
    exact primeSubdivisionPoint_mono _ _ (by omega : i.2 + 1 ≤ N)
  have hpow : 0 < (2 : ℕ) ^ i.1 := pow_pos (by decide) _
  refine ⟨l - 1, u - l, by omega, by omega, by omega, by omega, ?_⟩
  change sievePrimes l u = primeBlockSupport (l - 1) (u - l)
  ext q
  simp only [sievePrimes, primeBlockSupport, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hq⟩
    exact ⟨⟨by omega, by omega⟩, hq⟩
  · rintro ⟨⟨hlo, hhi⟩, hq⟩
    exact ⟨⟨by omega, by omega⟩, hq⟩

theorem clippedPrimeBlock_lower_dyadic_bound {W Z K N : ℕ} {i : ℕ × ℕ}
    (hi : i ∈ clippedPrimeIndices W Z K N) : W ≤ 2 * 2 ^ i.1 := by
  obtain ⟨p, hp⟩ := (clippedPrimeIndices_mem hi).2.2
  have hpW := (Finset.mem_Ico.mp
    (Finset.mem_filter.mp (clippedPrimeBlock_subset W Z N i hp)).1).1
  have hpupper := (Finset.mem_Ico.mp
    (Finset.mem_filter.mp (clippedPrimeBlock_subset_dyadic hi hp)).1).2
  rw [pow_succ] at hpupper
  omega

theorem clippedPrimeBlock_reciprocal_le {W Z K N : ℕ} (hW : 0 < W) {i : ℕ × ℕ}
    (hi : i ∈ clippedPrimeIndices W Z K N) :
    (∑ p ∈ clippedPrimeBlock W Z N i, (p : ℝ)⁻¹) ≤ (N : ℝ)⁻¹ + 2 / (W : ℝ) := by
  have hN : 0 < N := by have h := (clippedPrimeIndices_mem hi).2.1; omega
  have hH : 0 < (2 : ℕ) ^ i.1 := pow_pos (by decide) _
  have hHR : (0 : ℝ) < (2 ^ i.1 : ℕ) := by exact_mod_cast hH
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hinv : (((2 ^ i.1 : ℕ) : ℝ))⁻¹ ≤ 2 / (W : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hHR hWR).mpr
    simpa only [one_mul] using (show (W : ℝ) ≤ 2 * ((2 ^ i.1 : ℕ) : ℝ) by
      exact_mod_cast clippedPrimeBlock_lower_dyadic_bound hi)
  calc
    _ ≤ ∑ p ∈ sievePrimes (primeSubdivisionPoint (2 ^ i.1) N i.2)
        (primeSubdivisionPoint (2 ^ i.1) N (i.2 + 1)), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (clippedPrimeBlock_subset_subdivision W Z N i)
        (fun p _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg p))
    _ ≤ (N : ℝ)⁻¹ + (((2 ^ i.1 : ℕ) : ℝ))⁻¹ := primeSubdivision_reciprocal_le hH hN i.2
    _ ≤ _ := add_le_add_right hinv (N : ℝ)⁻¹

end Erdos421

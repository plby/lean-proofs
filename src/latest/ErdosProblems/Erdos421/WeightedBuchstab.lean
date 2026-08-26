import ErdosProblems.Erdos421.Buchstab

/-! # Weighted Buchstab decomposition and a prime minorant -/

namespace Erdos421

theorem weighted_buchstab_identity (C : Finset ℕ) (f : ℕ → ℝ) {w z : ℕ} (hwz : w ≤ z) :
    (∑ n ∈ sifted C w, f n) = (∑ n ∈ sifted C z, f n) +
      ∑ p ∈ sievePrimes w z, ∑ d ∈ sifted (sieveCofactors C p) p, f (p * d) := by
  classical
  rw [buchstab_partition C hwz,
    Finset.sum_union (sifted_disjoint_slices C w z), Finset.sum_biUnion]
  · congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hpprime := (Finset.mem_filter.mp hp).2
    rw [leastPrimeSlice_eq_image C hpprime, Finset.sum_image]
    intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hpprime.pos hab
  · intro p hp q hq hpq
    exact leastPrimeSlice_disjoint C hpq

theorem roughAt_prime_of_lt_square {n z : ℕ} (hn : 1 < n) (hnz : n < z ^ 2)
    (hrough : RoughAt n z) : n.Prime := by
  by_contra hp
  have hmin := (roughAt_iff_minFac.mp hrough).resolve_left (by omega)
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hp
  nlinarith

/-- Buchstab's decomposition, with a nonnegative remainder discarded, is a
pointwise lower bound for the weighted prime count. -/
theorem weighted_buchstab_prime_minorant (C : Finset ℕ) (f : ℕ → ℝ) {w z : ℕ}
    (hwz : w ≤ z) (hC : ∀ n ∈ C, 1 < n ∧ n < z ^ 2) (hf : ∀ n ∈ C, 0 ≤ f n) :
    (∑ n ∈ sifted C w, f n) -
      (∑ p ∈ sievePrimes w z, ∑ d ∈ sifted (sieveCofactors C p) w, f (p * d)) ≤
        ∑ p ∈ C.filter Nat.Prime, f p := by
  classical
  have hcofactor : (∑ p ∈ sievePrimes w z, ∑ d ∈ sifted (sieveCofactors C p) p, f (p * d)) ≤
      ∑ p ∈ sievePrimes w z, ∑ d ∈ sifted (sieveCofactors C p) w, f (p * d) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpprime := (Finset.mem_filter.mp hp).2
    have hwp := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hsub : sifted (sieveCofactors C p) p ⊆ sifted (sieveCofactors C p) w := by
      intro d hd
      obtain ⟨hdC, hdr⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hdC, hdr.mono hwp⟩
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro d hd hd'
    exact hf (p * d) ((mem_sieveCofactors hpprime.pos).mp (Finset.mem_filter.mp hd).1)
  have hprime : (∑ n ∈ sifted C z, f n) ≤ ∑ p ∈ C.filter Nat.Prime, f p := by
    have hsub : sifted C z ⊆ C.filter Nat.Prime := by
      intro n hn
      obtain ⟨hnC, hrough⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnC, roughAt_prime_of_lt_square
        (hC n hnC).1 (hC n hnC).2 hrough⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ ↦ hf n (Finset.mem_filter.mp hn).1)
  rw [weighted_buchstab_identity C f hwz]
  linarith

end Erdos421

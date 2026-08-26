import ErdosProblems.Erdos421.CanonicalLowerSieve

/-! # Finite divisor coefficients for the constructed lower sieve -/

namespace Erdos421

def lowerSievePairs (D z : ℕ) : Finset (ℕ × ℕ) :=
  (sievePrimes 0 z) ×ˢ Finset.Icc 1 (D ^ 2)

noncomputable def lowerSieveCoefficient (D z k : ℕ) : ℝ :=
  (if k = 1 then 1 else 0) -
    ∑ v ∈ (lowerSievePairs D z).filter (fun v ↦ v.1 * v.2 = k),
      canonicalUpperSieve D v.1 v.2

theorem lowerSievePairs_product_bounds {D z : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ lowerSievePairs D z) : 1 < v.1 * v.2 ∧ v.1 * v.2 ≤ z * D ^ 2 := by
  obtain ⟨hp, hd⟩ := Finset.mem_product.mp hv
  have hpprime := (Finset.mem_filter.mp hp).2
  have hpz := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2
  obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
  constructor
  · exact hpprime.one_lt.trans_le (Nat.le_mul_of_pos_right _ hd1)
  · exact Nat.mul_le_mul hpz.le hdD

theorem lowerSieveCoefficient_support {D z k : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z)
    (hk : z * D ^ 2 < k) : lowerSieveCoefficient D z k = 0 := by
  have hM : 1 ≤ z * D ^ 2 := Nat.mul_pos hz (pow_pos hD _)
  have hnot : k ≠ 1 := by omega
  unfold lowerSieveCoefficient
  rw [if_neg hnot, Finset.sum_eq_zero, sub_zero]
  intro v hv
  obtain ⟨hv, heq⟩ := Finset.mem_filter.mp hv
  have hbound := (lowerSievePairs_product_bounds hv).2
  omega

theorem lowerSieveCoefficient_action {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z)
    (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (z * D ^ 2), lowerSieveCoefficient D z k * f k) =
      f 1 - ∑ v ∈ lowerSievePairs D z, canonicalUpperSieve D v.1 v.2 * f (v.1 * v.2) := by
  have hM : 1 ≤ z * D ^ 2 := Nat.mul_pos hz (pow_pos hD _)
  have hmap : ∀ v ∈ lowerSievePairs D z, v.1 * v.2 ∈ Finset.Icc 1 (z * D ^ 2) := by
    intro v hv
    obtain ⟨hv1, hvM⟩ := lowerSievePairs_product_bounds hv
    exact Finset.mem_Icc.mpr ⟨by omega, hvM⟩
  have hfiber : (∑ k ∈ Finset.Icc 1 (z * D ^ 2),
      (∑ v ∈ (lowerSievePairs D z).filter (fun v ↦ v.1 * v.2 = k),
        canonicalUpperSieve D v.1 v.2) * f k) =
      ∑ v ∈ lowerSievePairs D z, canonicalUpperSieve D v.1 v.2 * f (v.1 * v.2) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap
      (fun v ↦ canonicalUpperSieve D v.1 v.2 * f (v.1 * v.2))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  simp only [lowerSieveCoefficient, sub_mul, Finset.sum_sub_distrib, hfiber]
  congr 1
  simp [ite_mul, Finset.mem_Icc, hM]

theorem canonicalUpper_sum_truncate (D z : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ (primeProductBelow z).divisors, canonicalUpperSieve D z d * f d) =
      ∑ d ∈ Finset.Icc 1 (D ^ 2), canonicalUpperSieve D z d * f d := by
  classical
  have hset : (primeProductBelow z).divisors.filter (fun d ↦ d ≤ D ^ 2) =
      (Finset.Icc 1 (D ^ 2)).filter (fun d ↦ d ∣ primeProductBelow z) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    have hP := (primeProductBelow_squarefree z).ne_zero
    constructor
    · rintro ⟨⟨hdP, _⟩, hdD⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdP (Nat.pos_of_ne_zero hP), hdD⟩, hdP⟩
    · rintro ⟨⟨_, hdD⟩, hdP⟩
      exact ⟨⟨hdP, hP⟩, hdD⟩
  calc
    _ = ∑ d ∈ (primeProductBelow z).divisors.filter (fun d ↦ d ≤ D ^ 2),
        canonicalUpperSieve D z d * f d := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs with h
      · rfl
      · rw [canonicalUpperSieve_support (by omega), zero_mul]
    _ = ∑ d ∈ (Finset.Icc 1 (D ^ 2)).filter (fun d ↦ d ∣ primeProductBelow z),
        canonicalUpperSieve D z d * f d := by rw [hset]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs with h
      · rfl
      · rw [canonicalUpperSieve_divisor_support D z d h, zero_mul]

theorem lowerSieveCoefficient_action_primes {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z)
    (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (z * D ^ 2), lowerSieveCoefficient D z k * f k) =
      f 1 - ∑ p ∈ sievePrimes 0 z, ∑ d ∈ (primeProductBelow p).divisors,
        canonicalUpperSieve D p d * f (p * d) := by
  rw [lowerSieveCoefficient_action hD hz, lowerSievePairs, Finset.sum_product]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact (canonicalUpper_sum_truncate D p (fun d ↦ f (p * d))).symm

end Erdos421

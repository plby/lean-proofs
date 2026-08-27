/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoordinateRecurrence

/-!
# Squarefree support and removal of one sieve coordinate

The weight of a product already enforces squarefreeness and all pairwise
coprimality conditions. Splitting off a coordinate changes the forbidden
modulus from `M` to `M * e`, with no additional support hypotheses.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem roughSieveWeight_eq_zero_of_not_squarefree (M : ℕ) (g : ℕ → ℝ)
    {n : ℕ} (hn : ¬Squarefree n) : roughSieveWeight M g n = 0 :=
  squarefreePrimeWeight_apply_of_not_squarefree _ hn

theorem roughSieveWeight_eq_zero_of_not_coprime (g : ℕ → ℝ)
    {M n : ℕ} (hn : ¬M.Coprime n) : roughSieveWeight M g n = 0 := by
  by_cases hsq : Squarefree n
  · obtain ⟨p, hp, hpM, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    rw [roughSieveWeight, squarefreePrimeWeight_apply_of_squarefree _ hsq]
    apply Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpn, hsq.ne_zero⟩)
    simp [hpM]
  · exact roughSieveWeight_eq_zero_of_not_squarefree M g hsq

theorem roughSieveWeight_support {M n : ℕ} {g : ℕ → ℝ}
    (hn : roughSieveWeight M g n ≠ 0) : Squarefree n ∧ M.Coprime n := by
  constructor
  · by_contra hsq
    exact hn (roughSieveWeight_eq_zero_of_not_squarefree M g hsq)
  · by_contra hcop
    exact hn (roughSieveWeight_eq_zero_of_not_coprime g hcop)

theorem roughSieveWeight_nonneg (M : ℕ) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → 0 ≤ g p) (n : ℕ) :
    0 ≤ roughSieveWeight M g n := by
  by_cases hsq : Squarefree n
  · rw [roughSieveWeight, squarefreePrimeWeight_apply_of_squarefree _ hsq]
    apply Finset.prod_nonneg
    intro p hp
    split_ifs with hpM
    · exact le_rfl
    · exact div_nonneg zero_le_one (hg p (Nat.prime_of_mem_primeFactors hp) hpM)
  · rw [roughSieveWeight_eq_zero_of_not_squarefree M g hsq]

theorem roughSieveWeight_modulus_mul_of_coprime (M : ℕ) (g : ℕ → ℝ)
    {e n : ℕ} (hen : e.Coprime n) :
    roughSieveWeight (M * e) g n = roughSieveWeight M g n := by
  by_cases hsq : Squarefree n
  · simp only [roughSieveWeight, squarefreePrimeWeight_apply_of_squarefree _ hsq]
    apply Finset.prod_congr rfl
    intro p hp
    have hpe := primeFactor_not_dvd_of_coprime hen hp
    simp only [(Nat.prime_of_mem_primeFactors hp).dvd_mul, hpe, or_false]
  · rw [roughSieveWeight_eq_zero_of_not_squarefree (M * e) g hsq,
      roughSieveWeight_eq_zero_of_not_squarefree M g hsq]

/-- The identity is unconditional: both sides vanish if either coordinate
is outside the squarefree, coprime support. -/
theorem roughSieveWeight_mul (M e n : ℕ) (g : ℕ → ℝ) :
    roughSieveWeight M g (e * n) =
      roughSieveWeight M g e * roughSieveWeight (M * e) g n := by
  by_cases hen : e.Coprime n
  · rw [roughSieveWeight_modulus_mul_of_coprime M g hen]
    exact (squarefreePrimeWeight_isMultiplicative _).map_mul_of_coprime hen
  · have hsq : ¬Squarefree (e * n) := fun h => hen (Nat.coprime_of_squarefree_mul h)
    have hcop : ¬(M * e).Coprime n := by
      obtain ⟨p, hp, hpe, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hen
      exact Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, dvd_mul_of_dvd_right hpe M, hpn⟩
    rw [roughSieveWeight_eq_zero_of_not_squarefree M g hsq,
      roughSieveWeight_eq_zero_of_not_coprime g hcop, mul_zero]

theorem sum_roughSieveWeight_mul (M e : ℕ) (g F : ℕ → ℝ) (S : Finset ℕ) :
    (∑ n ∈ S, F n * roughSieveWeight M g (e * n)) =
      roughSieveWeight M g e * (∑ n ∈ S, F n * roughSieveWeight (M * e) g n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [roughSieveWeight_mul]
  ring

/-- The analytic main-constant recurrence also extends over zero-weight
coordinates. This avoids adding support predicates to later finite sums. -/
theorem sieveMainConstant_coordinate_recurrence_all {k M : ℕ}
    (hk : 0 < k) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) (e : ℕ) :
    sieveMainConstant (M * e) g * roughSieveWeight M g e =
      sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e := by
  by_cases hsq : Squarefree e
  · by_cases hcop : M.Coprime e
    · exact sieveMainConstant_coordinate_recurrence hk hM hsq hcop hsmall g hg hclose
    · rw [roughSieveWeight_eq_zero_of_not_coprime g hcop,
        roughSieveWeight_eq_zero_of_not_coprime (fun p => g p + 1) hcop]
      simp
  · rw [roughSieveWeight_eq_zero_of_not_squarefree M g hsq,
      roughSieveWeight_eq_zero_of_not_squarefree M (fun p => g p + 1) hsq]
    simp

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.roughSieveWeight_mul
#print axioms Erdos4b.FGKMT.sieveMainConstant_coordinate_recurrence_all

import ErdosProblems.Erdos587.HooleyOddRootDensity
import ErdosProblems.Erdos587.EvenRootDensity

/-! # The even-modulus transfer with one log-log loss -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_even_root_density :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (e Q D R H X : ℕ), 0 < Q → (∀ p ∈ Q.primeFactors, p ≠ 2) →
        (2 : ℕ).Coprime Q → R.Coprime 8 → R.Coprime (primeSetModulus Q.primeFactors) →
        16 ≤ H → 2 * K ≤ H / 16 →
        (primeSetModulus Q.primeFactors : ℝ) ≤ ((H / 16 : ℕ) : ℝ) ^ 2 →
        primeSetModulus Q.primeFactors ≤ X →
        (H : ℝ) / (C * max 1 (Real.log (Real.log (X : ℝ)))) ≤
          ∑ i ∈ Finset.range H, (squareRootCount (2 ^ e * Q) (D + R * i) : ℝ) := by
  obtain ⟨K, hK, C, hC, hmean⟩ := exists_delta_unitSquareExpansion_density
  refine ⟨K, hK, 32 * C, by positivity, ?_⟩
  intro e Q D R H X hQ hodd h2 hR8 hR hH hL hroot hX
  obtain ⟨i₀, hi₀, hmod⟩ := exists_affine_unit_one_residue (D := D) (by norm_num : 0 < 8) hR8
  have hradDvd : primeSetModulus Q.primeFactors ∣ Q := Nat.prod_primeFactors_dvd Q
  have h8rad : (8 : ℕ).Coprime (primeSetModulus Q.primeFactors) := by
    have hh := (h2.of_dvd_right hradDvd).pow_left 3
    norm_num at hh
    exact hh
  have hR' : (8 * R).Coprime (primeSetModulus Q.primeFactors) := h8rad.mul_left hR
  have hraw := hmean Q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    hodd (D + R * i₀) (8 * R) (H / 16) X hR' hL hroot hX
  have hcount :
      (∑ j ∈ Finset.range (H / 16),
        unitSquareExpansionValue (primeSetModulus Q.primeFactors) (D + R * i₀ + (8 * R) * j)) ≤
      ∑ i ∈ Finset.range H, (squareRootCount (2 ^ e * Q) (D + R * i) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (H / 16),
          (squareRootCount (2 ^ e * Q) (D + R * i₀ + (8 * R) * j) : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact unitSquareExpansionValue_le_squareRootCount_two_mul_odd e Q _ hQ hodd h2
          (affine_eight_slice_modEq_one hmod j)
      _ = ∑ j ∈ Finset.range (H / 16),
          (squareRootCount (2 ^ e * Q) (D + R * (i₀ + 8 * j)) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun n : ℕ => (squareRootCount (2 ^ e * Q) n : ℝ)) (by ring)
      _ ≤ _ := affine_eight_slice_sum_le
        (fun i : ℕ => (squareRootCount (2 ^ e * Q) (D + R * i) : ℝ))
        H i₀ hi₀ (fun _ => Nat.cast_nonneg _)
  have hdenom : 0 < C * max 1 (Real.log (Real.log (X : ℝ))) := by positivity
  have hhalf : (H : ℝ) / 32 ≤ ((H / 16 : ℕ) : ℝ) := by
    have hh := half_div_le_nat_div 16 H (by norm_num) hH
    norm_num at hh
    exact hh
  calc
    _ = ((H : ℝ) / 32) / (C * max 1 (Real.log (Real.log (X : ℝ)))) := by ring
    _ ≤ ((H / 16 : ℕ) : ℝ) / (C * max 1 (Real.log (Real.log (X : ℝ)))) :=
      div_le_div_of_nonneg_right hhalf hdenom.le
    _ ≤ _ := hraw.trans hcount

end Erdos587

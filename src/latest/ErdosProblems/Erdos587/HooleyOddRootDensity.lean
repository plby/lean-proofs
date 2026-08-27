import ErdosProblems.Erdos587.HooleyRootEuler
import ErdosProblems.Erdos587.OddRootDensity

/-! # Uniform odd-modulus root density with one log-log loss -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_unitSquareExpansion_density :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p ≠ 2) →
      ∀ D R H X : ℕ, R.Coprime (primeSetModulus s) → 2 * K ≤ H →
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 → primeSetModulus s ≤ X →
      (H : ℝ) / (C * max 1 (Real.log (Real.log (X : ℝ)))) ≤
        ∑ i ∈ Finset.range H, unitSquareExpansionValue (primeSetModulus s) (D + R * i) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_unitSquareAffineDensityThreshold
  obtain ⟨A, hA, hEuler⟩ := exists_delta_primeSetUnitDensity_inv_bound
  let K := max 3 Q₀
  let C : ℝ := 2 * (K + A + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨K, by dsimp [K]; omega, C, hC, ?_⟩
  intro s hs hodd D R H X hR hH hroot hX
  let Q := primeSetModulus s
  let F := max 1 (Real.log (Real.log (X : ℝ)))
  have hQpos : 0 < Q := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have hF : 1 ≤ F := le_max_left _ _
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  have hHpos : 0 < H := by dsimp [K] at hH; omega
  change (H : ℝ) / (C * F) ≤ _
  by_cases hlarge : K ≤ Q
  · have hQthreshold : Q₀ ≤ Q := (le_max_right 3 Q₀).trans hlarge
    obtain ⟨M, hDM⟩ := exists_nat_affine_shift_of_coprime (D := D) hQpos hR
    have hmain := hQ₀ s hs hodd hQthreshold D R M H hR hDM hHpos hroot
    have hbound : (primeSetUnitDensity s)⁻¹ ≤ A * F := hEuler s hs X hX
    have hdenom : 2 * (A * F) ≤ C * F := by
      have hconst : 2 * A ≤ C := by
        dsimp [C]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hconst hFpos.le]
    calc
      _ ≤ (H : ℝ) / (2 * (A * F)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity) hdenom
      _ ≤ (H : ℝ) * primeSetUnitDensity s / 2 :=
        half_density_lower_of_inverse_bound (primeSetUnitDensity_pos s hs)
          (mul_pos hA hFpos) (Nat.cast_nonneg H) hbound
      _ ≤ _ := hmain
  · have hQK : Q ≤ K := by omega
    have htwo : 2 * Q ≤ H := (Nat.mul_le_mul_left 2 hQK).trans hH
    have hdenom : 2 * (Q : ℝ) ≤ C * F := by
      have hconst : 2 * (Q : ℝ) ≤ C := by
        have hQKR : (Q : ℝ) ≤ K := by exact_mod_cast hQK
        dsimp [C]
        linarith
      exact hconst.trans (le_mul_of_one_le_right hC.le hF)
    calc
      _ ≤ (H : ℝ) / (2 * Q) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity) hdenom
      _ ≤ _ := unitSquareExpansion_affine_sum_lower_of_two_periods (D := D) hQpos hR htwo

theorem exists_delta_odd_root_density :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ q D R H X : ℕ, 0 < q → (∀ p ∈ q.primeFactors, p ≠ 2) →
      R.Coprime (primeSetModulus q.primeFactors) → 2 * K ≤ H →
      (primeSetModulus q.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 →
      primeSetModulus q.primeFactors ≤ X →
      (H : ℝ) / (C * max 1 (Real.log (Real.log (X : ℝ)))) ≤
        ∑ i ∈ Finset.range H, (squareRootCount q (D + R * i) : ℝ) := by
  obtain ⟨K, hK, C, hC, hmean⟩ := exists_delta_unitSquareExpansion_density
  refine ⟨K, hK, C, hC, ?_⟩
  intro q D R H X hq hodd hR hH hroot hX
  have : NeZero q := ⟨hq.ne'⟩
  apply (hmean q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    hodd D R H X hR hH hroot hX).trans
  exact Finset.sum_le_sum (fun i hi => unitSquareExpansionValue_le_squareRootCount_odd hodd _)

end Erdos587

import ErdosProblems.Erdos587.HooleyEvenRootDensity
import ErdosProblems.Erdos587.CompleteRootDensity

/-! # Complete-root density with one log-log loss for every positive modulus -/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_complete_root_density :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ q D R H X : ℕ, 0 < q → R.Coprime q → A * Real.sqrt q ≤ H → q ≤ X →
      (H : ℝ) / (C * max 1 (Real.log (Real.log (X : ℝ)))) ≤
        ∑ i ∈ Finset.range H, (squareRootCount q (D + R * i) : ℝ) := by
  obtain ⟨K₁, hK₁, C₁, hC₁, hoddMean⟩ := exists_delta_odd_root_density
  obtain ⟨K₂, _hK₂, C₂, hC₂, hevenMean⟩ := exists_delta_even_root_density
  let K := max K₁ K₂
  refine ⟨32 * (2 * (K : ℝ) + 1), by positivity, C₁ + C₂, by positivity, ?_⟩
  intro q D R H X hq hR hscale hqX
  have hK : 3 ≤ K := hK₁.trans (le_max_left _ _)
  obtain ⟨hHK, hH16, hHL, hqL⟩ := root_density_scale_budgets K q H hK hq hscale
  have hHK₁ : 2 * K₁ ≤ H := by dsimp [K] at hHK; omega
  have hLK₂ : 2 * K₂ ≤ H / 16 := (Nat.mul_le_mul_left 2 (le_max_right _ _)).trans hHL
  by_cases htwo : 2 ∣ q
  · let e := q.factorization 2
    let Q := ordCompl[2] q
    have hQ : 0 < Q := Nat.ordCompl_pos 2 hq.ne'
    have hfactor : 2 ^ e * Q = q := Nat.ordProj_mul_ordCompl_eq_self q 2
    have hQdvd : Q ∣ q := ⟨2 ^ e, by rw [mul_comm]; exact hfactor.symm⟩
    have h2Q : (2 : ℕ).Coprime Q := Nat.coprime_ordCompl Nat.prime_two hq.ne'
    have hodd : ∀ p ∈ Q.primeFactors, p ≠ 2 := by
      intro p hp hp2
      subst p
      exact Nat.not_dvd_ordCompl Nat.prime_two hq.ne' (Nat.dvd_of_mem_primeFactors hp)
    have hR8 : R.Coprime 8 := by
      have hh := (hR.of_dvd_right htwo).pow_right 3
      norm_num at hh
      exact hh
    have hradDvd : primeSetModulus Q.primeFactors ∣ q :=
      (Nat.prod_primeFactors_dvd Q).trans hQdvd
    have hradLe : primeSetModulus Q.primeFactors ≤ q := Nat.le_of_dvd hq hradDvd
    have hroot : (primeSetModulus Q.primeFactors : ℝ) ≤ ((H / 16 : ℕ) : ℝ) ^ 2 :=
      (by exact_mod_cast hradLe : (primeSetModulus Q.primeFactors : ℝ) ≤ q).trans hqL
    have hraw := hevenMean e Q D R H X hQ hodd h2Q hR8 (hR.of_dvd_right hradDvd)
      hH16 hLK₂ hroot (hradLe.trans hqX)
    rw [hfactor] at hraw
    apply le_trans _ hraw
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ C₁ + C₂) (by positivity))
  · have hodd : ∀ p ∈ q.primeFactors, p ≠ 2 := by
      intro p hp hp2
      subst p
      exact htwo (Nat.dvd_of_mem_primeFactors hp)
    have hradLe := root_density_radical_le q hq
    have hradDvd : primeSetModulus q.primeFactors ∣ q := Nat.prod_primeFactors_dvd q
    have hroot : (primeSetModulus q.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 := by
      calc
        _ ≤ (q : ℝ) := by exact_mod_cast hradLe
        _ ≤ ((H / 16 : ℕ) : ℝ) ^ 2 := hqL
        _ ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _)
          (by exact_mod_cast Nat.div_le_self H 16) 2
    have hraw := hoddMean q D R H X hq hodd (hR.of_dvd_right hradDvd)
      hHK₁ hroot (hradLe.trans hqX)
    apply le_trans _ hraw
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith : C₁ ≤ C₁ + C₂) (by positivity))

end Erdos587

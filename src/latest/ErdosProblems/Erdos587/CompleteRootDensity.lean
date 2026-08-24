import ErdosProblems.Erdos587.EvenRootDensity

/-!
# Uniform complete-root density for every positive modulus

Above a fixed multiple of the square-root scale, an affine interval with
unit step has a positive root count with only a fixed logarithmic loss.
-/

open scoped BigOperators

namespace Erdos587

lemma root_density_lower_mono (p q H : ℕ) {c C : ℝ} {o O : ℕ}
    (hp : 0 < p) (hpq : p ≤ q) (hc : 0 < c) (hcC : c ≤ C) (ho : o ≤ O) :
    (H : ℝ) / (C * (1 + Real.log q) ^ O) ≤
      (H : ℝ) / (c * (1 + Real.log p) ^ o) := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hlogpq : Real.log p ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpq)
  have hlogq : 0 ≤ Real.log q := hlogp.trans hlogpq
  have hpow : (1 + Real.log p) ^ o ≤ (1 + Real.log q) ^ O :=
    (pow_le_pow_left₀ (by linarith) (by linarith) o).trans
      (pow_le_pow_right₀ (by linarith) ho)
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity)
  calc
    c * (1 + Real.log p) ^ o ≤ c * (1 + Real.log q) ^ O :=
      mul_le_mul_of_nonneg_left hpow hc.le
    _ ≤ C * (1 + Real.log q) ^ O := mul_le_mul_of_nonneg_right hcC (by positivity)

lemma root_density_scale_budgets (K q H : ℕ) (hK : 3 ≤ K) (hq : 0 < q)
    (hscale : (32 : ℝ) * (2 * K + 1) * Real.sqrt q ≤ H) :
    32 * K ≤ H ∧ 16 ≤ H ∧ 2 * K ≤ H / 16 ∧
      (q : ℝ) ≤ ((H / 16 : ℕ) : ℝ) ^ 2 := by
  let A : ℝ := 32 * (2 * K + 1)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA32 : 32 ≤ A := by dsimp [A]; have := Nat.cast_nonneg (α := ℝ) K; linarith
  have hAK : 32 * (K : ℝ) ≤ A := by dsimp [A]; have := Nat.cast_nonneg (α := ℝ) K; linarith
  have hsqrtOne : 1 ≤ Real.sqrt (q : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hq)
  have hHA : A ≤ (H : ℝ) := (le_mul_of_one_le_right hA0 hsqrtOne).trans hscale
  have hHK : 32 * K ≤ H := by exact_mod_cast hAK.trans hHA
  have hH16 : 16 ≤ H := by omega
  have hL : 2 * K ≤ H / 16 := by omega
  have hsqrt : Real.sqrt (q : ℝ) ≤ (H : ℝ) / 32 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    calc
      _ = (32 : ℝ) * Real.sqrt q := by ring
      _ ≤ A * Real.sqrt q := mul_le_mul_of_nonneg_right hA32 (Real.sqrt_nonneg _)
      _ ≤ H := hscale
  have hhalf : (H : ℝ) / 32 ≤ ((H / 16 : ℕ) : ℝ) := by
    have hh := half_div_le_nat_div 16 H (by norm_num) hH16
    norm_num at hh
    exact hh
  have hsquares := pow_le_pow_left₀ (Real.sqrt_nonneg (q : ℝ)) (hsqrt.trans hhalf) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg q)] at hsquares
  exact ⟨hHK, hH16, hL, hsquares⟩

lemma root_density_radical_le (q : ℕ) (hq : 0 < q) :
    primeSetModulus q.primeFactors ≤ q :=
  Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

theorem exists_complete_root_density_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q D R H : ℕ), 0 < q → R.Coprime q → A * Real.sqrt q ≤ H →
        (H : ℝ) / (C * (1 + Real.log q) ^ O) ≤
          ∑ i ∈ Finset.range H, (squareRootCount q (D + R * i) : ℝ) := by
  obtain ⟨K₁, hK₁, C₁, hC₁, O₁, hO₁, hoddMean⟩ := exists_uniform_odd_root_density
  obtain ⟨K₂, hK₂, C₂, hC₂, O₂, hO₂, hevenMean⟩ := exists_even_root_density
  let K := max K₁ K₂
  refine ⟨32 * (2 * (K : ℝ) + 1), by positivity,
    C₁ + C₂, by positivity, O₁ + O₂, by omega, ?_⟩
  intro q D R H hq hR hscale
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
    have hradPos : 0 < primeSetModulus Q.primeFactors :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have hroot : (primeSetModulus Q.primeFactors : ℝ) ≤ ((H / 16 : ℕ) : ℝ) ^ 2 :=
      (by exact_mod_cast hradLe : (primeSetModulus Q.primeFactors : ℝ) ≤ q).trans hqL
    have hraw := hevenMean e Q D R H hQ hodd h2Q hR8 (hR.of_dvd_right hradDvd)
      hH16 hLK₂ hroot
    rw [hfactor] at hraw
    exact (root_density_lower_mono _ q H hradPos hradLe hC₂ (by linarith)
      (by omega : O₂ ≤ O₁ + O₂)).trans hraw
  · have hodd : ∀ p ∈ q.primeFactors, p ≠ 2 := by
      intro p hp hp2
      subst p
      exact htwo (Nat.dvd_of_mem_primeFactors hp)
    have hradLe := root_density_radical_le q hq
    have hradPos : 0 < primeSetModulus q.primeFactors :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have hradDvd : primeSetModulus q.primeFactors ∣ q := Nat.prod_primeFactors_dvd q
    have hroot : (primeSetModulus q.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 := by
      calc
        _ ≤ (q : ℝ) := by exact_mod_cast hradLe
        _ ≤ ((H / 16 : ℕ) : ℝ) ^ 2 := hqL
        _ ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _)
          (by exact_mod_cast Nat.div_le_self H 16) 2
    have hraw := hoddMean q D R H hq hodd (hR.of_dvd_right hradDvd) hHK₁ hroot
    exact (root_density_lower_mono _ q H hradPos hradLe hC₁ (by linarith)
      (by omega : O₁ ≤ O₁ + O₂)).trans hraw

end Erdos587

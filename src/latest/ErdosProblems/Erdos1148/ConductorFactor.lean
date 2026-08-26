import ErdosProblems.Erdos1148.DivisorBounds

/-!
# The elementary lower bound for quadratic-order conductor factors

The class-number/regulator comparison for orders involves
`f * ∏ p ∣ f, (1 - χ(p)/p)`. This module bounds that numerical factor
below by every power `f^(1-ε)`. It proves neither the comparison formula
nor Siegel's lower bound for fundamental discriminants.
-/

namespace Erdos1148.DukeArithmetic

noncomputable def conductorFactor (f : ℕ) (χ : ℕ → ℝ) : ℝ :=
  f * ∏ p ∈ f.primeFactors, (1 - χ p / p)

lemma conductor_local_factor_ge_half {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : x ≤ 1) :
    1 / 2 ≤ 1 - x / p := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hdiv : x / p ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith

lemma one_le_divisors_mul_conductorProduct {f : ℕ} (hf : f ≠ 0) (χ : ℕ → ℝ)
    (hχ : ∀ p ∈ f.primeFactors, χ p ≤ 1) :
    1 ≤ (f.divisors.card : ℝ) * ∏ p ∈ f.primeFactors, (1 - χ p / p) := by
  have hcard : (f.divisors.card : ℝ) =
      ∏ p ∈ f.primeFactors, ((f.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hf, Nat.cast_prod]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.one_le_prod
  intro p hp
  have hk : 0 < f.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hf
      (Nat.dvd_of_mem_primeFactors hp)
  have hkR : (2 : ℝ) ≤ (f.factorization p : ℝ) + 1 := by
    exact_mod_cast (show 2 ≤ f.factorization p + 1 by omega)
  have hlocal := conductor_local_factor_ge_half (Nat.prime_of_mem_primeFactors hp) (hχ p hp)
  have hmul := mul_le_mul hkR hlocal (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)
  norm_num at hmul
  exact hmul

theorem exists_conductorFactor_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℕ) (χ : ℕ → ℝ), f ≠ 0 →
      (∀ p ∈ f.primeFactors, χ p ≤ 1) →
      c * (f : ℝ) ^ (1 - ε) ≤ conductorFactor f χ := by
  obtain ⟨C, hC, hbound⟩ := exists_card_divisors_le_rpow hε
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro f χ hf hχ
  have hfR : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero hf
  let P := ∏ p ∈ f.primeFactors, (1 - χ p / p)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun p hp =>
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
      (conductor_local_factor_ge_half (Nat.prime_of_mem_primeFactors hp) (hχ p hp)))
  have hone : 1 ≤ (C * (f : ℝ) ^ ε) * P :=
    (one_le_divisors_mul_conductorProduct hf χ hχ).trans
      (mul_le_mul_of_nonneg_right (hbound f hf) hP)
  have hlower : (C * (f : ℝ) ^ ε)⁻¹ ≤ P := by
    rw [inv_le_iff_one_le_mul₀' (by positivity)]
    exact hone
  calc
    C⁻¹ * (f : ℝ) ^ (1 - ε) = f * (C * (f : ℝ) ^ ε)⁻¹ := by
      rw [Real.rpow_sub hfR, Real.rpow_one, mul_inv_rev, div_eq_mul_inv]
      ring
    _ ≤ f * P := mul_le_mul_of_nonneg_left hlower hfR.le
    _ = conductorFactor f χ := rfl

end Erdos1148.DukeArithmetic

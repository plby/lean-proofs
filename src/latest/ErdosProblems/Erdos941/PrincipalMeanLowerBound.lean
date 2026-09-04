import ErdosProblems.Erdos941.PrincipalCharacterMean
import ErdosProblems.Erdos941.DivisorBounds

/-! # A subpower lower bound for the density of invertible residues -/

namespace Erdos941.Analytic

open Finset

theorem principalCharacterMean_eq_prod {q : ℕ} [NeZero q] :
    principalCharacterMean q = ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  push_cast at h
  apply (div_eq_iff (by exact_mod_cast NeZero.ne q : (q : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h

theorem one_le_divisorCount_mul_principalMean (q : ℕ) [NeZero q] :
    1 ≤ (q.divisors.card : ℝ) * principalCharacterMean q := by
  rw [Nat.card_divisors (NeZero.ne q), Nat.cast_prod, principalCharacterMean_eq_prod,
    ← prod_mul_distrib]
  apply one_le_prod
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have he : (2 : ℝ) ≤ (q.factorization p + 1 : ℕ) := by
    have hh := hp'.factorization_pos_of_dvd (NeZero.ne q) (Nat.dvd_of_mem_primeFactors hp)
    exact_mod_cast (show 2 ≤ q.factorization p + 1 by omega)
  have hi : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hp0).mpr (by linarith)
  nlinarith

theorem exists_principalMean_lower_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, q ≠ 0 →
      c * (q : ℝ) ^ (-δ) ≤ principalCharacterMean q := by
  obtain ⟨D, hD, hbound⟩ := exists_card_divisors_le_rpow hδ
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hmul : 1 ≤ (D * (q : ℝ) ^ δ) * principalCharacterMean q :=
    (one_le_divisorCount_mul_principalMean q).trans
      (mul_le_mul_of_nonneg_right (hbound q hq) (principalCharacterMean_nonneg q))
  have hdiv : 1 / (D * (q : ℝ) ^ δ) ≤ principalCharacterMean q :=
    (div_le_iff₀ (mul_pos hD (Real.rpow_pos_of_pos hqR δ))).mpr
      (by simpa only [mul_comm (principalCharacterMean q)] using hmul)
  simpa only [one_div, mul_inv_rev, Real.rpow_neg hqR.le, mul_comm] using hdiv

end Erdos941.Analytic

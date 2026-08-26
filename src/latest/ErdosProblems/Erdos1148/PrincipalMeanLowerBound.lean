import ErdosProblems.Erdos1148.PrincipalCharacterMean
import ErdosProblems.Erdos1148.ResidueUnitLowerBound

/-! # A subpower lower bound for the proportion of invertible residue classes -/

namespace Erdos1148.DukeArithmetic

open Finset

lemma principalCharacterMean_eq_prod {q : ℕ} [NeZero q] :
    principalCharacterMean q = ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  push_cast at h
  apply (div_eq_iff (by exact_mod_cast NeZero.ne q : (q : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h

theorem one_le_four_pow_primeFactors_mul_principalMean {q : ℕ} [NeZero q] :
    1 ≤ (4 : ℝ) ^ q.primeFactors.card * principalCharacterMean q := by
  rw [principalCharacterMean_eq_prod, ← prod_const, ← prod_mul_distrib]
  apply one_le_prod
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp0).mpr
    linarith
  linarith

theorem exists_principalMean_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, q ≠ 0 →
      c * (q : ℝ) ^ (-ε) ≤ principalCharacterMean q := by
  obtain ⟨C, hC, hLoss⟩ := exists_four_pow_primeFactors_le_rpow hε
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hmul : 1 ≤ (C * (q : ℝ) ^ ε) * principalCharacterMean q :=
    one_le_four_pow_primeFactors_mul_principalMean.trans
      (mul_le_mul_of_nonneg_right (hLoss q hq) (principalCharacterMean_nonneg q))
  have hdiv : 1 / (C * (q : ℝ) ^ ε) ≤ principalCharacterMean q :=
    (div_le_iff₀ (mul_pos hC (Real.rpow_pos_of_pos hqR ε))).mpr
      (by simpa only [mul_comm (principalCharacterMean q)] using hmul)
  simpa only [one_div, mul_inv_rev, Real.rpow_neg hqR.le, mul_comm] using hdiv

end Erdos1148.DukeArithmetic

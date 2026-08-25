import ErdosProblems.Erdos1141.BurgessDenominators
import ErdosProblems.Erdos1141.BurgessSubpower

/-!
# A subpower lower bound for the admissible amplifier denominators
-/

namespace Pollack17.Burgess

open Filter

theorem coprimeDenominators_lower_half (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hU : 2 * (4 : ℝ) ^ s.card ≤ U) :
    (U : ℝ) / (2 * (2 : ℝ) ^ s.card) ≤ (coprimeDenominators s U).card := by
  let a := (2 : ℝ) ^ s.card
  have ha : 0 < a := by dsimp [a]; positivity
  have h4 : (4 : ℝ) ^ s.card = a ^ 2 := by
    dsimp [a]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hUa : 2 * a ^ 2 ≤ (U : ℝ) := by simpa only [h4] using hU
  have hcalc : ((U : ℝ) / a - a) * (2 * a) = 2 * U - 2 * a ^ 2 := by
    field_simp
  have hhalf : (U : ℝ) / (2 * a) ≤ (U : ℝ) / a - a := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
    rw [hcalc]
    linarith
  have hbound := card_coprimeDenominators_lower s hs U
  have hmain : (U : ℝ) * (1 / 2 : ℝ) ^ s.card = (U : ℝ) / a := by
    simp [a, div_eq_mul_inv, inv_pow]
  rw [hmain] at hbound
  exact hhalf.trans hbound

theorem eventually_coprimeDenominators_lower {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (_hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      ∀ U : ℕ, (primeModulus s : ℝ) ^ u ≤ U →
        (U : ℝ) * (primeModulus s : ℝ) ^ (-δ) ≤ (coprimeDenominators s U).card := by
  have h₁ := eventually_const_mul_pow_primeFactors_le 2 4 (by omega) hu
  have h₂ := eventually_const_mul_pow_primeFactors_le 2 2 (by omega) hδ
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (h₁.and h₂)
  refine ⟨Q, fun s hs hq U hU => ?_⟩
  have h4 : 2 * (4 : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ u := by
    simpa only [primeModulus_primeFactors s hs, Nat.cast_ofNat] using (hQ (primeModulus s) hq).1
  have h2 : 2 * (2 : ℝ) ^ s.card ≤ (primeModulus s : ℝ) ^ δ := by
    simpa only [primeModulus_primeFactors s hs, Nat.cast_ofNat] using (hQ (primeModulus s) hq).2
  have hi := inv_anti₀ (by positivity : (0 : ℝ) < 2 * 2 ^ s.card) h2
  have hi' : (primeModulus s : ℝ) ^ (-δ) ≤ (2 * (2 : ℝ) ^ s.card)⁻¹ := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using hi
  calc
    _ ≤ (U : ℝ) / (2 * (2 : ℝ) ^ s.card) := by
      exact mul_le_mul_of_nonneg_left hi' (Nat.cast_nonneg U)
    _ ≤ _ := coprimeDenominators_lower_half s hs U (h4.trans hU)

end Pollack17.Burgess

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularRatios

/-!
# Exact small-prime ratios for the pinned coverage normalization

At a small cofactor prime the ratio is `1 - 1/p`, hence it is exactly
one half at two. At every other odd small prime it is at least one.
-/

namespace Erdos4b

noncomputable section

theorem pinnedLocalFactor_small_eq_inverse_power
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hpw : p.val ≤ w)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    pinnedLocalFactor h w m p₀ p = (1 - 1 / (p : ℝ))⁻¹ ^ (2 * (K - 1)) := by
  rw [pinnedLocalFactor, pinnedLocalMultiplicity,
    pinnedLocalForbiddenResidues_eq_empty_of_le_cutoff h p hpw hpp₀ hnum,
    Finset.card_empty, Nat.cast_zero, zero_div, sub_zero, one_mul, card_pinnedShiftIndex]

theorem pinnedSmallLocalRatio_eq_of_cofactor
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hpw : p.val ≤ w)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hpm : p.val ∣ m) :
    pinnedLocalFactor h w m p₀ p /
      largeGapLocalFactor (preSievedShifts K w) m 1 p = 1 - 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hb : 1 - 1 / (p : ℝ) ≠ 0 := (sub_pos.mpr ((div_lt_one hp0).mpr hp1)).ne'
  have hc : ((p : ℝ) - 1) / p ≠ 0 := div_ne_zero (by linarith) hp0.ne'
  have hdim : 2 * K = 2 * (K - 1) + 2 := by have := h.pos; omega
  calc
    _ = (1 * (1 - 1 / (p : ℝ))⁻¹ ^ (2 * (K - 1))) /
        ((((p : ℝ) - 1) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (2 * (K - 1) + 2)) := by
      rw [pinnedLocalFactor_small_eq_inverse_power h p hpw hpp₀ hnum,
        largeGapLocalFactor_preSievedShifts h.pos p.property hpw, if_pos hpm, hdim, one_mul]
    _ = (1 - 1 / (p : ℝ)) ^ 2 * 1 / (((p : ℝ) - 1) / p) :=
      cancel_two_inverse_powers _ _ _ _ hb hc
    _ = _ := by
      field_simp

theorem pinnedSmallLocalRatio_eq_of_not_cofactor
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hpw : p.val ≤ w) (hp2 : 2 < p.val)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hpm : ¬p.val ∣ m) :
    pinnedLocalFactor h w m p₀ p / largeGapLocalFactor (preSievedShifts K w) m 1 p =
      (1 - 1 / (p : ℝ)) ^ 2 / (1 - 2 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hp2R : (2 : ℝ) < p := by exact_mod_cast hp2
  have hb : 1 - 1 / (p : ℝ) ≠ 0 := (sub_pos.mpr ((div_lt_one hp0).mpr hp1)).ne'
  have hc : ((p : ℝ) - 2) / p ≠ 0 := div_ne_zero (by linarith) hp0.ne'
  have hdim : 2 * K = 2 * (K - 1) + 2 := by have := h.pos; omega
  calc
    _ = (1 * (1 - 1 / (p : ℝ))⁻¹ ^ (2 * (K - 1))) /
        ((((p : ℝ) - 2) / p) * (1 - 1 / (p : ℝ))⁻¹ ^ (2 * (K - 1) + 2)) := by
      rw [pinnedLocalFactor_small_eq_inverse_power h p hpw hpp₀ hnum,
        largeGapLocalFactor_preSievedShifts h.pos p.property hpw, if_neg hpm, hdim, one_mul]
    _ = (1 - 1 / (p : ℝ)) ^ 2 * 1 / (((p : ℝ) - 2) / p) :=
      cancel_two_inverse_powers _ _ _ _ hb hc
    _ = _ := by
      rw [mul_one, sub_div, div_self hp0.ne']

theorem one_le_pinnedSmallLocalRatio_of_not_cofactor
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hpw : p.val ≤ w) (hp2 : 2 < p.val)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hpm : ¬p.val ∣ m) :
    1 ≤ pinnedLocalFactor h w m p₀ p / largeGapLocalFactor (preSievedShifts K w) m 1 p := by
  rw [pinnedSmallLocalRatio_eq_of_not_cofactor h p hpw hp2 hpp₀ hnum hpm]
  have hpR : (2 : ℝ) * 1 < p := by exact_mod_cast hp2
  simpa only [mul_one, sub_self, zero_div, sub_zero] using
    one_le_pinned_noncofactor_ratio (by norm_num : (1 : ℝ) ≤ 1) hpR

end

end Erdos4b

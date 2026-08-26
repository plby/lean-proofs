/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularRatioAlgebra

/-!
# Exact local cancellation of pinned and unpinned singular factors

The power normalization cancels explicitly. At cofactor primes the exact
fixed inverse factor is included before taking the lower bound.
-/

namespace Erdos4b

noncomputable section

theorem cancel_two_inverse_powers (a b c : ℝ) (n : ℕ) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a * b⁻¹ ^ n) / (c * b⁻¹ ^ (n + 2)) = b ^ 2 * a / c := by
  rw [pow_add]
  field_simp

theorem pinnedLocalFactor_div_generic_eq
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hp : 2 * K < p.val) :
    pinnedLocalFactor h w m p₀ p / genericLargeGapLocalFactor K p =
      (1 - 1 / (p : ℝ)) ^ 2 *
        (1 - (pinnedLocalMultiplicity h w m p₀ p : ℝ) / p) / (1 - 2 * (K : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hb : 1 - 1 / (p : ℝ) ≠ 0 := (sub_pos.mpr ((div_lt_one hp0).mpr hp1)).ne'
  have hc : 1 - 2 * (K : ℝ) / p ≠ 0 :=
    (sub_pos.mpr ((div_lt_one hp0).mpr (by exact_mod_cast hp))).ne'
  have hdim : 2 * K = 2 * (K - 1) + 2 := by have := h.pos; omega
  unfold pinnedLocalFactor genericLargeGapLocalFactor
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [card_pinnedShiftIndex, hdim]
  exact cancel_two_inverse_powers _ _ _ _ hb hc

theorem one_le_pinnedLocalFactor_div_generic
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes)
    (hKw : K ≤ w) (hwp : w < p.val) (hp : 2 * K < p.val)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    1 ≤ pinnedLocalFactor h w m p₀ p / genericLargeGapLocalFactor K p := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast h.pos
  have hpR : 2 * (K : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hcount := pinnedLocalMultiplicity_le_two_card h p hKw hwp hpp₀ hnum
  rw [card_pinnedShiftIndex] at hcount
  have hcountR : (pinnedLocalMultiplicity h w m p₀ p : ℝ) ≤ 2 * (K : ℝ) - 2 := by
    have hc : (pinnedLocalMultiplicity h w m p₀ p : ℝ) ≤ (2 * (K - 1) : ℕ) := by
      exact_mod_cast hcount
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h.pos, Nat.cast_one] at hc
    linarith
  rw [pinnedLocalFactor_div_generic_eq h p hp]
  apply (one_le_pinned_noncofactor_ratio hK1 hpR).trans
  apply div_le_div_of_nonneg_right _
    (sub_pos.mpr ((div_lt_one hp0).mpr hpR)).le
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (div_le_div_of_nonneg_right hcountR hp0.le) 1) (sq_nonneg _)

theorem pinnedLocalMultiplicity_of_cofactor_prime
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w) (hwp : w < p.val)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hpm : p.val ∣ m) : pinnedLocalMultiplicity h w m p₀ p = K - 1 := by
  rw [pinnedLocalMultiplicity, pinnedLocalForbiddenResidues_eq_union h p hKw hwp hpp₀ hnum,
    pinnedCompanionLocalResidues, if_pos hpm, Finset.union_empty,
    card_pinnedFirstLocalResidues h p.property hKw hwp hpp₀, card_pinnedShiftIndex]

theorem pinnedLocalFactor_mul_fixed_div_generic_eq
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes)
    (hKw : K ≤ w) (hwp : w < p.val) (hp : 2 * K < p.val)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hpm : p.val ∣ m) :
    pinnedLocalFactor h w m p₀ p * (((p : ℝ) - 2 * K) / ((p : ℝ) - K)) /
        genericLargeGapLocalFactor K p =
      (1 - 1 / (p : ℝ)) ^ 2 * (1 - ((K : ℝ) - 1) / p) / (1 - (K : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp2 : 2 * (K : ℝ) < p := by exact_mod_cast hp
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hpk : 0 < (p : ℝ) - K := by linarith
  have hp2k : 0 < (p : ℝ) - 2 * K := by linarith
  have hp2kne : (p : ℝ) - (K : ℝ) * 2 ≠ 0 := by linarith
  calc
    _ = (pinnedLocalFactor h w m p₀ p / genericLargeGapLocalFactor K p) *
        (((p : ℝ) - 2 * K) / ((p : ℝ) - K)) := by ring
    _ = _ := by
      rw [pinnedLocalFactor_div_generic_eq h p hp,
        pinnedLocalMultiplicity_of_cofactor_prime h p hKw hwp hpp₀ hnum hpm,
        Nat.cast_sub h.pos, Nat.cast_one]
      field_simp [hp2kne]

theorem cofactor_residual_factor_le_pinnedLocal_combined_ratio
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes)
    (hKw : K ≤ w) (hwp : w < p.val) (hp : 2 * K < p.val)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0)
    (hpm : p.val ∣ m) :
    ((p : ℝ) - 2) / ((p : ℝ) - 1) ≤
      pinnedLocalFactor h w m p₀ p * (((p : ℝ) - 2 * K) / ((p : ℝ) - K)) /
        genericLargeGapLocalFactor K p := by
  rw [pinnedLocalFactor_mul_fixed_div_generic_eq h p hKw hwp hp hpp₀ hnum hpm]
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast h.pos
  have hpR : (K : ℝ) < p := by
    have hp2 : 2 * (K : ℝ) < p := by exact_mod_cast hp
    linarith
  exact (cofactor_residual_factor_le_one_sub_inv
    (by exact_mod_cast p.property.one_lt)).trans (one_sub_inv_le_pinned_cofactor_ratio hK1 hpR)

end

end Erdos4b

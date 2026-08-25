/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlopeAwareRosser

/-!
# Euler-product loss from slope primes

Away from primes dividing either slope, the affine local density is exactly
the pair-shift density at the determinant.  At a slope prime we bound the
local factor by one.  Thus the whole slope-aware Euler product is bounded by
the full pair product with its slope-prime factors deleted.
-/

namespace Erdos822

open scoped BigOperators

/-- Pair-shift local product with every prime dividing at least one slope
replaced by the harmless factor one. -/
noncomputable def pairProductWithoutSlopePrimes
    (h a b z y : ℕ) : ℝ :=
  ∏ p ∈ Erdos851.sievePrimes z y,
    if p ∣ a ∨ p ∣ b then 1
    else 1 - Erdos851.pairShiftDensity h p

/-- Multiplicative loss caused by deleting primes dividing one of the two
slopes from a pair-shift Euler product. -/
noncomputable def slopePrimeLoss (h a b z y : ℕ) : ℝ :=
  ∏ p ∈ Erdos851.sievePrimes z y,
    if p ∣ a ∨ p ∣ b then
      (1 - Erdos851.pairShiftDensity h p)⁻¹
    else 1

/-- Reciprocal mass of sieving primes which divide at least one slope. -/
noncomputable def slopeReciprocalMass (a b z y : ℕ) : ℝ :=
  ∑ p ∈ Erdos851.sievePrimes z y,
    if p ∣ a ∨ p ∣ b then (1 : ℝ) / p else 0

/-- At every prime above two, one inverse pair-shift local factor is bounded
by a fixed linear reciprocal correction. -/
theorem pairShift_inverseFactor_le_one_add_six_div
    {h p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (1 - Erdos851.pairShiftDensity h p)⁻¹ ≤
      1 + (6 : ℝ) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR2 : (2 : ℝ) < p := by exact_mod_cast hp2
  have hpR3 : (3 : ℝ) ≤ p := by
    exact_mod_cast (by omega : 3 ≤ p)
  unfold Erdos851.pairShiftDensity
  split_ifs
  · have hden : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
      exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
    rw [show (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / (p - 1) by
      field_simp [hden.ne', hpR.ne']]
    apply (div_le_iff₀ (by linarith)).2
    field_simp [hpR.ne']
    nlinarith
  · have hden : (0 : ℝ) < 1 - 2 * (p : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact sub_pos.mpr ((div_lt_one hpR).2 hpR2)
    rw [show (1 - 2 * (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / (p - 2) by
      field_simp [hden.ne', hpR.ne']]
    apply (div_le_iff₀ (by linarith)).2
    field_simp [hpR.ne']
    nlinarith

/-- The entire slope-prime loss is at most the exponential of six times its
reciprocal prime mass. -/
theorem slopePrimeLoss_le_exp_slopeReciprocalMass
    (h a b z y : ℕ) (hz : 2 ≤ z) :
    slopePrimeLoss h a b z y ≤
      Real.exp (6 * slopeReciprocalMass a b z y) := by
  unfold slopePrimeLoss slopeReciprocalMass
  calc
    (∏ p ∈ Erdos851.sievePrimes z y,
        if p ∣ a ∨ p ∣ b then
          (1 - Erdos851.pairShiftDensity h p)⁻¹
        else 1) ≤
        ∏ p ∈ Erdos851.sievePrimes z y,
          Real.exp (if p ∣ a ∨ p ∣ b then (6 : ℝ) / p else 0) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpData := Erdos851.mem_sievePrimes.mp hp
        have hp2 : 2 < p := by omega
        by_cases hslope : p ∣ a ∨ p ∣ b
        · rw [if_pos hslope]
          exact (inv_nonneg.mpr
            (Erdos851.pairShift_localFactor_pos
              hpData.2.2 hp2).le)
        · rw [if_neg hslope]
          norm_num
      · intro p hp
        have hpData := Erdos851.mem_sievePrimes.mp hp
        have hp2 : 2 < p := by omega
        by_cases hslope : p ∣ a ∨ p ∣ b
        · simp only [if_pos hslope]
          calc
            (1 - Erdos851.pairShiftDensity h p)⁻¹ ≤
                1 + (6 : ℝ) / p :=
              pairShift_inverseFactor_le_one_add_six_div hpData.2.2 hp2
            _ ≤ Real.exp ((6 : ℝ) / p) := by
              simpa [add_comm] using Real.add_one_le_exp ((6 : ℝ) / p)
        · simp [hslope]
    _ = Real.exp (∑ p ∈ Erdos851.sievePrimes z y,
        if p ∣ a ∨ p ∣ b then (6 : ℝ) / p else 0) := by
      symm
      apply Real.exp_sum
    _ = Real.exp (6 * ∑ p ∈ Erdos851.sievePrimes z y,
        if p ∣ a ∨ p ∣ b then (1 : ℝ) / p else 0) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hslope : p ∣ a ∨ p ∣ b <;>
        simp [hslope, div_eq_mul_inv]

/-- The union slope mass is bounded by the sum of the separate slope
masses. -/
theorem slopeReciprocalMass_le_add
    (a b z y : ℕ) :
    slopeReciprocalMass a b z y ≤
      (∑ p ∈ Erdos851.sievePrimes z y,
          if p ∣ a then (1 : ℝ) / p else 0) +
        ∑ p ∈ Erdos851.sievePrimes z y,
          if p ∣ b then (1 : ℝ) / p else 0 := by
  unfold slopeReciprocalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b <;>
    simp [hpa, hpb] <;> positivity

/-- Deleting slope-prime factors is exactly multiplication by the explicit
inverse-factor loss. -/
theorem pairProductWithoutSlopePrimes_eq_localEulerProduct_mul_loss
    (h a b z y : ℕ) (hz : 2 ≤ z) :
    pairProductWithoutSlopePrimes h a b z y =
      Erdos851.localEulerProduct (Erdos851.pairShiftDensity h) z y *
        slopePrimeLoss h a b z y := by
  unfold pairProductWithoutSlopePrimes Erdos851.localEulerProduct slopePrimeLoss
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpMem
  have hpData := Erdos851.mem_sievePrimes.mp hpMem
  have hfactorPos : 0 < 1 - Erdos851.pairShiftDensity h p :=
    Erdos851.pairShift_localFactor_pos hpData.2.2
      (by omega)
  by_cases hslope : p ∣ a ∨ p ∣ b
  · simpa [hslope] using (mul_inv_cancel₀ hfactorPos.ne').symm
  · simp [hslope]

/-- Local Euler product comparison for the slope-aware affine sieve. -/
theorem slopeAware_localEulerProduct_le_pairProductWithoutSlopePrimes
    {a s b t z y : ℕ} (hz : 2 ≤ z)
    (hconstants : ∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
      ¬ p ∣ s ∧ ¬ p ∣ t) :
    (∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
        (1 - twoAffineNu a s b t p)) ≤
      pairProductWithoutSlopePrimes (affineDetNat a s b t) a b z y := by
  have hterm :
      ∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
        0 ≤ 1 - twoAffineNu a s b t p ∧
        1 - twoAffineNu a s b t p ≤
          (if p ∣ a ∨ p ∣ b then 1
            else 1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p) := by
    intro p hpMem
    have hpData := mem_slopeAwareSievePrimes_iff.mp hpMem
    have hp := hpData.1
    have hp2 : 2 < p := hz.trans_lt hpData.2.1
    have hloc := twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
      hp hp2 (hconstants p hpMem).1 (hconstants p hpMem).2
      hpData.2.2.2
    constructor
    · exact sub_nonneg.mpr hloc.2.le
    · by_cases hslope : p ∣ a ∨ p ∣ b
      · rw [if_pos hslope]
        exact sub_le_self _ hloc.1.le
      · have hpa : ¬ p ∣ a := by
          intro h
          exact hslope (Or.inl h)
        have hpb : ¬ p ∣ b := by
          intro h
          exact hslope (Or.inr h)
        rw [if_neg hslope,
          twoAffineNu_eq_pairShiftDensity_of_not_dvd hp hpa hpb]
  calc
    (∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
        (1 - twoAffineNu a s b t p)) ≤
        ∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
          (if p ∣ a ∨ p ∣ b then 1
            else 1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact (hterm p hp).1
      · intro p hp
        exact (hterm p hp).2
    _ = pairProductWithoutSlopePrimes (affineDetNat a s b t) a b z y := by
      unfold pairProductWithoutSlopePrimes slopeAwareSievePrimes
      rw [erdos387_sievePrimes_eq_erdos851_sievePrimes
        (by omega : 0 < y + 1)]
      simp only [Nat.add_sub_cancel]
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b <;>
        simp [hpa, hpb]

/-- Final finite Euler-product form: the affine local product is bounded by
the full pair-shift product times the explicit slope-prime loss. -/
theorem slopeAware_localEulerProduct_le_pair_mul_slopeLoss
    {a s b t z y : ℕ} (hz : 2 ≤ z)
    (hconstants : ∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
      ¬ p ∣ s ∧ ¬ p ∣ t) :
    (∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
        (1 - twoAffineNu a s b t p)) ≤
      Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y *
        slopePrimeLoss (affineDetNat a s b t) a b z y := by
  rw [← pairProductWithoutSlopePrimes_eq_localEulerProduct_mul_loss
    (affineDetNat a s b t) a b z y hz]
  exact slopeAware_localEulerProduct_le_pairProductWithoutSlopePrimes
    hz hconstants

end Erdos822

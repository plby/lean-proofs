/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Asymptotic

/-!
# Erdős Problem 446: finite counts and passage to density

The analytic proof is naturally expressed using finite prefix counts.  This
file identifies their normalized limits with `epsilon` and `epsilonR`, and
packages the exact uniform hypotheses needed to pass Ford's finite estimates
to the two density conclusions.
-/

namespace Erdos446

open Filter Finset Set
open scoped Topology

/-- Number of `m < X` having a divisor in `(y, z]`.  The residue `m = 0`
is included, exactly as in `Set.partialDensity`; deleting it changes a finite
count by at most one and is immaterial to all asymptotic estimates. -/
def divisorPrefixCount (X y z : ℕ) : ℕ :=
  ((Finset.range X).filter fun m ↦ 0 < divisorCountIoc y z m).card

/-- Number of `m < X` having exactly `r` divisors in `(y, z]`. -/
def exactDivisorPrefixCount (r X y z : ℕ) : ℕ :=
  ((Finset.range X).filter fun m ↦ divisorCountIoc y z m = r).card

theorem partialDensity_divisorSetIoc_eq (X y z : ℕ) :
    (divisorSetIoc y z).partialDensity Set.univ X =
      (divisorPrefixCount X y z : ℝ) / (X : ℝ) := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
    Set.ncard_Iio_nat]
  have hset : divisorSetIoc y z ∩ Set.Iio X =
      ↑((Finset.range X).filter fun m ↦ 0 < divisorCountIoc y z m) := by
    ext m
    simp [divisorSetIoc, and_comm]
  rw [hset, Set.ncard_coe_finset]
  rfl

theorem partialDensity_exactDivisorSetIoc_eq (r X y z : ℕ) :
    (exactDivisorSetIoc r y z).partialDensity Set.univ X =
      (exactDivisorPrefixCount r X y z : ℝ) / (X : ℝ) := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
    Set.ncard_Iio_nat]
  have hset : exactDivisorSetIoc r y z ∩ Set.Iio X =
      ↑((Finset.range X).filter fun m ↦ divisorCountIoc y z m = r) := by
    ext m
    simp [exactDivisorSetIoc, and_comm]
  rw [hset, Set.ncard_coe_finset]
  rfl

theorem tendsto_divisorPrefixCount_div (y z : ℕ) (hy : 0 < y) :
    Tendsto (fun X : ℕ ↦ (divisorPrefixCount X y z : ℝ) / (X : ℝ))
      atTop (nhds (epsilon y z)) := by
  exact (divisorSetIoc_hasDensity y z hy).congr'
    (Eventually.of_forall fun X ↦ partialDensity_divisorSetIoc_eq X y z)

theorem tendsto_exactDivisorPrefixCount_div (r y z : ℕ) (hy : 0 < y) :
    Tendsto
      (fun X : ℕ ↦ (exactDivisorPrefixCount r X y z : ℝ) / (X : ℝ))
      atTop (nhds (epsilonR r y z)) := by
  exact (exactDivisorSetIoc_hasDensity r y z hy).congr'
    (Eventually.of_forall fun X ↦
      partialDensity_exactDivisorSetIoc_eq r X y z)

theorem epsilon_nonneg (y z : ℕ) : 0 ≤ epsilon y z := by
  unfold epsilon
  positivity

theorem epsilonR_nonneg (r y z : ℕ) : 0 ≤ epsilonR r y z := by
  unfold epsilonR
  positivity

/-! ## Uniform interfaces for Ford's two analytic estimates -/

/-- Uniform dyadic finite-count bounds with absolute constants. -/
def DyadicPrefixBounds (c C : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → ∀ X : ℕ, y * y ≤ X →
    c * (X : ℝ) * growth446 y ≤ (divisorPrefixCount X y (2 * y) : ℝ) ∧
      (divisorPrefixCount X y (2 * y) : ℝ) ≤
        C * (X : ℝ) * growth446 y

/-- Uniform finite-count lower comparison for one fixed multiplicity. -/
def FixedMultiplicityPrefixLower (r : ℕ) (c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → ∀ X : ℕ, y * y ≤ X →
    c * (divisorPrefixCount X y (2 * y) : ℝ) ≤
      (exactDivisorPrefixCount r X y (2 * y) : ℝ)

theorem epsilon_bounds_of_dyadicPrefixBounds
    {c C : ℝ} {Y : ℕ} (hY : 1 ≤ Y)
    (h : DyadicPrefixBounds c C Y) :
    ∀ y : ℕ, Y ≤ y →
      c * growth446 y ≤ epsilon y (2 * y) ∧
        epsilon y (2 * y) ≤ C * growth446 y := by
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le Nat.zero_lt_one (hY.trans hy)
  have htend := tendsto_divisorPrefixCount_div y (2 * y) hypos
  constructor
  · apply ge_of_tendsto htend
    filter_upwards [eventually_ge_atTop (y * y), eventually_gt_atTop 0]
      with X hX hXpos
    have hcount := (h y hy X hX).1
    have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
    apply (le_div_iff₀ hXR).2
    nlinarith
  · apply le_of_tendsto htend
    filter_upwards [eventually_ge_atTop (y * y), eventually_gt_atTop 0]
      with X hX hXpos
    have hcount := (h y hy X hX).2
    have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
    apply (div_le_iff₀ hXR).2
    nlinarith

theorem epsilon_isTheta_growth446_of_dyadicPrefixBounds
    {c C : ℝ} {Y : ℕ} (hY : 1 ≤ Y) (hc : 0 < c) (hC : 0 < C)
    (h : DyadicPrefixBounds c C Y) :
    (fun y ↦ epsilon y (2 * y)) =Θ[atTop] growth446 := by
  have hb := epsilon_bounds_of_dyadicPrefixBounds hY h
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop Y, eventually_growthDenominator446_pos]
      with y hy hden
    have heps := epsilon_nonneg y (2 * y)
    have hgrowth : 0 < growth446 y := inv_pos.mpr hden
    simpa only [Real.norm_eq_abs, abs_of_nonneg heps, abs_of_pos hgrowth] using
      (hb y hy).2
  · apply Asymptotics.IsBigO.of_bound c⁻¹
    filter_upwards [eventually_ge_atTop Y, eventually_growthDenominator446_pos]
      with y hy hden
    have heps := epsilon_nonneg y (2 * y)
    have hgrowth : 0 < growth446 y := inv_pos.mpr hden
    rw [Real.norm_eq_abs, abs_of_pos hgrowth, Real.norm_eq_abs,
      abs_of_nonneg heps]
    have hlower := (hb y hy).1
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hlower)

theorem epsilonR_lower_of_fixedMultiplicityPrefixLower
    {r : ℕ} {c : ℝ} {Y : ℕ} (hY : 1 ≤ Y)
    (h : FixedMultiplicityPrefixLower r c Y) :
    ∀ y : ℕ, Y ≤ y →
      c * epsilon y (2 * y) ≤ epsilonR r y (2 * y) := by
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le Nat.zero_lt_one (hY.trans hy)
  have htend : Tendsto
      (fun X : ℕ ↦
        c * ((divisorPrefixCount X y (2 * y) : ℝ) / (X : ℝ)) -
          ((exactDivisorPrefixCount r X y (2 * y) : ℝ) / (X : ℝ)))
      atTop (nhds (c * epsilon y (2 * y) - epsilonR r y (2 * y))) :=
    (tendsto_const_nhds.mul (tendsto_divisorPrefixCount_div y (2 * y) hypos)).sub
      (tendsto_exactDivisorPrefixCount_div r y (2 * y) hypos)
  have hle : c * epsilon y (2 * y) - epsilonR r y (2 * y) ≤ 0 := by
    apply le_of_tendsto htend
    filter_upwards [eventually_ge_atTop (y * y), eventually_gt_atTop 0]
      with X hX hXpos
    have hcount := h y hy X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
    apply sub_nonpos.mpr
    rw [show c * ((divisorPrefixCount X y (2 * y) : ℝ) / (X : ℝ)) =
      (c * (divisorPrefixCount X y (2 * y) : ℝ)) / (X : ℝ) by ring]
    apply (div_le_div_iff_of_pos_right hXR).2
    exact hcount
  linarith

end Erdos446

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.SlopeLossControl

/-!
# Exponential control of the determinant singular factor

The pair-shift Euler product separates into the square of the ordinary
Mertens product and a finite singular factor.  This file records the
elementary estimate which charges that singular factor to reciprocal prime
mass of the reduced totient determinant.
-/

namespace Erdos822

open scoped BigOperators

/-- Reciprocal mass, in a finite sieve interval, of primes dividing an
integer. -/
noncomputable def divisorReciprocalMass (h z y : ℕ) : ℝ :=
  ∑ p ∈ Erdos851.sievePrimes z y,
    if p ∣ h then (1 : ℝ) / p else 0

/-- A singular local factor at a prime above two is bounded by a fixed
linear reciprocal correction. -/
theorem singularLocal_le_one_add_two_div
    {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ 1 + (2 : ℝ) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR2 : (2 : ℝ) < p := by exact_mod_cast hp2
  apply (div_le_iff₀ (by linarith)).2
  field_simp [hpR.ne']
  nlinarith

/-- One local singular factor is at most the exponential of twice its
reciprocal-prime charge. -/
theorem singularLocal_le_exp_two_div
    {h p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (if p ∣ h then (p : ℝ) / ((p : ℝ) - 1) else 1) ≤
      Real.exp (if p ∣ h then (2 : ℝ) / p else 0) := by
  by_cases hph : p ∣ h
  · simp only [if_pos hph]
    calc
      (p : ℝ) / ((p : ℝ) - 1) ≤ 1 + (2 : ℝ) / p :=
        singularLocal_le_one_add_two_div hp hp2
      _ ≤ Real.exp ((2 : ℝ) / p) := by
        simpa [add_comm] using Real.add_one_le_exp ((2 : ℝ) / p)
  · simp [hph]

/-- The whole truncated determinant singular factor is bounded by the
exponential of twice the reciprocal mass of its prime divisors. -/
theorem singularFactor_le_exp_divisorReciprocalMass
    (h z y : ℕ) (hz : 2 ≤ z) :
    Erdos851.singularFactor h z y ≤
      Real.exp (2 * divisorReciprocalMass h z y) := by
  unfold Erdos851.singularFactor divisorReciprocalMass
  calc
    (∏ p ∈ Erdos851.sievePrimes z y,
        if p ∣ h then (p : ℝ) / ((p : ℝ) - 1) else 1) ≤
        ∏ p ∈ Erdos851.sievePrimes z y,
          Real.exp (if p ∣ h then (2 : ℝ) / p else 0) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpData := Erdos851.mem_sievePrimes.mp hp
        by_cases hph : p ∣ h
        · simp only [if_pos hph]
          exact div_nonneg (by positivity) (by
            have : (1 : ℝ) < p := by exact_mod_cast hpData.2.2.one_lt
            linarith)
        · simp [hph]
      · intro p hp
        have hpData := Erdos851.mem_sievePrimes.mp hp
        exact singularLocal_le_exp_two_div hpData.2.2 (by omega)
    _ = Real.exp (∑ p ∈ Erdos851.sievePrimes z y,
        if p ∣ h then (2 : ℝ) / p else 0) := by
      symm
      apply Real.exp_sum
    _ = Real.exp (2 * ∑ p ∈ Erdos851.sievePrimes z y,
        if p ∣ h then (1 : ℝ) / p else 0) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hph : p ∣ h <;>
        simp [hph, div_eq_mul_inv]

/-- The pair-shift product is bounded by the square one-shift product times
the explicit exponential determinant mass. -/
theorem pairShift_localEulerProduct_le_oneShift_sq_mul_exp_mass
    (h z y : ℕ) (hz : 2 ≤ z) :
    Erdos851.localEulerProduct (Erdos851.pairShiftDensity h) z y ≤
      Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
        Real.exp (2 * divisorReciprocalMass h z y) := by
  calc
    Erdos851.localEulerProduct (Erdos851.pairShiftDensity h) z y ≤
        Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
          Erdos851.singularFactor h z y :=
      Erdos851.pairShift_localEulerProduct_le h hz
    _ ≤ Erdos851.localEulerProduct Erdos851.oneShiftDensity z y ^ 2 *
          Real.exp (2 * divisorReciprocalMass h z y) := by
      exact mul_le_mul_of_nonneg_left
        (singularFactor_le_exp_divisorReciprocalMass h z y hz)
        (sq_nonneg _)

end Erdos822

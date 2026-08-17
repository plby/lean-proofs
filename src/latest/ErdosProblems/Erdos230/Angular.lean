/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos230.Surface
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Angular form of the polynomials in Erdős Problem 230

The analytic construction is most naturally written on the real line, with
`theta` parametrizing the unit circle by `exp (theta * I)`.  This file gives
the exact bridge to the polynomial statement and records the harmless removal
of a constant coefficient at the end of the construction.
-/

open scoped BigOperators

namespace Erdos230

noncomputable section

/-- The standard real parametrization of the complex unit circle. -/
def unitPoint (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)

@[simp]
theorem norm_unitPoint (theta : ℝ) : ‖unitPoint theta‖ = 1 := by
  simp [unitPoint, Complex.norm_exp]

/-- The period-one parametrization used by number-theoretic Fourier sums. -/
def periodicPoint (theta : ℝ) : ℂ :=
  unitPoint (2 * Real.pi * theta)

@[simp]
theorem norm_periodicPoint (theta : ℝ) : ‖periodicPoint theta‖ = 1 := by
  simp [periodicPoint]

theorem periodic_periodicPoint : Function.Periodic periodicPoint 1 := by
  intro x
  rw [periodicPoint, periodicPoint, unitPoint, unitPoint]
  have harg : (((2 * Real.pi * (x + 1) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Reducing a real phase modulo one does not change its circle point. -/
theorem periodicPoint_fract (x : ℝ) :
    periodicPoint (Int.fract x) = periodicPoint x := by
  have h := (periodic_periodicPoint.int_mul ⌊x⌋) (Int.fract x)
  rw [mul_one, Int.fract_add_floor] at h
  exact h.symm

/-- The value of a Problem 230 polynomial at `exp (theta * I)`. -/
def angularValue {n : ℕ} (a : Fin n → ℂ) (theta : ℝ) : ℂ :=
  ∑ i : Fin n, a i * unitPoint theta ^ (i.1 + 1)

@[simp]
theorem eval_phasePoly_unitPoint {n : ℕ} (a : Fin n → ℂ) (theta : ℝ) :
    (phasePoly a).eval (unitPoint theta) = angularValue a theta := by
  simp [angularValue, eval_phasePoly, phaseValue]

/-- Angularly stated, arbitrarily large one-sided ultraflat examples. -/
def HasAngularUltraflatUpper : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ N : ℕ,
    ∃ n : ℕ, max 2 N ≤ n ∧
      ∃ a : Fin n → ℂ, IsUnimodular a ∧
        ∀ theta : ℝ, ‖angularValue a theta‖ ≤
          (1 + epsilon) * Real.sqrt n

/-- A uniform angular estimate is the same estimate at every point of the
unit circle. -/
theorem hasUltraflatUpper_of_angular (h : HasAngularUltraflatUpper) :
    HasUltraflatUpper := by
  intro epsilon hepsilon N
  obtain ⟨n, hn, a, ha, hbound⟩ := h epsilon hepsilon N
  refine ⟨n, hn, a, ha, ?_⟩
  intro z hz
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff z).mp hz
  subst z
  simpa [eval_phasePoly, phaseValue, angularValue, unitPoint] using hbound theta

/-- An analytic polynomial with exponents `0, ..., n`. -/
def zerothValue {n : ℕ} (a : Fin (n + 1) → ℂ) (theta : ℝ) : ℂ :=
  ∑ i : Fin (n + 1), a i * unitPoint theta ^ i.1

/-- The exponent-zero value written with a period-one real parameter. -/
def normalizedZerothValue {n : ℕ} (a : Fin (n + 1) → ℂ) (theta : ℝ) : ℂ :=
  ∑ i : Fin (n + 1), a i * periodicPoint theta ^ i.1

theorem normalizedZerothValue_div_two_pi {n : ℕ}
    (a : Fin (n + 1) → ℂ) (theta : ℝ) :
    normalizedZerothValue a (theta / (2 * Real.pi)) = zerothValue a theta := by
  have hpoint : periodicPoint (theta / (2 * Real.pi)) = unitPoint theta := by
    apply congrArg unitPoint
    field_simp [Real.pi_ne_zero]
  simp [normalizedZerothValue, zerothValue, hpoint]

/-- Remove the constant coefficient and reindex the remaining coefficients. -/
def tailCoeffs {n : ℕ} (a : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun i => a i.succ

theorem zerothValue_eq_const_add_angularValue {n : ℕ}
    (a : Fin (n + 1) → ℂ) (theta : ℝ) :
    zerothValue a theta = a 0 + angularValue (tailCoeffs a) theta := by
  classical
  rw [zerothValue, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one]
  congr 1

/-- Deleting a constant coefficient of norm at most one costs at most one in
the uniform norm. -/
theorem norm_angularValue_tail_le {n : ℕ}
    (a : Fin (n + 1) → ℂ) (ha0 : ‖a 0‖ ≤ 1) (theta : ℝ) :
    ‖angularValue (tailCoeffs a) theta‖ ≤ ‖zerothValue a theta‖ + 1 := by
  rw [zerothValue_eq_const_add_angularValue] at *
  have h := norm_sub_le (a 0 + angularValue (tailCoeffs a) theta) (a 0)
  simpa [add_sub_cancel_left] using h.trans (add_le_add_right ha0 _)

end

end Erdos230

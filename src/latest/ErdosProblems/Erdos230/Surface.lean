/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Surface statement for Erdős Problem 230

For coefficients `a 0, ..., a (n - 1)` of complex norm one, `phasePoly a`
is the polynomial

`a 0 * X + a 1 * X^2 + ... + a (n - 1) * X^n`.

`ErdosNewmanClaim` is the proposed uniform improvement over the Parseval
lower bound.  Its `circleMaximum` is the supremum of the polynomial norm on
the unit circle; the extreme-value theorem below proves that this supremum is
an attained maximum.

The established negative resolution follows from the existence, at
arbitrarily large degrees, of unimodular polynomials whose norm is at most
`(1 + epsilon) * sqrt n` everywhere on the unit circle.  This file contains
only the finite polynomial interface and the elementary logical implication;
the analytic ultraflat construction is supplied separately.
-/

open scoped BigOperators

namespace Erdos230

noncomputable section

/-! ## Unimodular coefficient polynomials -/

/-- A finite coefficient vector is unimodular when every coefficient has
complex norm one. -/
def IsUnimodular {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i, ‖a i‖ = 1

/-- The polynomial `sum_(i < n) a_i X^(i+1)`.  Thus the coefficient vector
is zero-indexed while the exponents agree with the one-indexed mathematical
statement of Erdős Problem 230. -/
def phasePoly {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial (i.1 + 1) (a i)

/-- The corresponding finite trigonometric sum evaluated at `z`. -/
def phaseValue {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin n, a i * z ^ (i.1 + 1)

@[simp]
theorem eval_phasePoly {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (phasePoly a).eval z = phaseValue a z := by
  classical
  simp [phasePoly, phaseValue, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

/-! ## The attained circle maximum -/

/-- The set of norms taken by a coefficient polynomial on the unit circle. -/
def circleValues {n : ℕ} (a : Fin n → ℂ) : Set ℝ :=
  {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖(phasePoly a).eval z‖}

/-- The circle maximum, initially defined as a supremum.  The next theorem
proves that it is attained. -/
noncomputable def circleMaximum {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  sSup (circleValues a)

theorem circleValues_nonempty {n : ℕ} (a : Fin n → ℂ) :
    (circleValues a).Nonempty := by
  refine ⟨‖(phasePoly a).eval 1‖, ?_⟩
  exact ⟨1, norm_one, rfl⟩

/-- A pointwise circle upper bound also bounds the circle maximum. -/
theorem circleMaximum_le {n : ℕ} (a : Fin n → ℂ) (U : ℝ)
    (hU : ∀ z : ℂ, ‖z‖ = 1 → ‖(phasePoly a).eval z‖ ≤ U) :
    circleMaximum a ≤ U := by
  apply csSup_le (circleValues_nonempty a)
  rintro x ⟨z, hz, rfl⟩
  exact hU z hz

/-- The supremum in `circleMaximum` is an actual maximum, by compactness of
the unit circle and continuity of polynomial evaluation. -/
theorem exists_circleMaximum {n : ℕ} (a : Fin n → ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖(phasePoly a).eval z‖ = circleMaximum a := by
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    hne (phasePoly a).continuous.norm.continuousOn
  have hzunit : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hupper : ∀ x ∈ circleValues a, x ≤ ‖(phasePoly a).eval z‖ := by
    rintro x ⟨w, hw, rfl⟩
    exact hmax (mem_sphere_zero_iff_norm.mpr hw)
  have hbdd : BddAbove (circleValues a) :=
    ⟨‖(phasePoly a).eval z‖, hupper⟩
  have hle : ‖(phasePoly a).eval z‖ ≤ circleMaximum a := by
    apply le_csSup hbdd
    exact ⟨z, hzunit, rfl⟩
  have hge : circleMaximum a ≤ ‖(phasePoly a).eval z‖ := by
    exact csSup_le (circleValues_nonempty a) hupper
  exact ⟨z, hzunit, le_antisymm hle hge⟩

/-! ## Exact proposed lower bound and ultraflat upper examples -/

/-- The Erdős--Newman claim in its literal circle-maximum form. -/
def ErdosNewmanClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ a : Fin n → ℂ, IsUnimodular a →
        (1 + c) * Real.sqrt n ≤ circleMaximum a

/-- Arbitrarily large unimodular polynomials with a uniform upper bound
arbitrarily close to the Parseval scale `sqrt n`.

This is the precise one-sided consequence of an ultraflat family needed to
disprove `ErdosNewmanClaim`.  The lower cutoff `N` records that the examples
occur at arbitrarily large degrees, rather than at a single exceptional
degree. -/
def HasUltraflatUpper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ, max 2 N ≤ n ∧
      ∃ a : Fin n → ℂ, IsUnimodular a ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          ‖(phasePoly a).eval z‖ ≤ (1 + ε) * Real.sqrt n

/-- Ultraflat upper examples rule out every fixed positive multiplicative
improvement over `sqrt n`. -/
theorem not_erdos230Claim_of_ultraflat_upper
    (hultra : HasUltraflatUpper) : ¬ ErdosNewmanClaim := by
  rintro ⟨c, hc, hclaim⟩
  obtain ⟨n, hn, a, ha, hupper⟩ := hultra (c / 2) (by linarith) 2
  have hn2 : 2 ≤ n := by
    exact (le_max_left 2 2).trans hn
  have hsqrt : 0 < Real.sqrt n := by
    apply Real.sqrt_pos.2
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn2)
  have hfactor : (1 + c / 2) * Real.sqrt n <
      (1 + c) * Real.sqrt n := by
    apply mul_lt_mul_of_pos_right _ hsqrt
    linarith
  have hmax : circleMaximum a ≤ (1 + c / 2) * Real.sqrt n :=
    circleMaximum_le a _ hupper
  exact (not_lt_of_ge ((hclaim n hn2 a ha).trans hmax)) hfactor

end

end Erdos230

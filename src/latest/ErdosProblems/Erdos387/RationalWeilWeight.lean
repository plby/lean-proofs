/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.InversePhasePartialFraction
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Multiplicative polynomial weights for a simple-pole rational phase

Let F be a monic polynomial whose roots are alpha.  At a pole parameter r,

  F'(r) / F(r) = sum_alpha 1 / (r - alpha).

Consequently the sum of the simple-pole phase over the roots of F is

  - sum_r coeff(r) F'(r) / F(r).

This file packages that logarithmic-derivative expression.  Its character
weight is zero when F contains a pole and is otherwise multiplicative in F.
This is the local Euler weight needed by an Artin L-function proof of the
rational Weil bound.
-/

namespace Erdos387

open Polynomial

namespace RationalWeil

/-- A polynomial avoids the poles when it does not vanish at any supported
pole. -/
def AvoidsPoleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) : Prop :=
  ∀ r ∈ InverseRational.poleSupport coeff, eval r F ≠ 0

/-- The logarithmic-derivative expression equal to the sum of the rational
phase over all roots, when the polynomial splits and avoids the poles. -/
noncomputable def logarithmicDerivativePhase
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) : ZMod p :=
  -∑ r ∈ InverseRational.poleSupport coeff,
    coeff r * eval r F.derivative * (eval r F)⁻¹

/-- The polynomial Euler weight: pole-containing polynomials receive zero,
and all other polynomials receive the additive character of the root phase. -/
noncomputable def polynomialWeight
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (F : (ZMod p)[X]) : ℂ := by
  classical
  exact if AvoidsPoleSupport coeff F then
    ZMod.stdAddChar (logarithmicDerivativePhase coeff F)
  else 0

theorem avoidsPoleSupport_mul_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F G : (ZMod p)[X]) :
    AvoidsPoleSupport coeff (F * G) ↔
      AvoidsPoleSupport coeff F ∧ AvoidsPoleSupport coeff G := by
  simp only [AvoidsPoleSupport, eval_mul, mul_ne_zero_iff, forall_and]

/-- The logarithmic derivative is additive on products that avoid every
pole. -/
theorem logarithmicDerivativePhase_mul
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {F G : (ZMod p)[X]}
    (hF : AvoidsPoleSupport coeff F)
    (hG : AvoidsPoleSupport coeff G) :
    logarithmicDerivativePhase coeff (F * G) =
      logarithmicDerivativePhase coeff F +
        logarithmicDerivativePhase coeff G := by
  classical
  simp only [logarithmicDerivativePhase, derivative_mul, eval_add, eval_mul]
  rw [← neg_add, ← Finset.sum_add_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro r hr
  have hFr := hF r hr
  have hGr := hG r hr
  field_simp [hFr, hGr]

/-- The zero-extended character weight is completely multiplicative. -/
theorem polynomialWeight_mul
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (F G : (ZMod p)[X]) :
    polynomialWeight coeff (F * G) =
      polynomialWeight coeff F * polynomialWeight coeff G := by
  classical
  by_cases hF : AvoidsPoleSupport coeff F
  · by_cases hG : AvoidsPoleSupport coeff G
    · rw [polynomialWeight, polynomialWeight, polynomialWeight,
        if_pos hF, if_pos hG,
        if_pos ((avoidsPoleSupport_mul_iff coeff F G).2 ⟨hF, hG⟩),
        logarithmicDerivativePhase_mul coeff hF hG,
        AddChar.map_add_eq_mul]
    · have hFG : ¬AvoidsPoleSupport coeff (F * G) := by
        exact fun h => hG ((avoidsPoleSupport_mul_iff coeff F G).1 h).2
      simp only [polynomialWeight, hF, hG, hFG, if_true, if_false, mul_zero]
  · have hFG : ¬AvoidsPoleSupport coeff (F * G) := by
      exact fun h => hF ((avoidsPoleSupport_mul_iff coeff F G).1 h).1
    simp only [polynomialWeight, hF, hFG, if_false, zero_mul]

/-- A linear polynomial avoids the pole set exactly when its root is not a
pole. -/
theorem avoidsPoleSupport_X_sub_C_iff
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    AvoidsPoleSupport coeff (X - C x) ↔
      x ∉ InverseRational.poleSupport coeff := by
  constructor
  · intro h hx
    exact h x hx (by simp)
  · intro hx r hr
    simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
    intro hrx
    apply hx
    subst r
    exact hr

/-- On a linear polynomial the logarithmic-derivative expression is exactly
the original simple-pole phase at its root. -/
theorem logarithmicDerivativePhase_X_sub_C
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) (x : ZMod p) :
    logarithmicDerivativePhase coeff (X - C x) =
      InverseRational.simplePolePhase coeff x := by
  classical
  rw [logarithmicDerivativePhase,
    InverseRational.simplePolePhase_eq_sum_poleSupport]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero,
    eval_one, mul_one, eval_sub, eval_X, eval_C]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show r - x = -(x - r) by ring, inv_neg]
  ring

/-- The Euler weight of a non-pole linear factor is the additive character
of the rational phase at its root. -/
theorem polynomialWeight_X_sub_C_of_not_mem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {x : ZMod p}
    (hx : x ∉ InverseRational.poleSupport coeff) :
    polynomialWeight coeff (X - C x) =
      ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
  rw [polynomialWeight, if_pos
    ((avoidsPoleSupport_X_sub_C_iff coeff x).2 hx),
    logarithmicDerivativePhase_X_sub_C]

/-- A linear factor rooted at a pole has zero Euler weight. -/
theorem polynomialWeight_X_sub_C_of_mem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {x : ZMod p}
    (hx : x ∈ InverseRational.poleSupport coeff) :
    polynomialWeight coeff (X - C x) = 0 := by
  rw [polynomialWeight, if_neg]
  exact fun h => ((avoidsPoleSupport_X_sub_C_iff coeff x).1 h) hx

end RationalWeil

end Erdos387

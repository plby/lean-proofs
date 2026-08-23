/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.HermiteInterpolation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The integral extrapolation step in the rational-prime Baker argument

This file packages the analytic implication at the end of Lemma 4 of van der
Poorten--Loxton.  The arithmetic construction supplies a Liouville
alternative for an auxiliary algebraic function `g`; the interpolation
argument supplies a strict upper bound for the nearby entire function `f`.
The two bounds force the value of `g` to vanish.

The theorem is deliberately independent of the eventual (large) parameter
structure.  Its hypotheses are exactly the quantities estimated in the
source proof: a boundary quotient, the interpolation-polynomial value, and a
strict numerical budget.  The Newton--Hermite identity and its Cauchy
remainder estimate are proved in `HermiteInterpolation`, rather than assumed
here.
-/

open scoped BigOperators

open Complex Metric Polynomial Set

noncomputable section

namespace Erdos240.BakerIntegralExtrapolation

open Erdos240.HermiteInterpolation

/-- A boundary estimate for `f` and its Hermite polynomial, together with a
positive lower bound for the nodal product, gives the quotient estimate used
by the Cauchy remainder formula. -/
theorem boundary_div_nodeProductNorm_le
    {f : ℂ → ℂ} {nodes : List ℂ} {c : ℂ} {R F H D : ℝ}
    (hD : 0 < D)
    (hf : ∀ w ∈ sphere c R, ‖f w‖ ≤ F)
    (hpoly : ∀ w ∈ sphere c R,
      ‖(polynomial f nodes).eval w‖ ≤ H)
    (hprod : ∀ w ∈ sphere c R, D ≤ nodeProductNorm nodes w) :
    ∀ w ∈ sphere c R,
      ‖f w - (polynomial f nodes).eval w‖ /
          nodeProductNorm nodes w ≤ (F + H) / D := by
  intro w hw
  have hnum :
      ‖f w - (polynomial f nodes).eval w‖ ≤ F + H := by
    calc
      ‖f w - (polynomial f nodes).eval w‖ ≤
          ‖f w‖ + ‖(polynomial f nodes).eval w‖ := norm_sub_le _ _
      _ ≤ F + H := add_le_add (hf w hw) (hpoly w hw)
  have hden : 0 < nodeProductNorm nodes w :=
    hD.trans_le (hprod w hw)
  exact (div_le_div_of_nonneg_right hnum hden.le).trans
    (div_le_div_of_nonneg_left
      ((norm_nonneg (f w - (polynomial f nodes).eval w)).trans hnum)
      hD (hprod w hw))

/-- Quantitative one-step integral extrapolation.

The conclusion is the logical endpoint of source Lemma 4.  The Cauchy--Hermite
remainder theorem bounds `f z - P z`; `hpolyTarget` bounds the interpolating
polynomial itself; and `hbudget` makes their sum strictly smaller than the
Liouville lower bound.  Therefore the nonzero branch of `hliouville` is
impossible. -/
theorem vdpl_integral_extrapolation_step
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : List ℂ)
    {c z : ℂ} {R B Pbound lower : ℝ}
    (hR : 0 < R) (hz : z ∈ ball c R) (hB : 0 ≤ B)
    (hnodes : ∀ a ∈ nodes, a ∈ ball c R)
    (hboundary : ∀ w ∈ sphere c R,
      ‖f w - (polynomial f nodes).eval w‖ /
          nodeProductNorm nodes w ≤ B)
    (hpolyTarget : ‖(polynomial f nodes).eval z‖ ≤ Pbound)
    (hbudget :
      Pbound + nodeProductNorm nodes z *
          (R * (B / (R - dist z c))) < lower)
    (hliouville : g z = 0 ∨ lower ≤ ‖f z‖) :
    g z = 0 := by
  rcases hliouville with hzero | hlower
  · exact hzero
  exfalso
  have hrem := norm_remainder_le_of_boundary_div_nodeProductNorm
    hf nodes hR hz hB hnodes hboundary
  have hwhole :
      ‖f z‖ ≤ ‖(polynomial f nodes).eval z‖ +
          ‖f z - (polynomial f nodes).eval z‖ := by
    calc
      ‖f z‖ = ‖(polynomial f nodes).eval z +
          (f z - (polynomial f nodes).eval z)‖ := by congr 1; ring
      _ ≤ ‖(polynomial f nodes).eval z‖ +
          ‖f z - (polynomial f nodes).eval z‖ := norm_add_le _ _
  have : ‖f z‖ < lower := by
    calc
      ‖f z‖ ≤ ‖(polynomial f nodes).eval z‖ +
          ‖f z - (polynomial f nodes).eval z‖ := hwhole
      _ ≤ Pbound + nodeProductNorm nodes z *
          (R * (B / (R - dist z c))) := add_le_add hpolyTarget hrem
      _ < lower := hbudget
  linarith

/-- A source-shaped version of the one-step theorem.  Instead of a boundary
quotient, callers may provide separate upper bounds for the entire function
and its Hermite polynomial and a positive lower bound for the nodal product.
This is the form used after inserting the explicit integral-node product
estimates. -/
theorem vdpl_integral_extrapolation_step_of_boundary_bounds
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : List ℂ)
    {c z : ℂ} {R F H D Pbound lower : ℝ}
    (hR : 0 < R) (hz : z ∈ ball c R)
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hD : 0 < D)
    (hnodes : ∀ a ∈ nodes, a ∈ ball c R)
    (hboundaryF : ∀ w ∈ sphere c R, ‖f w‖ ≤ F)
    (hboundaryPolynomial : ∀ w ∈ sphere c R,
      ‖(polynomial f nodes).eval w‖ ≤ H)
    (hboundaryProduct : ∀ w ∈ sphere c R,
      D ≤ nodeProductNorm nodes w)
    (hpolyTarget : ‖(polynomial f nodes).eval z‖ ≤ Pbound)
    (hbudget :
      Pbound + nodeProductNorm nodes z *
          (R * (((F + H) / D) / (R - dist z c))) < lower)
    (hliouville : g z = 0 ∨ lower ≤ ‖f z‖) :
    g z = 0 := by
  apply vdpl_integral_extrapolation_step hf nodes hR hz
    (div_nonneg (add_nonneg hF hH) hD.le)
    hnodes
  · exact boundary_div_nodeProductNorm_le hD hboundaryF
      hboundaryPolynomial hboundaryProduct
  · exact hpolyTarget
  · exact hbudget
  · exact hliouville

/-- Pointwise one-step extrapolation immediately yields vanishing on a finite
target set.  This is convenient for the integer interval at each source
recursion level. -/
theorem vdpl_integral_extrapolation_finset
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : List ℂ)
    (targets : Finset ℂ) {c : ℂ} {R B Pbound lower : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B)
    (hnodes : ∀ a ∈ nodes, a ∈ ball c R)
    (htargets : ∀ z ∈ targets, z ∈ ball c R)
    (hboundary : ∀ w ∈ sphere c R,
      ‖f w - (polynomial f nodes).eval w‖ /
          nodeProductNorm nodes w ≤ B)
    (hpolyTarget : ∀ z ∈ targets,
      ‖(polynomial f nodes).eval z‖ ≤ Pbound)
    (hbudget : ∀ z ∈ targets,
      Pbound + nodeProductNorm nodes z *
          (R * (B / (R - dist z c))) < lower)
    (hliouville : ∀ z ∈ targets, g z = 0 ∨ lower ≤ ‖f z‖) :
    ∀ z ∈ targets, g z = 0 := by
  intro z hz
  exact vdpl_integral_extrapolation_step hf nodes hR (htargets z hz) hB
    hnodes hboundary (hpolyTarget z hz) (hbudget z hz) (hliouville z hz)

end Erdos240.BakerIntegralExtrapolation

#print axioms Erdos240.BakerIntegralExtrapolation.vdpl_integral_extrapolation_step

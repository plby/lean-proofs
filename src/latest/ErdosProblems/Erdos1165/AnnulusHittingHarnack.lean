/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.GreenAsymptotic

/-!
# Sharp annular hitting comparisons

This module converts the quantitative potential-kernel gradient into a
multiplicative comparison for probabilities of hitting a fixed point before
leaving a finite planar disc.  The comparison is uniform over the two
starting boundary points.  It keeps the elementary geometric logarithmic
envelopes as explicit inputs, so it can be instantiated at any of the nested
Hao--Li--Okada--Zheng scales.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165
namespace AnnulusHittingHarnack

open Annulus AnnulusHarnack GreenFunction GreenProbability GreenAsymptotic
open PlanarPotential PotentialKernel PotentialConvergence PotentialAsymptotic

noncomputable section

theorem infiniteGreen_closedDisc_diagonal_toReal_pos
    (R : ℕ) {target : Point} (htarget : target ∈ closedDisc R) :
    0 < (infiniteGreen (closedDisc R) target target).toReal := by
  have hfinite : infiniteGreen (closedDisc R) target target ≠ ⊤ := by
    apply infiniteGreen_ne_top_of_subset_coordinateBox (closedDisc R) R
    intro z hz
    exact (mem_closedDisc R z).mp hz |>.1
  have hone : (1 : ℝ≥0∞) ≤ infiniteGreen (closedDisc R) target target := by
    have hzero : killedPower planarKernel (closedDisc R) 0 target target ≤
        ∑' n, killedPower planarKernel (closedDisc R) n target target :=
      ENNReal.le_tsum 0
    simpa [infiniteGreen, killedPower, htarget] using hzero
  have honeReal : (1 : ℝ) ≤
      (infiniteGreen (closedDisc R) target target).toReal := by
    simpa using ENNReal.toReal_mono hfinite hone
  linarith

/-- Quantitative annular Harnack comparison in the exact form needed for
boundary starting points.  The geometric inputs are logarithmic envelopes
on the stopped support and its exit boundary, together with an additive
potential oscillation estimate between the two starting points. -/
theorem hitBeforeExit_closedDisc_compare_of_pointLog_window
    (R : ℕ) {target x y : Point}
    (htarget : target ∈ closedDisc R)
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    {L U oscillation lower : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - target))
    (hU : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      pointLogMain (z - target) ≤ U)
    (hoscNonneg : 0 ≤ oscillation)
    (hosc : |planarPotentialKernel (y - target) -
      planarPotentialKernel (x - target)| ≤ oscillation)
    (hlower : 0 < lower)
    (href : lower ≤ L - 100 - planarPotentialKernel (x - target)) :
    let error := U - L + 200 + oscillation
    (1 - error / lower) *
        (simpleRandomWalkFrom x
          (walkHitBeforeExit (closedDisc R) target)).toReal ≤
      (simpleRandomWalkFrom y
        (walkHitBeforeExit (closedDisc R) target)).toReal ∧
    (simpleRandomWalkFrom y
        (walkHitBeforeExit (closedDisc R) target)).toReal ≤
      (1 + error / lower) *
        (simpleRandomWalkFrom x
          (walkHitBeforeExit (closedDisc R) target)).toReal := by
  dsimp only
  let gx := (infiniteGreen (closedDisc R) x target).toReal
  let gy := (infiniteGreen (closedDisc R) y target).toReal
  let d := (infiniteGreen (closedDisc R) target target).toReal
  have hxLower :=
    pointLogMainBoundaryLower_sub_le_infiniteGreen_toReal
      R hx (y := target) hL
  have hyLower :=
    pointLogMainBoundaryLower_sub_le_infiniteGreen_toReal
      R hy (y := target) hL
  have hxUpper := infiniteGreen_toReal_le_of_pointLogMain_le R hx hU
  have hyUpper := infiniteGreen_toReal_le_of_pointLogMain_le R hy hU
  have hxLower' : (L - 100) - planarPotentialKernel (x - target) ≤ gx := by
    dsimp only [gx]
    linarith
  have hyLower' : (L - 100) - planarPotentialKernel (y - target) ≤ gy := by
    dsimp only [gy]
    linarith
  have hxUpper' : gx ≤ (U + 100) - planarPotentialKernel (x - target) := by
    dsimp only [gx]
    linarith
  have hyUpper' : gy ≤ (U + 100) - planarPotentialKernel (y - target) := by
    dsimp only [gy]
    linarith
  have hdiff0 := abs_sub_le_of_common_potential_window
    hxLower' hxUpper' hyLower' hyUpper'
  have hdiff : |gy - gx| ≤ U - L + 200 + oscillation := by
    dsimp only [gx, gy]
    linarith
  have herror : 0 ≤ U - L + 200 + oscillation := by
    have hgxNonneg : 0 ≤ gx := ENNReal.toReal_nonneg
    have hgyNonneg : 0 ≤ gy := ENNReal.toReal_nonneg
    have hwidth : L - 100 ≤ U + 100 := by
      dsimp only [gx] at hxLower hxUpper hgxNonneg
      linarith
    linarith
  have hgreenLower : lower ≤ gx := by
    dsimp only [gx]
    exact href.trans hxLower
  have hmult := multiplicative_compare_of_additive herror hlower hgreenLower hdiff
  have hd : 0 < d := by
    dsimp only [d]
    exact infiniteGreen_closedDisc_diagonal_toReal_pos R htarget
  have hpx := simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div
    R x target htarget
  have hpy := simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div
    R y target htarget
  dsimp only [gx, gy, d] at hmult ⊢
  rw [hpx, hpy]
  constructor
  · calc
      (1 - (U - L + 200 + oscillation) / lower) *
          ((infiniteGreen (closedDisc R) x target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal) =
        ((1 - (U - L + 200 + oscillation) / lower) *
          (infiniteGreen (closedDisc R) x target).toReal) /
            (infiniteGreen (closedDisc R) target target).toReal := by ring
      _ ≤ (infiniteGreen (closedDisc R) y target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal :=
        div_le_div_of_nonneg_right hmult.1 hd.le
  · calc
      (infiniteGreen (closedDisc R) y target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal ≤
        ((1 + (U - L + 200 + oscillation) / lower) *
          (infiniteGreen (closedDisc R) x target).toReal) /
            (infiniteGreen (closedDisc R) target target).toReal :=
        div_le_div_of_nonneg_right hmult.2 hd.le
      _ = (1 + (U - L + 200 + oscillation) / lower) *
          ((infiniteGreen (closedDisc R) x target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal) := by ring

/-- Explicit error term in the all-parity potential oscillation bound. -/
noncomputable def anchoredPotentialError (u v : Point) : ℝ :=
  300 / ((max (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) - 2 : ℕ) : ℝ) +
  150 * ((PotentialGradient.natGap
        (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
        (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) : ℝ) +
      PotentialGradient.natGap
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor v))) /
    ((max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) -
        (PotentialGradient.natGap
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) +
          PotentialGradient.natGap
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor v))) : ℕ) : ℝ) +
  300 / ((max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) - 2 : ℕ) : ℝ)

/-- Scale-ratio form of the anchored error.  If all three denominators are
at least `rho` and the diagonal displacement is at most `gap`, the loss is
`(600 + 150 gap) / rho`. -/
theorem anchoredPotentialError_le_scale {u v : Point} {rho gap : ℕ}
    (hrho : 0 < rho)
    (hv : rho ≤ max (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) - 2)
    (hmiddle : rho ≤
      max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) -
        (PotentialGradient.natGap
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) +
          PotentialGradient.natGap
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor v))))
    (hu : rho ≤ max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) - 2)
    (hgap : PotentialGradient.natGap
          (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) +
        PotentialGradient.natGap
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) ≤ gap) :
    anchoredPotentialError u v ≤
      600 / (rho : ℝ) + 150 * (gap : ℝ) / (rho : ℝ) := by
  unfold anchoredPotentialError
  have hrhoReal : (0 : ℝ) < rho := by exact_mod_cast hrho
  have hvReal : (rho : ℝ) ≤
      (max (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) - 2 : ℕ) := by
    exact_mod_cast hv
  have hmReal : (rho : ℝ) ≤
      (max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) -
        (PotentialGradient.natGap
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) +
          PotentialGradient.natGap
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor v))) : ℕ) := by
    exact_mod_cast hmiddle
  have huReal : (rho : ℝ) ≤
      (max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) - 2 : ℕ) := by
    exact_mod_cast hu
  have hgapReal :
      ((PotentialGradient.natGap
          (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) : ℕ) : ℝ) +
        PotentialGradient.natGap
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) ≤ gap := by
    exact_mod_cast hgap
  have hvPos : (0 : ℝ) <
      (max (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) - 2 : ℕ) :=
    hrhoReal.trans_le hvReal
  have hmPos : (0 : ℝ) <
      (max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) -
        (PotentialGradient.natGap
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) +
          PotentialGradient.natGap
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor v))) : ℕ) :=
    hrhoReal.trans_le hmReal
  have huPos : (0 : ℝ) <
      (max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) - 2 : ℕ) :=
    hrhoReal.trans_le huReal
  calc
    300 / (↑(max (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) - 2) : ℝ) +
        150 * (↑(PotentialGradient.natGap
              (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
              (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))) +
            ↑(PotentialGradient.natGap
              (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
              (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)))) /
          (↑(max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
            (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) -
              (PotentialGradient.natGap
                (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
                (EndpointDiagonal.firstDiagonalOffset (evenAnchor v)) +
              PotentialGradient.natGap
                (EndpointDiagonal.secondDiagonalOffset (evenAnchor u))
                (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)))) : ℝ) +
        300 / (↑(max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) - 2) : ℝ) ≤
      300 / rho + 150 * gap / rho + 300 / rho := by
        gcongr
    _ = 600 / (rho : ℝ) + 150 * (gap : ℝ) / (rho : ℝ) := by ring

/-- Fully explicit whole-lattice annular Harnack comparison.  Parity is
handled by `evenAnchor`; the scale loss is inverse-radius for the two anchor
steps plus `150 L/(R-L)` for the central displacement. -/
theorem hitBeforeExit_closedDisc_compare_via_evenAnchors
    (R : ℕ) {target x y : Point}
    (htarget : target ∈ closedDisc R)
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    {L U lower : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - target))
    (hU : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      pointLogMain (z - target) ≤ U)
    (hxR : 2 < max
      (EndpointDiagonal.firstDiagonalOffset (evenAnchor (x - target)))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor (x - target))))
    (hyR : 2 < max
      (EndpointDiagonal.firstDiagonalOffset (evenAnchor (y - target)))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor (y - target))))
    (hgap : PotentialGradient.natGap
          (EndpointDiagonal.firstDiagonalOffset (evenAnchor (x - target)))
          (EndpointDiagonal.firstDiagonalOffset (evenAnchor (y - target))) +
        PotentialGradient.natGap
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor (x - target)))
          (EndpointDiagonal.secondDiagonalOffset (evenAnchor (y - target))) <
      max (EndpointDiagonal.firstDiagonalOffset (evenAnchor (x - target)))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor (x - target))))
    (hlower : 0 < lower)
    (href : lower ≤ L - 100 - planarPotentialKernel (x - target)) :
    let error := U - L + 200 + anchoredPotentialError (x - target) (y - target)
    (1 - error / lower) *
        (simpleRandomWalkFrom x
          (walkHitBeforeExit (closedDisc R) target)).toReal ≤
      (simpleRandomWalkFrom y
        (walkHitBeforeExit (closedDisc R) target)).toReal ∧
    (simpleRandomWalkFrom y
        (walkHitBeforeExit (closedDisc R) target)).toReal ≤
      (1 + error / lower) *
        (simpleRandomWalkFrom x
          (walkHitBeforeExit (closedDisc R) target)).toReal := by
  apply hitBeforeExit_closedDisc_compare_of_pointLog_window
    R htarget hx hy hL hU
  · unfold anchoredPotentialError
    positivity
  · unfold anchoredPotentialError
    exact abs_planarPotentialKernel_sub_le_via_evenAnchors hxR hyR hgap
  · exact hlower
  · exact href

end

end AnnulusHittingHarnack
end Erdos1165

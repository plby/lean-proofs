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

import ErdosProblems.Erdos1165.GreenHarnack
import ErdosProblems.Erdos1165.PotentialRadialShell

/-!
# Boundary-sharp multiplicative annular Harnack estimates

This module turns the boundary-reference Green estimate into a direct
multiplicative comparison of hit-before-exit probabilities.  Unlike the
coarser logarithmic-window comparison, its error contains no global
potential-asymptotic constant: it is exactly twice the potential oscillation
on the exit boundary plus the potential oscillation between the starting
points, divided by a positive Green lower bound.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165
namespace SharpAnnulusHarnack

open Annulus AnnulusHarnack AnnulusHittingHarnack GreenFunction GreenProbability
open GreenAsymptotic GreenHarnack PlanarPotential PotentialConvergence
open PotentialRadialMass PotentialRadialShell

noncomputable section

/-- The diagonal-coordinate geometry needed to apply the radial-shell
potential estimate to two arbitrary lattice points.  The points themselves
need not have even parity: `evenAnchor` changes each by at most one
nearest-neighbor step before the radial estimate is applied. -/
structure RadialShellPair (u v : Point) (rho : ℕ) : Prop where
  two_le : 2 ≤ rho
  first_u_le : EndpointDiagonal.firstDiagonalOffset (evenAnchor u) ≤ 2 * rho
  second_u_le : EndpointDiagonal.secondDiagonalOffset (evenAnchor u) ≤ 2 * rho
  first_v_le : EndpointDiagonal.firstDiagonalOffset (evenAnchor v) ≤ 2 * rho
  second_v_le : EndpointDiagonal.secondDiagonalOffset (evenAnchor v) ≤ 2 * rho
  radius_u_sub_two : rho ≤
    max (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)) - 2
  radius_v_sub_two : rho ≤
    max (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
      (EndpointDiagonal.secondDiagonalOffset (evenAnchor v)) - 2
  radiusSq_gap : PotentialGradient.natGap
      (PotentialRadialMass.radiusSq
        (EndpointDiagonal.firstDiagonalOffset (evenAnchor u))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor u)))
      (PotentialRadialMass.radiusSq
        (EndpointDiagonal.firstDiagonalOffset (evenAnchor v))
        (EndpointDiagonal.secondDiagonalOffset (evenAnchor v))) ≤ 8 * rho

/-- Explicit error delivered by the radial-shell comparison after paying for
the two parity-correction steps. -/
def radialShellError (rho : ℕ) : ℝ := 2100000600 / (rho : ℝ)

theorem radialShellError_nonneg (rho : ℕ) : 0 ≤ radialShellError rho := by
  unfold radialShellError
  positivity

/-- Whole-lattice radial-shell potential comparison.  The central
even-to-even comparison costs `2100000000 / rho`; each of the two
parity-correction steps costs at most `300 / rho`. -/
theorem abs_planarPotentialKernel_sub_le_of_radialShellPair
    {u v : Point} {rho : ℕ} (h : RadialShellPair u v rho) :
    |planarPotentialKernel v - planarPotentialKernel u| ≤ radialShellError rho := by
  let du := EndpointDiagonal.firstDiagonalOffset (evenAnchor u)
  let eu := EndpointDiagonal.secondDiagonalOffset (evenAnchor u)
  let dv := EndpointDiagonal.firstDiagonalOffset (evenAnchor v)
  let ev := EndpointDiagonal.secondDiagonalOffset (evenAnchor v)
  have hrhoNat : 0 < rho := lt_of_lt_of_le Nat.zero_lt_two h.two_le
  have hrho : 0 < (rho : ℝ) := by exact_mod_cast hrhoNat
  have hRu : 2 < max du eu := by
    dsimp only [du, eu]
    exact Nat.sub_pos_iff_lt.mp
      (lt_of_lt_of_le hrhoNat h.radius_u_sub_two)
  have hRv : 2 < max dv ev := by
    dsimp only [dv, ev]
    exact Nat.sub_pos_iff_lt.mp
      (lt_of_lt_of_le hrhoNat h.radius_v_sub_two)
  have huAnchor := abs_planarPotentialKernel_sub_evenAnchor_le (x := u) hRu
  have hvAnchor := abs_planarPotentialKernel_sub_evenAnchor_le (x := v) hRv
  have huAnchor' :
      |planarPotentialKernel u - planarPotentialKernel (evenAnchor u)| ≤
        300 / (rho : ℝ) := by
    apply huAnchor.trans
    apply div_le_div_of_nonneg_left (by norm_num) hrho
    exact_mod_cast h.radius_u_sub_two
  have hvAnchor' :
      |planarPotentialKernel v - planarPotentialKernel (evenAnchor v)| ≤
        300 / (rho : ℝ) := by
    apply hvAnchor.trans
    apply div_le_div_of_nonneg_left (by norm_num) hrho
    exact_mod_cast h.radius_v_sub_two
  have hradius_u : rho ≤ max du eu := by
    dsimp only [du, eu]
    exact h.radius_u_sub_two.trans (Nat.sub_le _ _)
  have hradius_v : rho ≤ max dv ev := by
    dsimp only [dv, ev]
    exact h.radius_v_sub_two.trans (Nat.sub_le _ _)
  have hmiddleFourier :
      |PotentialFourierIntegral.fourierPotential du eu -
          PotentialFourierIntegral.fourierPotential dv ev| ≤
        2100000000 / (rho : ℝ) := by
    apply PotentialRadialShell.abs_fourierPotential_sub_le_of_radiusSq_gap h.two_le
    · exact h.first_u_le
    · exact h.second_u_le
    · exact h.first_v_le
    · exact h.second_v_le
    · exact hradius_u
    · exact hradius_v
    · exact h.radiusSq_gap
  have hmiddle :
      |planarPotentialKernel (evenAnchor u) -
          planarPotentialKernel (evenAnchor v)| ≤
        2100000000 / (rho : ℝ) := by
    rw [planarPotentialKernel_eq_diagonalPotential_of_even (even_evenAnchor u),
      planarPotentialKernel_eq_diagonalPotential_of_even (even_evenAnchor v),
      PotentialAsymptotic.diagonalPotential_eq_fourierPotential,
      PotentialAsymptotic.diagonalPotential_eq_fourierPotential]
    exact hmiddleFourier
  unfold radialShellError
  calc
    |planarPotentialKernel v - planarPotentialKernel u| ≤
        |planarPotentialKernel v - planarPotentialKernel (evenAnchor v)| +
          |planarPotentialKernel (evenAnchor v) -
            planarPotentialKernel (evenAnchor u)| +
          |planarPotentialKernel (evenAnchor u) - planarPotentialKernel u| := by
      have hdecomp :
          planarPotentialKernel v - planarPotentialKernel u =
            (planarPotentialKernel v - planarPotentialKernel (evenAnchor v)) +
              (planarPotentialKernel (evenAnchor v) -
                planarPotentialKernel (evenAnchor u)) +
              (planarPotentialKernel (evenAnchor u) - planarPotentialKernel u) := by
        ring
      rw [hdecomp]
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 300 / (rho : ℝ) + 2100000000 / (rho : ℝ) + 300 / (rho : ℝ) := by
      exact add_le_add
        (add_le_add hvAnchor' (by simpa only [abs_sub_comm] using hmiddle))
        (by simpa only [abs_sub_comm] using huAnchor')
    _ = 2100000600 / (rho : ℝ) := by ring

/-- Uniform whole-lattice exit-boundary specialization of the radial-shell
estimate.  This is exactly the boundary premise consumed by
`hitBeforeExit_closedDisc_compare_of_boundaryReference`. -/
theorem closedDisc_boundary_potential_oscillation_le_radialShellError
    (R rho : ℕ) {target q : Point}
    (hgeom : ∀ z, z ∈ outerBoundary (closedDisc R) →
      RadialShellPair (q - target) (z - target) rho) :
    ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤ radialShellError rho := by
  intro z hz
  exact abs_planarPotentialKernel_sub_le_of_radialShellPair (hgeom z hz)

/-- Boundary-sharp multiplicative Harnack comparison for hitting a point
before leaving a disc.  Only actual potential oscillations occur in the
error; in particular there is no `O(1)` logarithmic-envelope loss. -/
theorem hitBeforeExit_closedDisc_compare_of_boundaryReference
    (R : ℕ) {target x y q : Point}
    (htarget : target ∈ closedDisc R)
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    {boundaryError startError lower : ℝ}
    (hboundaryNonneg : 0 ≤ boundaryError)
    (hboundary : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤ boundaryError)
    (hstartNonneg : 0 ≤ startError)
    (hstart : |planarPotentialKernel (y - target) -
      planarPotentialKernel (x - target)| ≤ startError)
    (hlower : 0 < lower)
    (href : lower ≤ planarPotentialKernel (q - target) -
      planarPotentialKernel (x - target) - boundaryError) :
    let error := 2 * boundaryError + startError
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
  have hxApprox := abs_infiniteGreen_toReal_sub_boundaryReference_le R hx hboundary
  have hyApprox := abs_infiniteGreen_toReal_sub_boundaryReference_le R hy hboundary
  have hxBounds := abs_le.mp hxApprox
  have hyBounds := abs_le.mp hyApprox
  have hxLower :
      (planarPotentialKernel (q - target) - boundaryError) -
          planarPotentialKernel (x - target) ≤ gx := by
    dsimp only [gx]
    linarith
  have hxUpper : gx ≤
      (planarPotentialKernel (q - target) + boundaryError) -
        planarPotentialKernel (x - target) := by
    dsimp only [gx]
    linarith
  have hyLower :
      (planarPotentialKernel (q - target) - boundaryError) -
          planarPotentialKernel (y - target) ≤ gy := by
    dsimp only [gy]
    linarith
  have hyUpper : gy ≤
      (planarPotentialKernel (q - target) + boundaryError) -
        planarPotentialKernel (y - target) := by
    dsimp only [gy]
    linarith
  have hdiff0 := abs_sub_le_of_common_potential_window
    hxLower hxUpper hyLower hyUpper
  have hdiff : |gy - gx| ≤ 2 * boundaryError + startError := by
    dsimp only [gx, gy]
    linarith
  have herror : 0 ≤ 2 * boundaryError + startError := by linarith
  have hgreenLower : lower ≤ gx := by
    dsimp only [gx]
    exact href.trans (by linarith [hxBounds.1])
  have hmult := multiplicative_compare_of_additive herror hlower hgreenLower hdiff
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_of_lt_of_le zero_lt_one
      (one_le_infiniteGreen_closedDisc_diagonal_toReal R htarget)
  have hpx := simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div
    R x target htarget
  have hpy := simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div
    R y target htarget
  dsimp only [gx, gy, d] at hmult ⊢
  rw [hpx, hpy]
  constructor
  · calc
      (1 - (2 * boundaryError + startError) / lower) *
          ((infiniteGreen (closedDisc R) x target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal) =
        ((1 - (2 * boundaryError + startError) / lower) *
          (infiniteGreen (closedDisc R) x target).toReal) /
            (infiniteGreen (closedDisc R) target target).toReal := by ring
      _ ≤ (infiniteGreen (closedDisc R) y target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal :=
        div_le_div_of_nonneg_right hmult.1 hd.le
  · calc
      (infiniteGreen (closedDisc R) y target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal ≤
        ((1 + (2 * boundaryError + startError) / lower) *
          (infiniteGreen (closedDisc R) x target).toReal) /
            (infiniteGreen (closedDisc R) target target).toReal :=
        div_le_div_of_nonneg_right hmult.2 hd.le
      _ = (1 + (2 * boundaryError + startError) / lower) *
          ((infiniteGreen (closedDisc R) x target).toReal /
            (infiniteGreen (closedDisc R) target target).toReal) := by ring

/-- The same sharp probability comparison with the starting-point
oscillation discharged by the all-parity anchored gradient. -/
theorem hitBeforeExit_closedDisc_compare_via_startAnchors
    (R : ℕ) {target x y q : Point}
    (htarget : target ∈ closedDisc R)
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    {boundaryError lower : ℝ}
    (hboundaryNonneg : 0 ≤ boundaryError)
    (hboundary : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤ boundaryError)
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
    (href : lower ≤ planarPotentialKernel (q - target) -
      planarPotentialKernel (x - target) - boundaryError) :
    let error := 2 * boundaryError +
      anchoredPotentialError (x - target) (y - target)
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
  apply hitBeforeExit_closedDisc_compare_of_boundaryReference
    R htarget hx hy hboundaryNonneg hboundary
  · exact anchoredPotentialError_nonneg _ _
  · exact abs_planarPotentialKernel_sub_le_via_evenAnchors hxR hyR hgap
  · exact hlower
  · exact href

/-- Fully radial-shell-dischargeable hit-probability Harnack comparison.
The caller supplies one uniform shell certificate from the reference point
to every exit-boundary point and one certificate between the two starting
points.  No potential-oscillation hypothesis remains. -/
theorem hitBeforeExit_closedDisc_compare_via_radialShell
    (R boundaryRho startRho : ℕ) {target x y q : Point}
    (htarget : target ∈ closedDisc R)
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    (hboundaryGeom : ∀ z, z ∈ outerBoundary (closedDisc R) →
      RadialShellPair (q - target) (z - target) boundaryRho)
    (hstartGeom : RadialShellPair (x - target) (y - target) startRho)
    {lower : ℝ}
    (hlower : 0 < lower)
    (href : lower ≤ planarPotentialKernel (q - target) -
      planarPotentialKernel (x - target) - radialShellError boundaryRho) :
    let error := 2 * radialShellError boundaryRho + radialShellError startRho
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
  apply hitBeforeExit_closedDisc_compare_of_boundaryReference
    R htarget hx hy (radialShellError_nonneg boundaryRho)
  · exact closedDisc_boundary_potential_oscillation_le_radialShellError
      R boundaryRho hboundaryGeom
  · exact radialShellError_nonneg startRho
  · exact abs_planarPotentialKernel_sub_le_of_radialShellPair hstartGeom
  · exact hlower
  · exact href

end

end SharpAnnulusHarnack
end Erdos1165

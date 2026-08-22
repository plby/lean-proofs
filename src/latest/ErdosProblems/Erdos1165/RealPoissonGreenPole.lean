/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.PoissonKernelGreenPole

/-!
# Moving-pole Green comparison at real radii

This module is the real-radius counterpart of `PoissonKernelGreenPole`.
The killed domain is an arbitrary finite set contained in a coordinate box;
the only geometric assumption on it is that its graph outer boundary lies on
the literal inner vertex boundary of the Euclidean disc of radius `R`.

There is no rounding of `R`, `S`, or `r`.  A fixed lattice point `q` on the
literal radius-`R` boundary is used as the potential-kernel reference.  This
avoids the nonexistent notion of a lattice axis point at an arbitrary real
radius.
-/

open Real Set
open scoped ENNReal

namespace Erdos1165.RealPoissonGreenPole

open Annulus AnnulusHarnack BoundaryStoppedHarnack GreenProbability
open PlanarPotential PoissonKernelGreenPole PoissonKernelRadial
open PotentialConvergence PotentialEuclideanGeometry PotentialRadialAsymptotic
open PotentialRadialGlobal RadialHarnackSpecialization

noncomputable section

/-! ## A literal real radial cut -/

/-- The two-unit radial shell used as the intermediate cut. -/
def thickRealRadialCut (S : ℝ) : Set Point :=
  {z | S < euclideanRadius z ∧ euclideanRadius z < S + 2}

@[simp] theorem mem_thickRealRadialCut {S : ℝ} {z : Point} :
    z ∈ thickRealRadialCut S ↔
      S < euclideanRadius z ∧ euclideanRadius z < S + 2 := by
  rfl

/-! ## Explicit errors -/

/-- The smallest radius guaranteed after translating a literal radius-`R`
boundary point by a pole of radius at most `r`. -/
def boundaryPoleGap (R r : ℝ) : ℝ := R - r - 1

/-- A deliberately one-unit-weakened lower radius at the intermediate cut.
The spare unit makes this form stable under subsequent nearest-neighbor
specializations. -/
def intermediatePoleGap (S r : ℝ) : ℝ := S - r - 1

def boundaryPoleError (R r : ℝ) : ℝ :=
  (2 * globalRadialConstant + (2 * r + 1)) / boundaryPoleGap R r

/-- Error from moving the inner pole at the fixed real-radius boundary
reference point. -/
def outerPoleError (R r : ℝ) : ℝ :=
  (2 * globalRadialConstant + 2 * r) / boundaryPoleGap R r

def intermediatePoleError (S r : ℝ) : ℝ :=
  (2 * globalRadialConstant + 2 * r) / intermediatePoleGap S r

def greenPoleAdditiveError (R S r : ℝ) : ℝ :=
  2 * boundaryPoleError R r + outerPoleError R r +
    intermediatePoleError S r

/-- Explicit positive reference value needed to turn the additive Green
comparison into a multiplicative one. -/
def greenPoleLower (R S r : ℝ) : ℝ :=
  (2 / Real.pi) * Real.log
      (boundaryPoleGap R r / (S + r + 2)) -
    globalRadialConstant / boundaryPoleGap R r -
    globalRadialConstant / intermediatePoleGap S r -
    boundaryPoleError R r

def greenPoleRelativeError (R S r : ℝ) : ℝ :=
  greenPoleAdditiveError R S r / greenPoleLower R S r

theorem boundaryPoleGap_pos
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R) :
    0 < boundaryPoleGap R r := by
  unfold boundaryPoleGap
  linarith

theorem intermediatePoleGap_pos
    {S r : ℝ} (hS : r + 2 ≤ S) :
    0 < intermediatePoleGap S r := by
  unfold intermediatePoleGap
  linarith

theorem boundaryPoleError_nonneg
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R) :
    0 ≤ boundaryPoleError R r := by
  unfold boundaryPoleError
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  exact div_nonneg (by linarith) (boundaryPoleGap_pos hr hS hscale).le

theorem outerPoleError_nonneg
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R) :
    0 ≤ outerPoleError R r := by
  unfold outerPoleError
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  exact div_nonneg (by linarith) (boundaryPoleGap_pos hr hS hscale).le

theorem intermediatePoleError_nonneg
    {S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S) :
    0 ≤ intermediatePoleError S r := by
  unfold intermediatePoleError
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  exact div_nonneg (by linarith) (intermediatePoleGap_pos hS).le

theorem greenPoleAdditiveError_nonneg
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R) :
    0 ≤ greenPoleAdditiveError R S r := by
  unfold greenPoleAdditiveError
  have hb := boundaryPoleError_nonneg hr hS hscale
  have ho := outerPoleError_nonneg hr hS hscale
  have hi := intermediatePoleError_nonneg hr hS
  linarith

theorem greenPoleRelativeError_nonneg
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R)
    (hlower : 0 < greenPoleLower R S r) :
    0 ≤ greenPoleRelativeError R S r := by
  unfold greenPoleRelativeError
  exact div_nonneg (greenPoleAdditiveError_nonneg hr hS hscale) hlower.le

/-! ## Real-radius shell geometry -/

/-- Every vertex of the literal inner boundary of the real-radius disc lies
in the shell `(R-1,R]`. -/
theorem discBoundary_zero_euclideanRadius_bounds_real
    {R : ℝ} {z : Point}
    (hz : z ∈ ThickPoint.discBoundary 0 R) :
    R - 1 < euclideanRadius z ∧ euclideanRadius z ≤ R := by
  rcases hz with ⟨hzIn, y, hyOut, hzy⟩
  have hzUpper : euclideanRadius z ≤ R := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hzIn
  have hyLower : R < euclideanRadius y := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hyOut
  have hgap := abs_euclideanRadius_sub_le_of_adjacent hzy
  exact ⟨by linarith [(abs_le.mp hgap).1], hzUpper⟩

private theorem literalBoundary_sub_inner_bounds
    {R r : ℝ} {w x : Point}
    (hw : w ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) :
    boundaryPoleGap R r ≤ euclideanRadius (w - x) ∧
      euclideanRadius (w - x) ≤ R + r := by
  have hwBounds := discBoundary_zero_euclideanRadius_bounds_real hw
  have hlower := euclideanRadius_sub_lower w x
  have hupper := euclideanRadius_sub_le_add w x
  constructor
  · unfold boundaryPoleGap
    linarith
  · linarith

private theorem thickRealRadialCut_sub_inner_bounds
    {S r : ℝ} {start x : Point}
    (hstart : start ∈ thickRealRadialCut S)
    (hx : euclideanRadius x ≤ r) :
    intermediatePoleGap S r ≤ euclideanRadius (start - x) ∧
      euclideanRadius (start - x) ≤ S + r + 2 := by
  have hstartBounds := mem_thickRealRadialCut.mp hstart
  have hlower := euclideanRadius_sub_lower start x
  have hupper := euclideanRadius_sub_le_add start x
  constructor
  · unfold intermediatePoleGap
    linarith
  · linarith

/-! ## Potential-kernel estimates -/

/-- Uniform oscillation of the shifted potential on a literal real-radius
boundary, relative to an arbitrary fixed point `q` of that boundary. -/
theorem literalBoundary_shifted_potential_oscillation
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R)
    {q x : Point} (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) :
    ∀ w, w ∈ ThickPoint.discBoundary 0 R →
      |planarPotentialKernel (w - x) -
        planarPotentialKernel (q - x)| ≤ boundaryPoleError R r := by
  intro w hw
  have hwBounds := literalBoundary_sub_inner_bounds hw hx
  have hqBounds := literalBoundary_sub_inner_bounds hq hx
  have hrho : 0 < boundaryPoleGap R r :=
    boundaryPoleGap_pos hr hS hscale
  have hw0 : w - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hwBounds.1)
  have hq0 : q - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hqBounds.1)
  have hgap :
      |euclideanRadius (w - x) - euclideanRadius (q - x)| ≤
        2 * r + 1 := by
    unfold boundaryPoleGap at hwBounds hqBounds
    rw [abs_le]
    constructor <;> linarith
  simpa [boundaryPoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := w - x) (y := q - x) hrho hw0 hq0
      hwBounds.1 hqBounds.1 hgap)

/-- Moving the pole inside the radius-`r` disc at a fixed literal-boundary
reference point. -/
theorem boundaryReference_potential_oscillation_inner_poles
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R)
    {q x y : Point} (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |planarPotentialKernel (q - y) -
      planarPotentialKernel (q - x)| ≤ outerPoleError R r := by
  have hxBounds := literalBoundary_sub_inner_bounds hq hx
  have hyBounds := literalBoundary_sub_inner_bounds hq hy
  have hrho : 0 < boundaryPoleGap R r :=
    boundaryPoleGap_pos hr hS hscale
  have hx0 : q - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hxBounds.1)
  have hy0 : q - y ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hyBounds.1)
  have hxy : euclideanRadius (y - x) ≤ 2 * r :=
    euclideanRadius_sub_le_two_mul_of_le hy hx
  have hgap :
      |euclideanRadius (q - y) - euclideanRadius (q - x)| ≤ 2 * r :=
    (abs_euclideanRadius_sub_sub_le q y x).trans hxy
  simpa [outerPoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := q - y) (y := q - x) hrho hy0 hx0
      hyBounds.1 hxBounds.1 hgap)

/-- Moving the pole at a starting point in the thick real radial cut. -/
theorem intermediate_potential_oscillation_inner_poles
    {S r : ℝ} (_hr : 0 ≤ r) (hS : r + 2 ≤ S)
    {start x y : Point} (hstart : start ∈ thickRealRadialCut S)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |planarPotentialKernel (start - y) -
      planarPotentialKernel (start - x)| ≤
        intermediatePoleError S r := by
  have hxBounds := thickRealRadialCut_sub_inner_bounds hstart hx
  have hyBounds := thickRealRadialCut_sub_inner_bounds hstart hy
  have hrho : 0 < intermediatePoleGap S r := intermediatePoleGap_pos hS
  have hx0 : start - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hxBounds.1)
  have hy0 : start - y ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hyBounds.1)
  have hxy : euclideanRadius (y - x) ≤ 2 * r :=
    euclideanRadius_sub_le_two_mul_of_le hy hx
  have hgap := (abs_euclideanRadius_sub_sub_le start y x).trans hxy
  simpa [intermediatePoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := start - y) (y := start - x) hrho hy0 hx0
      hyBounds.1 hxBounds.1 hgap)

/-- Additive comparison of the two boundary-reference potential values. -/
theorem abs_potentialReferenceDifference_inner_poles
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R)
    {start q x y : Point} (hstart : start ∈ thickRealRadialCut S)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |(planarPotentialKernel (q - y) -
        planarPotentialKernel (start - y)) -
      (planarPotentialKernel (q - x) -
        planarPotentialKernel (start - x))| ≤
      outerPoleError R r + intermediatePoleError S r := by
  have houter := boundaryReference_potential_oscillation_inner_poles
    hr hS hscale hq hx hy
  have hintermediate := intermediate_potential_oscillation_inner_poles
    hr hS hstart hx hy
  calc
    |(planarPotentialKernel (q - y) -
          planarPotentialKernel (start - y)) -
        (planarPotentialKernel (q - x) -
          planarPotentialKernel (start - x))| =
      |(planarPotentialKernel (q - y) -
          planarPotentialKernel (q - x)) -
        (planarPotentialKernel (start - y) -
          planarPotentialKernel (start - x))| := by
            congr 1
            ring
    _ ≤ |planarPotentialKernel (q - y) -
          planarPotentialKernel (q - x)| +
        |planarPotentialKernel (start - y) -
          planarPotentialKernel (start - x)| := abs_sub _ _
    _ ≤ outerPoleError R r + intermediatePoleError S r :=
      add_le_add houter hintermediate

/-- The explicit logarithmic lower bound for the reference Green value. -/
theorem greenPoleLower_le_potentialReference
    {R S r : ℝ} (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R)
    {start q x : Point} (hstart : start ∈ thickRealRadialCut S)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) :
    greenPoleLower R S r ≤
      planarPotentialKernel (q - x) -
        planarPotentialKernel (start - x) - boundaryPoleError R r := by
  let qx := q - x
  let sx := start - x
  have hqBounds := literalBoundary_sub_inner_bounds hq hx
  have hsBounds := thickRealRadialCut_sub_inner_bounds hstart hx
  have hqGap : 0 < boundaryPoleGap R r :=
    boundaryPoleGap_pos hr hS hscale
  have hsGap : 0 < intermediatePoleGap S r :=
    intermediatePoleGap_pos hS
  have hqPos : 0 < euclideanRadius qx := hqGap.trans_le hqBounds.1
  have hsPos : 0 < euclideanRadius sx := hsGap.trans_le hsBounds.1
  have hqExpansion :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      ((euclideanRadius_pos_iff qx).mp hqPos)
  have hsExpansion :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      ((euclideanRadius_pos_iff sx).mp hsPos)
  have hqExpansionLower :
      (2 / Real.pi) * Real.log (euclideanRadius qx) + cPotential -
          globalRadialConstant / euclideanRadius qx ≤
        planarPotentialKernel qx := by
    have h := (abs_le.mp hqExpansion).1
    linarith
  have hsExpansionUpper :
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (euclideanRadius sx) + cPotential +
          globalRadialConstant / euclideanRadius sx := by
    have h := (abs_le.mp hsExpansion).2
    linarith
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  have hqRemainder :
      globalRadialConstant / euclideanRadius qx ≤
        globalRadialConstant / boundaryPoleGap R r :=
    div_le_div_of_nonneg_left hC hqGap hqBounds.1
  have hsRemainder :
      globalRadialConstant / euclideanRadius sx ≤
        globalRadialConstant / intermediatePoleGap S r :=
    div_le_div_of_nonneg_left hC hsGap hsBounds.1
  have hqLog :
      Real.log (boundaryPoleGap R r) ≤
        Real.log (euclideanRadius qx) :=
    Real.log_le_log hqGap hqBounds.1
  have hsumPos : 0 < S + r + 2 := by linarith
  have hsLog :
      Real.log (euclideanRadius sx) ≤ Real.log (S + r + 2) := by
    exact Real.log_le_log hsPos hsBounds.2
  have hcoef : 0 ≤ (2 : ℝ) / Real.pi := by positivity
  have hqMainLower :
      (2 / Real.pi) * Real.log (boundaryPoleGap R r) + cPotential -
          globalRadialConstant / boundaryPoleGap R r ≤
        planarPotentialKernel qx := by
    calc
      (2 / Real.pi) * Real.log (boundaryPoleGap R r) + cPotential -
          globalRadialConstant / boundaryPoleGap R r ≤
        (2 / Real.pi) * Real.log (euclideanRadius qx) + cPotential -
          globalRadialConstant / euclideanRadius qx := by
            have hmain := mul_le_mul_of_nonneg_left hqLog hcoef
            linarith
      _ ≤ planarPotentialKernel qx := hqExpansionLower
  have hsMainUpper :
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (S + r + 2) + cPotential +
          globalRadialConstant / intermediatePoleGap S r := by
    calc
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (euclideanRadius sx) + cPotential +
          globalRadialConstant / euclideanRadius sx := hsExpansionUpper
      _ ≤ (2 / Real.pi) * Real.log (S + r + 2) + cPotential +
          globalRadialConstant / intermediatePoleGap S r := by
            have hmain := mul_le_mul_of_nonneg_left hsLog hcoef
            linarith
  dsimp only [qx, sx] at hqMainLower hsMainUpper ⊢
  unfold greenPoleLower
  rw [Real.log_div hqGap.ne' hsumPos.ne']
  linarith

/-! ## Arbitrary finite-domain comparison -/

/-- **Moving-inner-pole Green comparison for a literal real-radius outer
boundary.**

`D` may be any finite killed domain contained in `coordinateBox M`.  Its
graph outer boundary must lie in the literal boundary of `D(0,R)`.  The
starting point belongs to the two-unit cut at real radius `S`, and both poles
belong to the real radius-`r` disc. -/
theorem infiniteGreen_compare_inner_poles
    (D : Finset Point) (M : ℕ) (R S r : ℝ)
    {start q x y : Point}
    (hr : 0 ≤ r) (hS : r + 2 ≤ S)
    (hscale : S + 2 * r + 2 ≤ R)
    (hstartD : start ∈ D) (hD : D ⊆ coordinateBox M)
    (houter : ∀ w, w ∈ outerBoundary D →
      w ∈ ThickPoint.discBoundary 0 R)
    (hstart : start ∈ thickRealRadialCut S)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    (1 - greenPoleRelativeError R S r) *
        (infiniteGreen D start x).toReal ≤
      (infiniteGreen D start y).toReal ∧
    (infiniteGreen D start y).toReal ≤
      (1 + greenPoleRelativeError R S r) *
        (infiniteGreen D start x).toReal := by
  have hboundaryX : ∀ w, w ∈ outerBoundary D →
      |planarPotentialKernel (w - x) -
        planarPotentialKernel (q - x)| ≤ boundaryPoleError R r := by
    intro w hw
    exact literalBoundary_shifted_potential_oscillation
      hr hS hscale hq hx w (houter w hw)
  have hboundaryY : ∀ w, w ∈ outerBoundary D →
      |planarPotentialKernel (w - y) -
        planarPotentialKernel (q - y)| ≤ boundaryPoleError R r := by
    intro w hw
    exact literalBoundary_shifted_potential_oscillation
      hr hS hscale hq hy w (houter w hw)
  have hpole := abs_potentialReferenceDifference_inner_poles
    hr hS hscale hstart hq hx hy
  have hlowerReference := greenPoleLower_le_potentialReference
    hr hS hscale hstart hq hx
  have hcompare :=
    PoissonKernelGreenPole.infiniteGreen_compare_of_boundaryReferences
      D M hstartD hD
      (boundaryPoleError_nonneg hr hS hscale)
      (boundaryPoleError_nonneg hr hS hscale)
      hboundaryX hboundaryY
      (add_nonneg (outerPoleError_nonneg hr hS hscale)
        (intermediatePoleError_nonneg hr hS))
      hpole hlower hlowerReference
  simpa only [greenPoleRelativeError, greenPoleAdditiveError, two_mul,
    add_assoc, div_eq_mul_inv] using hcompare

end

end Erdos1165.RealPoissonGreenPole

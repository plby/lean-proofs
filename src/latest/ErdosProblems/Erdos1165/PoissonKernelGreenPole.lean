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

import ErdosProblems.Erdos1165.BoundaryStoppedHarnack
import ErdosProblems.Erdos1165.PoissonKernelRadial
import ErdosProblems.Erdos1165.PoissonKernelCutGeometry

/-!
# Moving-pole Harnack comparison for the literal stopped disc

The boundary-reference Green estimate is usually applied with a fixed pole
and two nearby starting points.  Proposition 4.8 also needs the complementary
comparison: the starting point is on an intermediate circle, while the pole
moves in a much smaller inner disc.

The first theorem below is an abstract additive-to-multiplicative comparison.
The rest of the file verifies its hypotheses from the global radial expansion
of the planar potential kernel.  In particular, the final theorem assumes
only Euclidean-radius bounds for the two poles; it has no hypothesis saying
that the two corresponding target events or kernels are equal.
-/

open Real Set
open scoped ENNReal

namespace Erdos1165.PoissonKernelGreenPole

open Annulus AnnulusHarnack GreenProbability PlanarPotential
open PotentialConvergence PotentialEuclideanGeometry PotentialRadialAsymptotic
open PotentialRadialGlobal PoissonKernelRadial
open BoundaryStoppedHarnack RadialHarnackSpecialization
open PoissonKernelCutGeometry

noncomputable section

/-! ## Generic boundary-reference comparison -/

/-- Compare two Green functions with the same starting point and different
poles.  Each Green function is compared to its own potential-kernel boundary
reference.  Thus the statement does not require the two poles, or their hit
events, to be equivalent. -/
theorem infiniteGreen_compare_of_boundaryReferences
    (D : Finset Point) (boxRadius : ℕ) {start x y qx qy : Point}
    (hstart : start ∈ D) (hD : D ⊆ coordinateBox boxRadius)
    {boundaryErrorX boundaryErrorY poleError lower : ℝ}
    (hboundaryErrorX : 0 ≤ boundaryErrorX)
    (hboundaryErrorY : 0 ≤ boundaryErrorY)
    (hboundaryX : ∀ w, w ∈ outerBoundary D →
      |planarPotentialKernel (w - x) -
        planarPotentialKernel (qx - x)| ≤ boundaryErrorX)
    (hboundaryY : ∀ w, w ∈ outerBoundary D →
      |planarPotentialKernel (w - y) -
        planarPotentialKernel (qy - y)| ≤ boundaryErrorY)
    (hpoleError : 0 ≤ poleError)
    (hpole :
      |(planarPotentialKernel (qy - y) -
          planarPotentialKernel (start - y)) -
        (planarPotentialKernel (qx - x) -
          planarPotentialKernel (start - x))| ≤ poleError)
    (hlower : 0 < lower)
    (hlowerReference :
      lower ≤ planarPotentialKernel (qx - x) -
        planarPotentialKernel (start - x) - boundaryErrorX) :
    let error := boundaryErrorX + boundaryErrorY + poleError
    (1 - error / lower) * (infiniteGreen D start x).toReal ≤
        (infiniteGreen D start y).toReal ∧
      (infiniteGreen D start y).toReal ≤
        (1 + error / lower) * (infiniteGreen D start x).toReal := by
  dsimp only
  let gx := (infiniteGreen D start x).toReal
  let gy := (infiniteGreen D start y).toReal
  let rx := planarPotentialKernel (qx - x) -
    planarPotentialKernel (start - x)
  let ry := planarPotentialKernel (qy - y) -
    planarPotentialKernel (start - y)
  have hxApprox :=
    abs_infiniteGreen_toReal_sub_boundaryReference_le_of_subset_coordinateBox
      D boxRadius hstart hD hboundaryErrorX hboundaryX
  have hyApprox :=
    abs_infiniteGreen_toReal_sub_boundaryReference_le_of_subset_coordinateBox
      D boxRadius hstart hD hboundaryErrorY hboundaryY
  have hxBounds : -boundaryErrorX ≤ gx - rx ∧
      gx - rx ≤ boundaryErrorX := by
    simpa only [gx, rx] using (abs_le.mp hxApprox)
  have hyBounds : -boundaryErrorY ≤ gy - ry ∧
      gy - ry ≤ boundaryErrorY := by
    simpa only [gy, ry] using (abs_le.mp hyApprox)
  have hpoleBounds : -poleError ≤ ry - rx ∧
      ry - rx ≤ poleError := by
    simpa only [rx, ry] using (abs_le.mp hpole)
  have hdiff : |gy - gx| ≤
      boundaryErrorX + boundaryErrorY + poleError := by
    rw [abs_le]
    constructor <;> linarith
  have herror : 0 ≤ boundaryErrorX + boundaryErrorY + poleError := by
    linarith
  have hgreenLower : lower ≤ gx := by
    dsimp only [gx, rx] at hxBounds ⊢
    linarith
  exact multiplicative_compare_of_additive herror hlower hgreenLower hdiff

/-! ## Euclidean geometry -/

/-- The deterministic reference point on the positive horizontal axis. -/
def axisReference (R : ℕ) : Point := ((R : ℤ), 0)

private theorem pointComplex_sub (u v : Point) :
    pointComplex (u - v) = pointComplex u - pointComplex v := by
  apply Complex.ext <;> simp [pointComplex]

theorem euclideanRadius_axisReference (R : ℕ) :
    euclideanRadius (axisReference R) = R := by
  rw [euclideanRadius_eq_norm_pointComplex]
  simp [axisReference, pointComplex, Complex.norm_def, Complex.normSq_apply]

/-- Reverse triangle inequality in lattice coordinates. -/
theorem euclideanRadius_sub_lower (u v : Point) :
    euclideanRadius u - euclideanRadius v ≤ euclideanRadius (u - v) := by
  rw [euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex, pointComplex_sub]
  exact le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)

/-- Triangle inequality in lattice coordinates. -/
theorem euclideanRadius_sub_le_add (u v : Point) :
    euclideanRadius (u - v) ≤ euclideanRadius u + euclideanRadius v := by
  rw [euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex, pointComplex_sub]
  exact norm_sub_le _ _

/-- Moving the subtracted point changes the radius by at most the distance
between the two subtracted points. -/
theorem abs_euclideanRadius_sub_sub_le (u x y : Point) :
    |euclideanRadius (u - x) - euclideanRadius (u - y)| ≤
      euclideanRadius (x - y) := by
  rw [euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex,
    pointComplex_sub, pointComplex_sub, pointComplex_sub]
  calc
    |‖pointComplex u - pointComplex x‖ -
        ‖pointComplex u - pointComplex y‖| ≤
      ‖(pointComplex u - pointComplex x) -
        (pointComplex u - pointComplex y)‖ := abs_norm_sub_norm_le _ _
    _ = ‖pointComplex x - pointComplex y‖ := by
      rw [show (pointComplex u - pointComplex x) -
          (pointComplex u - pointComplex y) =
        -(pointComplex x - pointComplex y) by abel, norm_neg]

/-- Two points in the radius-`r` disc are at Euclidean distance at most
`2r`. -/
theorem euclideanRadius_sub_le_two_mul_of_le
    {x y : Point} {r : ℝ}
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    euclideanRadius (x - y) ≤ 2 * r := by
  calc
    euclideanRadius (x - y) ≤
        euclideanRadius x + euclideanRadius y :=
      euclideanRadius_sub_le_add x y
    _ ≤ 2 * r := by linarith

/-! ## Explicit error and lower-bound functions -/

def boundaryPoleGap (R r : ℕ) : ℝ := (R : ℝ) - (r : ℝ) - 1

def outerPoleGap (R r : ℕ) : ℝ := (R : ℝ) - (r : ℝ)

def intermediatePoleGap (S r : ℕ) : ℝ :=
  (S : ℝ) - (r : ℝ) - 1

def boundaryPoleError (R r : ℕ) : ℝ :=
  (2 * globalRadialConstant + (2 * r + 1 : ℕ)) / boundaryPoleGap R r

def outerPoleError (R r : ℕ) : ℝ :=
  (2 * globalRadialConstant + (2 * r : ℕ)) / outerPoleGap R r

def intermediatePoleError (S r : ℕ) : ℝ :=
  (2 * globalRadialConstant + (2 * r : ℕ)) / intermediatePoleGap S r

/-- Total additive Green-function error.  When `S` is a fixed fraction of
`R` and `r = o(R)`, this is explicitly `O((r+1)/(R-r))`. -/
def greenPoleAdditiveError (R S r : ℕ) : ℝ :=
  2 * boundaryPoleError R r + outerPoleError R r +
    intermediatePoleError S r

/-- A single-scale upper envelope for `greenPoleAdditiveError`. -/
def greenPoleScaleError (R r : ℕ) : ℝ :=
  (12 * (2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
    outerPoleGap R r

/-- The explicit radial lower bound for the reference Green value.  Its
main term is `(2/π) log ((R-r)/(S+r))`, i.e. the required positive
`log(R/S)` separation; the remaining terms are the two global radial
remainders and the literal-boundary oscillation. -/
def greenPoleLower (R S r : ℕ) : ℝ :=
  (2 / Real.pi) * Real.log
      (outerPoleGap R r / ((S : ℝ) + (r : ℝ) + 2)) -
    globalRadialConstant / outerPoleGap R r -
    globalRadialConstant / intermediatePoleGap S r -
    boundaryPoleError R r

theorem boundaryPoleGap_pos {R r : ℕ} (h : r + 2 ≤ R) :
    0 < boundaryPoleGap R r := by
  unfold boundaryPoleGap
  have h' : (r : ℝ) + 2 ≤ R := by exact_mod_cast h
  linarith

theorem outerPoleGap_pos {R r : ℕ} (h : r + 1 ≤ R) :
    0 < outerPoleGap R r := by
  unfold outerPoleGap
  have h' : (r : ℝ) + 1 ≤ R := by exact_mod_cast h
  linarith

theorem intermediatePoleGap_pos {S r : ℕ} (h : r + 2 ≤ S) :
    0 < intermediatePoleGap S r := by
  unfold intermediatePoleGap
  have h' : (r : ℝ) + 2 ≤ S := by exact_mod_cast h
  linarith

theorem boundaryPoleError_nonneg {R r : ℕ} (h : r + 2 ≤ R) :
    0 ≤ boundaryPoleError R r := by
  unfold boundaryPoleError
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  exact div_nonneg (by positivity) (boundaryPoleGap_pos h).le

theorem outerPoleError_nonneg {R r : ℕ} (h : r + 1 ≤ R) :
    0 ≤ outerPoleError R r := by
  unfold outerPoleError
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  exact div_nonneg (by positivity) (outerPoleGap_pos h).le

theorem intermediatePoleError_nonneg {S r : ℕ} (h : r + 2 ≤ S) :
    0 ≤ intermediatePoleError S r := by
  unfold intermediatePoleError
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  exact div_nonneg (by positivity) (intermediatePoleGap_pos h).le

/-- If `S` is comparable to `R` and the pole disc is small compared with
`S`, the full additive error has the advertised explicit
`O((r+1)/(R-r))` form. -/
theorem greenPoleAdditiveError_le_scale
    {R S r : ℕ} (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hsmall : 2 * (r + 1) ≤ S) (hbalanced : R ≤ 3 * S) :
    greenPoleAdditiveError R S r ≤ greenPoleScaleError R r := by
  let C := globalRadialConstant
  let K := 2 * C + 3
  let t := (r : ℝ) + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact globalRadialConstant_pos.le
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    linarith
  have hKt0 : 0 ≤ K * t := mul_nonneg hK0 ht0
  have houterPos : 0 < outerPoleGap R r :=
    outerPoleGap_pos (by omega)
  have hboundaryPos : 0 < boundaryPoleGap R r :=
    boundaryPoleGap_pos hR
  have hintermediatePos : 0 < intermediatePoleGap S r :=
    intermediatePoleGap_pos hS
  have houterTwo : 2 ≤ outerPoleGap R r := by
    unfold outerPoleGap
    have hcast : (r : ℝ) + 2 ≤ R := by exact_mod_cast hR
    linarith
  have hboundaryDenom :
      outerPoleGap R r ≤ 2 * boundaryPoleGap R r := by
    unfold outerPoleGap at houterTwo
    unfold outerPoleGap boundaryPoleGap
    linarith
  have hsmallCast : 2 * ((r : ℝ) + 1) ≤ S := by
    exact_mod_cast hsmall
  have hbalancedCast : (R : ℝ) ≤ 3 * S := by
    exact_mod_cast hbalanced
  have hintermediateDenom :
      outerPoleGap R r ≤ 6 * intermediatePoleGap S r := by
    unfold outerPoleGap intermediatePoleGap
    linarith
  have hboundaryNumerator :
      2 * C + (2 * r + 1 : ℕ) ≤ K * t := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp only [K, t]
    nlinarith [mul_nonneg hC hr0]
  have houterNumerator :
      2 * C + (2 * r : ℕ) ≤ K * t := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    dsimp only [K, t]
    nlinarith [mul_nonneg hC hr0]
  have hboundaryError :
      boundaryPoleError R r ≤
        2 * (K * t) / outerPoleGap R r := by
    unfold boundaryPoleError
    apply (div_le_div_iff₀ hboundaryPos houterPos).2
    calc
      (2 * C + ↑(2 * r + 1)) * outerPoleGap R r ≤
          (K * t) * outerPoleGap R r :=
        mul_le_mul_of_nonneg_right hboundaryNumerator houterPos.le
      _ ≤ (K * t) * (2 * boundaryPoleGap R r) :=
        mul_le_mul_of_nonneg_left hboundaryDenom hKt0
      _ = (2 * (K * t)) * boundaryPoleGap R r := by ring
  have houterError :
      outerPoleError R r ≤ (K * t) / outerPoleGap R r := by
    unfold outerPoleError
    exact div_le_div_of_nonneg_right houterNumerator houterPos.le
  have hintermediateError :
      intermediatePoleError S r ≤
        6 * (K * t) / outerPoleGap R r := by
    unfold intermediatePoleError
    apply (div_le_div_iff₀ hintermediatePos houterPos).2
    calc
      (2 * C + ↑(2 * r)) * outerPoleGap R r ≤
          (K * t) * outerPoleGap R r :=
        mul_le_mul_of_nonneg_right houterNumerator houterPos.le
      _ ≤ (K * t) * (6 * intermediatePoleGap S r) :=
        mul_le_mul_of_nonneg_left hintermediateDenom hKt0
      _ = (6 * (K * t)) * intermediatePoleGap S r := by ring
  have hunit : 0 ≤ (K * t) / outerPoleGap R r :=
    div_nonneg hKt0 houterPos.le
  unfold greenPoleAdditiveError greenPoleScaleError
  dsimp only [C, K, t] at *
  calc
    2 * boundaryPoleError R r + outerPoleError R r +
        intermediatePoleError S r ≤
      2 * (2 * ((2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r) +
        ((2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r +
        6 * ((2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r := by linarith
    _ = 11 * (((2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r) := by ring
    _ ≤ (12 * (2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r := by
      rw [show (12 * (2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r =
        12 * (((2 * globalRadialConstant + 3) * ((r : ℝ) + 1)) /
          outerPoleGap R r) by ring]
      linarith

/-! ## Radial verification of the comparison hypotheses -/

private theorem axisReference_sub_inner_bounds
    {R r : ℕ} {x : Point} (hx : euclideanRadius x ≤ r) :
    outerPoleGap R r ≤ euclideanRadius (axisReference R - x) ∧
      euclideanRadius (axisReference R - x) ≤ (R : ℝ) + r := by
  have hlower := euclideanRadius_sub_lower (axisReference R) x
  have hupper := euclideanRadius_sub_le_add (axisReference R) x
  rw [euclideanRadius_axisReference] at hlower hupper
  constructor
  · unfold outerPoleGap
    linarith
  · linarith

private theorem literalBoundary_sub_inner_bounds
    {R r : ℕ} {w x : Point} (hR : 1 ≤ R)
    (hw : w ∈ ThickPoint.discBoundary 0 (R : ℝ))
    (hx : euclideanRadius x ≤ r) :
    boundaryPoleGap R r ≤ euclideanRadius (w - x) ∧
      euclideanRadius (w - x) ≤ (R : ℝ) + r := by
  have hwBounds := discBoundary_zero_euclideanRadius_bounds_nat hR hw
  have hlower := euclideanRadius_sub_lower w x
  have hupper := euclideanRadius_sub_le_add w x
  constructor
  · unfold boundaryPoleGap
    have hcast : (((R - 1 : ℕ) : ℝ)) + 1 = (R : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hR)
    linarith [hwBounds.1]
  · linarith

private theorem thickShell_sub_inner_bounds
    {S r : ℕ} {start x : Point}
    (hstartLower : (S : ℝ) < euclideanRadius start)
    (hstartUpper : euclideanRadius start < (S : ℝ) + 2)
    (hx : euclideanRadius x ≤ r) :
    intermediatePoleGap S r ≤ euclideanRadius (start - x) ∧
      euclideanRadius (start - x) ≤ (S : ℝ) + r + 2 := by
  have hlower := euclideanRadius_sub_lower start x
  have hupper := euclideanRadius_sub_le_add start x
  constructor
  · unfold intermediatePoleGap
    linarith
  · linarith

/-- Uniform potential oscillation on the actual outer boundary after
translation by an arbitrary pole in the radius-`r` inner disc. -/
theorem outerBoundary_shifted_potential_oscillation
    {R r : ℕ} (hR : r + 2 ≤ R) {x : Point}
    (hx : euclideanRadius x ≤ r) :
    ∀ w, w ∈ outerBoundary (boundaryInterior R) →
      |planarPotentialKernel (w - x) -
        planarPotentialKernel (axisReference R - x)| ≤
          boundaryPoleError R r := by
  intro w hw
  have hR1 : 1 ≤ R := by omega
  have hwBoundary := outerBoundary_boundaryInterior_subset_discBoundary R hw
  have hwBounds := literalBoundary_sub_inner_bounds hR1 hwBoundary hx
  have hqBounds := axisReference_sub_inner_bounds (R := R) hx
  have hrho : 0 < boundaryPoleGap R r := boundaryPoleGap_pos hR
  have hw0 : w - x ≠ 0 :=
    (euclideanRadius_pos_iff (w - x)).mp (hrho.trans_le hwBounds.1)
  have hq0 : axisReference R - x ≠ 0 :=
    (euclideanRadius_pos_iff (axisReference R - x)).mp
      (hrho.trans_le (hqBounds.1.trans' (by
        unfold boundaryPoleGap outerPoleGap
        linarith)))
  have hgap :
      |euclideanRadius (w - x) -
        euclideanRadius (axisReference R - x)| ≤ (2 * r + 1 : ℕ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    unfold boundaryPoleGap at hwBounds
    unfold outerPoleGap at hqBounds
    rw [abs_le]
    constructor <;> linarith
  simpa [boundaryPoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := w - x) (y := axisReference R - x)
      hrho hw0 hq0 hwBounds.1
      (by
        unfold boundaryPoleGap outerPoleGap at *
        linarith [hqBounds.1]) hgap)

/-- Moving a pole inside the radius-`r` disc changes the potential at the
fixed outer-axis reference by the explicit wide-shell error. -/
theorem axisReference_potential_oscillation_inner_poles
    {R r : ℕ} (hR : r + 1 ≤ R) {x y : Point}
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |planarPotentialKernel (axisReference R - y) -
      planarPotentialKernel (axisReference R - x)| ≤
        outerPoleError R r := by
  have hxBounds := axisReference_sub_inner_bounds (R := R) hx
  have hyBounds := axisReference_sub_inner_bounds (R := R) hy
  have hrho := outerPoleGap_pos hR
  have hx0 : axisReference R - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hxBounds.1)
  have hy0 : axisReference R - y ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hyBounds.1)
  have hxy : euclideanRadius (x - y) ≤ (2 * r : ℕ) := by
    norm_num
    exact euclideanRadius_sub_le_two_mul_of_le hx hy
  have hgap :
      |euclideanRadius (axisReference R - y) -
        euclideanRadius (axisReference R - x)| ≤ (2 * r : ℕ) :=
    (abs_euclideanRadius_sub_sub_le (axisReference R) y x).trans (by
      simpa only [euclideanRadius_eq_norm_pointComplex, pointComplex_sub,
        norm_sub_rev] using hxy)
  simpa [outerPoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := axisReference R - y) (y := axisReference R - x)
      hrho hy0 hx0 hyBounds.1 hxBounds.1 hgap)

/-- Moving a pole inside the radius-`r` disc changes the potential at a
fixed point on the literal radius-`S` boundary by the corresponding
intermediate-shell error. -/
theorem intermediateBoundary_potential_oscillation_inner_poles
    {S r : ℕ} (hS : r + 2 ≤ S) {start x y : Point}
    (hstartLower : (S : ℝ) < euclideanRadius start)
    (hstartUpper : euclideanRadius start < (S : ℝ) + 2)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |planarPotentialKernel (start - y) -
      planarPotentialKernel (start - x)| ≤
        intermediatePoleError S r := by
  have hxBounds := thickShell_sub_inner_bounds hstartLower hstartUpper hx
  have hyBounds := thickShell_sub_inner_bounds hstartLower hstartUpper hy
  have hrho := intermediatePoleGap_pos hS
  have hx0 : start - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hxBounds.1)
  have hy0 : start - y ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hrho.trans_le hyBounds.1)
  have hxy : euclideanRadius (y - x) ≤ (2 * r : ℕ) := by
    norm_num
    exact euclideanRadius_sub_le_two_mul_of_le hy hx
  have hgap := (abs_euclideanRadius_sub_sub_le start y x).trans hxy
  simpa [intermediatePoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := start - y) (y := start - x)
      hrho hy0 hx0 hyBounds.1 hxBounds.1 hgap)

/-- Additive comparison of the two potential-kernel reference values. -/
theorem abs_potentialReferenceDifference_inner_poles
    {R S r : ℕ} (hR : r + 1 ≤ R) (hS : r + 2 ≤ S)
    {start x y : Point}
    (hstartLower : (S : ℝ) < euclideanRadius start)
    (hstartUpper : euclideanRadius start < (S : ℝ) + 2)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |(planarPotentialKernel (axisReference R - y) -
        planarPotentialKernel (start - y)) -
      (planarPotentialKernel (axisReference R - x) -
        planarPotentialKernel (start - x))| ≤
      outerPoleError R r + intermediatePoleError S r := by
  have houter := axisReference_potential_oscillation_inner_poles hR hx hy
  have hinner :=
    intermediateBoundary_potential_oscillation_inner_poles hS
      hstartLower hstartUpper hx hy
  calc
    |(planarPotentialKernel (axisReference R - y) -
          planarPotentialKernel (start - y)) -
        (planarPotentialKernel (axisReference R - x) -
          planarPotentialKernel (start - x))| =
      |(planarPotentialKernel (axisReference R - y) -
          planarPotentialKernel (axisReference R - x)) -
        (planarPotentialKernel (start - y) -
          planarPotentialKernel (start - x))| := by
            congr 1
            ring
    _ ≤ |planarPotentialKernel (axisReference R - y) -
          planarPotentialKernel (axisReference R - x)| +
        |planarPotentialKernel (start - y) -
          planarPotentialKernel (start - x)| := abs_sub _ _
    _ ≤ outerPoleError R r + intermediatePoleError S r :=
      add_le_add houter hinner

/-- The reference potential difference is bounded below by the explicit
`log((R-r)/(S+r+2))` main term, with the global radial remainders and the
literal-boundary oscillation subtracted. -/
theorem greenPoleLower_le_potentialReference
    {R S r : ℕ} (hR : r + 1 ≤ R) (hS : r + 2 ≤ S)
    {start x : Point}
    (hstartLower : (S : ℝ) < euclideanRadius start)
    (hstartUpper : euclideanRadius start < (S : ℝ) + 2)
    (hx : euclideanRadius x ≤ r) :
    greenPoleLower R S r ≤
      planarPotentialKernel (axisReference R - x) -
        planarPotentialKernel (start - x) - boundaryPoleError R r := by
  let qx := axisReference R - x
  let sx := start - x
  have hqBounds := axisReference_sub_inner_bounds (R := R) hx
  have hsBounds := thickShell_sub_inner_bounds hstartLower hstartUpper hx
  have hqGap : 0 < outerPoleGap R r := outerPoleGap_pos hR
  have hsGap : 0 < intermediatePoleGap S r :=
    intermediatePoleGap_pos hS
  have hqPos : 0 < euclideanRadius qx := by
    exact hqGap.trans_le hqBounds.1
  have hsPos : 0 < euclideanRadius sx := by
    exact hsGap.trans_le hsBounds.1
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
    have := (abs_le.mp hqExpansion).1
    linarith
  have hsExpansionUpper :
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (euclideanRadius sx) + cPotential +
          globalRadialConstant / euclideanRadius sx := by
    have := (abs_le.mp hsExpansion).2
    linarith
  have hC : 0 ≤ globalRadialConstant := globalRadialConstant_pos.le
  have hqRemainder :
      globalRadialConstant / euclideanRadius qx ≤
        globalRadialConstant / outerPoleGap R r :=
    div_le_div_of_nonneg_left hC hqGap hqBounds.1
  have hsRemainder :
      globalRadialConstant / euclideanRadius sx ≤
        globalRadialConstant / intermediatePoleGap S r :=
    div_le_div_of_nonneg_left hC hsGap hsBounds.1
  have hqLog :
      Real.log (outerPoleGap R r) ≤
        Real.log (euclideanRadius qx) :=
    Real.log_le_log hqGap hqBounds.1
  have hsumPos : 0 < (S : ℝ) + (r : ℝ) + 2 := by positivity
  have hsLog :
      Real.log (euclideanRadius sx) ≤
        Real.log ((S : ℝ) + (r : ℝ) + 2) := by
    apply Real.log_le_log hsPos
    exact hsBounds.2
  have hcoef : 0 ≤ (2 : ℝ) / Real.pi := by positivity
  have hqMainLower :
      (2 / Real.pi) * Real.log (outerPoleGap R r) + cPotential -
          globalRadialConstant / outerPoleGap R r ≤
        planarPotentialKernel qx := by
    calc
      (2 / Real.pi) * Real.log (outerPoleGap R r) + cPotential -
          globalRadialConstant / outerPoleGap R r ≤
        (2 / Real.pi) * Real.log (euclideanRadius qx) + cPotential -
          globalRadialConstant / euclideanRadius qx := by
            have := mul_le_mul_of_nonneg_left hqLog hcoef
            linarith
      _ ≤ planarPotentialKernel qx := hqExpansionLower
  have hsMainUpper :
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log ((S : ℝ) + (r : ℝ) + 2) +
          cPotential +
          globalRadialConstant / intermediatePoleGap S r := by
    calc
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (euclideanRadius sx) + cPotential +
          globalRadialConstant / euclideanRadius sx := hsExpansionUpper
      _ ≤ (2 / Real.pi) *
          Real.log ((S : ℝ) + (r : ℝ) + 2) + cPotential +
          globalRadialConstant / intermediatePoleGap S r := by
            have := mul_le_mul_of_nonneg_left hsLog hcoef
            linarith
  dsimp only [qx, sx] at hqMainLower hsMainUpper ⊢
  unfold greenPoleLower
  rw [Real.log_div hqGap.ne' hsumPos.ne']
  linarith

/-! ## Literal cut specialization -/

/-- **Moving-inner-pole Green Harnack inequality on the actual radial cut.**

The start point is an arbitrary member of `thickRadialCut R S`, hence its
radius may be anywhere in `(S,S+2)`.  The two poles are arbitrary points in
the radius-`r` disc.  In particular, there is no target-equivalence
hypothesis.  The multiplicative error is the explicit additive radial error
divided by the positive logarithmic lower bound `greenPoleLower R S r`. -/
theorem infiniteGreen_boundaryInterior_compare_inner_poles
    (R S r : ℕ) {start x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hstart : start ∈ thickRadialCut R S)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    let error := greenPoleAdditiveError R S r / greenPoleLower R S r
    (1 - error) *
        (infiniteGreen (boundaryInterior R) start x).toReal ≤
      (infiniteGreen (boundaryInterior R) start y).toReal ∧
    (infiniteGreen (boundaryInterior R) start y).toReal ≤
      (1 + error) *
        (infiniteGreen (boundaryInterior R) start x).toReal := by
  dsimp only
  have hR : r + 2 ≤ R := by omega
  have hR' : r + 1 ≤ R := by omega
  have hstartData := (mem_thickRadialCut.mp hstart)
  have hstartD : start ∈ boundaryInterior R := hstartData.1
  have hstartLower : (S : ℝ) < euclideanRadius start := hstartData.2.1
  have hstartUpper : euclideanRadius start < (S : ℝ) + 2 :=
    hstartData.2.2
  have hboundaryX := outerBoundary_shifted_potential_oscillation hR hx
  have hboundaryY := outerBoundary_shifted_potential_oscillation hR hy
  have hpole := abs_potentialReferenceDifference_inner_poles
    hR' hS hstartLower hstartUpper hx hy
  have hlowerReference := greenPoleLower_le_potentialReference
    hR' hS hstartLower hstartUpper hx
  have hcompare := infiniteGreen_compare_of_boundaryReferences
    (boundaryInterior R) R hstartD
    (boundaryInterior_subset_coordinateBox R)
    (boundaryPoleError_nonneg hR)
    (boundaryPoleError_nonneg hR)
    hboundaryX hboundaryY
    (add_nonneg (outerPoleError_nonneg hR')
      (intermediatePoleError_nonneg hS))
    hpole hlower hlowerReference
  simpa only [greenPoleAdditiveError, add_assoc, two_mul,
    div_eq_mul_inv] using hcompare

/-- Coarser single-scale form of the preceding theorem.  Its multiplicative
error is literally a fixed explicit constant times
`(r+1)/(R-r)`, divided by `greenPoleLower R S r`. -/
theorem infiniteGreen_boundaryInterior_compare_inner_poles_scale
    (R S r : ℕ) {start x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hsmall : 2 * (r + 1) ≤ S) (hbalanced : R ≤ 3 * S)
    (hstart : start ∈ thickRadialCut R S)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    let error := greenPoleScaleError R r / greenPoleLower R S r
    (1 - error) *
        (infiniteGreen (boundaryInterior R) start x).toReal ≤
      (infiniteGreen (boundaryInterior R) start y).toReal ∧
    (infiniteGreen (boundaryInterior R) start y).toReal ≤
      (1 + error) *
        (infiniteGreen (boundaryInterior R) start x).toReal := by
  dsimp only
  have hbase := infiniteGreen_boundaryInterior_compare_inner_poles
    R S r hS hscale hstart hx hy hlower
  dsimp only at hbase
  have hR : r + 2 ≤ R := by omega
  have herror := greenPoleAdditiveError_le_scale
    hR hS hsmall hbalanced
  have hratio :
      greenPoleAdditiveError R S r / greenPoleLower R S r ≤
        greenPoleScaleError R r / greenPoleLower R S r :=
    div_le_div_of_nonneg_right herror hlower.le
  have hgreen : 0 ≤
      (infiniteGreen (boundaryInterior R) start x).toReal :=
    ENNReal.toReal_nonneg
  constructor
  · calc
      (1 - greenPoleScaleError R r / greenPoleLower R S r) *
          (infiniteGreen (boundaryInterior R) start x).toReal ≤
        (1 - greenPoleAdditiveError R S r / greenPoleLower R S r) *
          (infiniteGreen (boundaryInterior R) start x).toReal :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hratio 1) hgreen
      _ ≤ (infiniteGreen (boundaryInterior R) start y).toReal := hbase.1
  · calc
      (infiniteGreen (boundaryInterior R) start y).toReal ≤
        (1 + greenPoleAdditiveError R S r / greenPoleLower R S r) *
          (infiniteGreen (boundaryInterior R) start x).toReal := hbase.2
      _ ≤ (1 + greenPoleScaleError R r / greenPoleLower R S r) *
          (infiniteGreen (boundaryInterior R) start x).toReal :=
        mul_le_mul_of_nonneg_right
          (by simpa only [add_comm] using add_le_add_left hratio 1) hgreen

end

end Erdos1165.PoissonKernelGreenPole

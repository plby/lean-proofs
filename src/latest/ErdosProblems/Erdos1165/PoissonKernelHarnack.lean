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

import ErdosProblems.Erdos1165.PoissonKernelCutGeometry
import ErdosProblems.Erdos1165.PoissonKernelExitFlux
import ErdosProblems.Erdos1165.PoissonKernelGreenPole
import ErdosProblems.Erdos1165.PoissonKernelLastExit

/-!
# Pointwise Poisson-kernel Harnack on the literal stopped disc

The moving-pole Green estimate is first transferred through a finite radial
cut.  This gives a pointwise comparison at every possible last interior
vertex on the outer side of the cut.  The exit-flux identity then turns that
comparison into the corresponding statement for arbitrary finite sets of
exit locations.
-/

open scoped ENNReal

namespace Erdos1165.PoissonKernelHarnack

open Annulus AnnulusHarnack BoundaryStoppedHarnack GreenProbability
open PotentialEuclideanGeometry PotentialRadialAsymptotic
open PoissonKernelCutGeometry PoissonKernelExitFlux PoissonKernelGreenPole
open PoissonKernelLastExit
open RadialHarnackSpecialization

noncomputable section

/-- The explicit relative error in the moving-pole and Poisson-kernel
comparisons. -/
def poissonKernelRelativeError (R S r : ℕ) : ℝ :=
  greenPoleAdditiveError R S r / greenPoleLower R S r

theorem greenPoleAdditiveError_nonneg
    {R S r : ℕ} (hS : r + 2 ≤ S) (hR : r + 2 ≤ R) :
    0 ≤ greenPoleAdditiveError R S r := by
  unfold greenPoleAdditiveError
  have hb := boundaryPoleError_nonneg hR
  have ho := outerPoleError_nonneg (show r + 1 ≤ R by omega)
  have hi := intermediatePoleError_nonneg hS
  positivity

theorem poissonKernelRelativeError_nonneg
    {R S r : ℕ} (hS : r + 2 ≤ S) (hR : r + 2 ≤ R)
    (hlower : 0 < greenPoleLower R S r) :
    0 ≤ poissonKernelRelativeError R S r := by
  exact div_nonneg (greenPoleAdditiveError_nonneg hS hR) hlower.le

/-- A point whose radius is bounded by the small inner radius is a genuine
interior vertex of the much larger literal stopped disc. -/
theorem mem_boundaryInterior_of_euclideanRadius_le
    {R r : ℕ} (hR : r + 2 ≤ R) {x : Point}
    (hx : euclideanRadius x ≤ r) :
    x ∈ boundaryInterior R := by
  rw [mem_boundaryInterior]
  constructor
  · apply mem_closedDisc_of_euclideanRadius_le
    exact hx.trans (by exact_mod_cast (show r ≤ R by omega))
  · intro hboundary
    have hR1 : 1 ≤ R := by omega
    have hlower :=
      (discBoundary_zero_euclideanRadius_bounds_nat hR1 hboundary).1
    have hcast : (((R - 1 : ℕ) : ℝ)) ≥ (r : ℝ) + 1 := by
      exact_mod_cast (show r + 1 ≤ R - 1 by omega)
    linarith

/-- The cut comparison propagated to an arbitrary outer-side target.

This is the checked pointwise Green theorem used underneath the Poisson
kernel.  The target `a` is completely arbitrary apart from lying beyond the
radial cut; in particular it need not itself be a boundary vertex. -/
theorem infiniteGreen_boundaryInterior_le_of_outer_target
    (R S r : ℕ) {x y a : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (ha : (S : ℝ) + 2 ≤ euclideanRadius a)
    (hlower : 0 < greenPoleLower R S r) :
    infiniteGreen (boundaryInterior R) y a ≤
      ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
        infiniteGreen (boundaryInterior R) x a := by
  let D := boundaryInterior R
  let C := thickRadialCut R S
  let c : ℝ≥0∞ := ENNReal.ofReal (1 + poissonKernelRelativeError R S r)
  have hR : r + 2 ≤ R := by omega
  have hxS : euclideanRadius x ≤ S :=
    hx.trans (by exact_mod_cast (show r ≤ S by omega))
  have hyS : euclideanRadius y ≤ S :=
    hy.trans (by exact_mod_cast (show r ≤ S by omega))
  have hxAvoid : infiniteGreen (D \ C) x a = 0 := by
    simpa only [D, C, cutBoundaryInterior, poissonKernelRelativeError] using
      (infiniteGreen_cutBoundaryInterior_eq_zero (R := R) hxS ha)
  have hyAvoid : infiniteGreen (D \ C) y a = 0 := by
    simpa only [D, C, cutBoundaryInterior, poissonKernelRelativeError] using
      (infiniteGreen_cutBoundaryInterior_eq_zero (R := R) hyS ha)
  have herror0 : 0 ≤ poissonKernelRelativeError R S r :=
    poissonKernelRelativeError_nonneg hS hR hlower
  have hcReal : c.toReal = 1 + poissonKernelRelativeError R S r := by
    simp [c, ENNReal.toReal_ofReal (by linarith :
      0 ≤ 1 + poissonKernelRelativeError R S r)]
  apply infiniteGreen_le_mul_of_cut D C y x a c hyAvoid hxAvoid
  intro z hz
  have hzC : z ∈ thickRadialCut R S := (Finset.mem_inter.mp hz).2
  have hcompare :=
    infiniteGreen_boundaryInterior_compare_inner_poles R S r hS hscale hzC
      hx hy hlower
  have hfiniteY : infiniteGreen D z y ≠ ⊤ :=
    infiniteGreen_ne_top_of_subset_coordinateBox D R z y
      (boundaryInterior_subset_coordinateBox R)
  have hfiniteX : infiniteGreen D z x ≠ ⊤ :=
    infiniteGreen_ne_top_of_subset_coordinateBox D R z x
      (boundaryInterior_subset_coordinateBox R)
  rw [infiniteGreen_symm D y z, infiniteGreen_symm D x z]
  apply (ENNReal.toReal_le_toReal hfiniteY
    (ENNReal.mul_ne_top (by simp [c]) hfiniteX)).mp
  rw [ENNReal.toReal_mul, hcReal]
  exact hcompare.2

/-! ## Poisson kernels and arbitrary continuation weights -/

/-- Sharp pointwise-positive-harmonic comparison for every finite subset of
the literal exit boundary.  No condition is placed on the subset beyond
being made of boundary vertices. -/
theorem exitMass_boundaryInterior_le
    (R S r : ℕ) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hcutOuter : S + 4 ≤ R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    exitMass (boundaryInterior R) B y ≤
      ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
        exitMass (boundaryInterior R) B x := by
  have hR : r + 2 ≤ R := by omega
  have hxD := mem_boundaryInterior_of_euclideanRadius_le hR hx
  have hyD := mem_boundaryInterior_of_euclideanRadius_le hR hy
  apply exitMass_le_of_infiniteGreen_le_on_exitFlux_support
    (boundaryInterior R) B
    (boundaryInterior_disjoint_finset_of_subset_discBoundary R B hB)
    hxD hyD
  intro a ha hflux
  exact infiniteGreen_boundaryInterior_le_of_outer_target R S r hS hscale
    hx hy
    (cutRadius_le_euclideanRadius_of_boundaryInterior_exitFlux_ne_zero
      hcutOuter B hB ha hflux)
    hlower

/-- Two-sided finite-boundary-subset Poisson Harnack comparison. -/
theorem exitMass_boundaryInterior_compare
    (R S r : ℕ) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hcutOuter : S + 4 ≤ R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    exitMass (boundaryInterior R) B y ≤
        ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
          exitMass (boundaryInterior R) B x ∧
      exitMass (boundaryInterior R) B x ≤
        ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
          exitMass (boundaryInterior R) B y := by
  exact ⟨exitMass_boundaryInterior_le R S r B hB hS hscale hcutOuter
      hx hy hlower,
    exitMass_boundaryInterior_le R S r B hB hS hscale hcutOuter
      hy hx hlower⟩

/-- Conventional real `1 ± error` form of the same comparison.  The lower
bound is derived from the reverse upper comparison and the elementary
inequality `(1-error)(1+error) ≤ 1`. -/
theorem exitMass_boundaryInterior_toReal_two_sided
    (R S r : ℕ) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hcutOuter : S + 4 ≤ R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r)
    (herror1 : poissonKernelRelativeError R S r ≤ 1) :
    (1 - poissonKernelRelativeError R S r) *
          (exitMass (boundaryInterior R) B x).toReal ≤
        (exitMass (boundaryInterior R) B y).toReal ∧
      (exitMass (boundaryInterior R) B y).toReal ≤
        (1 + poissonKernelRelativeError R S r) *
          (exitMass (boundaryInterior R) B x).toReal := by
  let e := poissonKernelRelativeError R S r
  have hR : r + 2 ≤ R := by omega
  have he0 : 0 ≤ e := poissonKernelRelativeError_nonneg hS hR hlower
  have hc0 : 0 ≤ 1 + e := by linarith
  have hcompare := exitMass_boundaryInterior_compare R S r B hB hS hscale
    hcutOuter hx hy hlower
  have hfiniteX : exitMass (boundaryInterior R) B x ≠ ⊤ :=
    ne_of_lt ((exitMass_le_one _ _ _).trans_lt ENNReal.one_lt_top)
  have hfiniteY : exitMass (boundaryInterior R) B y ≠ ⊤ :=
    ne_of_lt ((exitMass_le_one _ _ _).trans_lt ENNReal.one_lt_top)
  have hfactorFinite : ENNReal.ofReal
      (1 + poissonKernelRelativeError R S r) ≠ ⊤ := by simp
  have hxy := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfactorFinite hfiniteX) hcompare.1
  have hyx := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfactorFinite hfiniteY) hcompare.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at hxy hyx
  change (1 - e) * (exitMass (boundaryInterior R) B x).toReal ≤
      (exitMass (boundaryInterior R) B y).toReal ∧
    (exitMass (boundaryInterior R) B y).toReal ≤
      (1 + e) * (exitMass (boundaryInterior R) B x).toReal
  constructor
  · have hfactor : (1 - e) * (1 + e) ≤ 1 := by nlinarith
    calc
      (1 - e) * (exitMass (boundaryInterior R) B x).toReal ≤
          (1 - e) * ((1 + e) *
            (exitMass (boundaryInterior R) B y).toReal) := by
        exact mul_le_mul_of_nonneg_left hyx (sub_nonneg.mpr herror1)
      _ = ((1 - e) * (1 + e)) *
          (exitMass (boundaryInterior R) B y).toReal := by ring
      _ ≤ 1 * (exitMass (boundaryInterior R) B y).toReal :=
        mul_le_mul_of_nonneg_right hfactor ENNReal.toReal_nonneg
      _ = _ := one_mul _
  · exact hxy

/-- A finite nonnegative continuation weight integrated against the literal
boundary exit distribution. -/
def weightedBoundaryExitMass
    (R : ℕ) (F : Finset Point) (weight : Point → ℝ≥0∞) (x : Point) : ℝ≥0∞ :=
  ∑ z ∈ F, weight z * exitMass (boundaryInterior R) {z} x

/-- The pointwise comparison survives integration against an arbitrary
nonnegative continuation weight.  This is the form used when the exit point
feeds into unrestricted future stopped data. -/
theorem weightedBoundaryExitMass_le
    (R S r : ℕ) (F : Finset Point) (weight : Point → ℝ≥0∞)
    (hF : ∀ z ∈ F, z ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hcutOuter : S + 4 ≤ R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    weightedBoundaryExitMass R F weight y ≤
      ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
        weightedBoundaryExitMass R F weight x := by
  unfold weightedBoundaryExitMass
  calc
    (∑ z ∈ F, weight z * exitMass (boundaryInterior R) {z} y) ≤
        ∑ z ∈ F, weight z *
          (ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
            exitMass (boundaryInterior R) {z} x) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left
      · apply exitMass_boundaryInterior_le R S r {z}
        · intro b hb
          rw [Finset.mem_singleton.mp hb]
          exact hF z hz
        · exact hS
        · exact hscale
        · exact hcutOuter
        · exact hx
        · exact hy
        · exact hlower
      · exact bot_le
    _ = ∑ z ∈ F,
        ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
          (weight z * exitMass (boundaryInterior R) {z} x) := by
      apply Finset.sum_congr rfl
      intro z hz
      ac_rfl
    _ = ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
        ∑ z ∈ F, weight z * exitMass (boundaryInterior R) {z} x := by
      rw [Finset.mul_sum]

/-- Two-sided arbitrary-weight Poisson Harnack comparison. -/
theorem weightedBoundaryExitMass_compare
    (R S r : ℕ) (F : Finset Point) (weight : Point → ℝ≥0∞)
    (hF : ∀ z ∈ F, z ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {x y : Point}
    (hS : r + 2 ≤ S) (hscale : S + 2 * r + 2 ≤ R)
    (hcutOuter : S + 4 ≤ R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < greenPoleLower R S r) :
    weightedBoundaryExitMass R F weight y ≤
        ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
          weightedBoundaryExitMass R F weight x ∧
      weightedBoundaryExitMass R F weight x ≤
        ENNReal.ofReal (1 + poissonKernelRelativeError R S r) *
          weightedBoundaryExitMass R F weight y := by
  exact ⟨weightedBoundaryExitMass_le R S r F weight hF hS hscale hcutOuter
      hx hy hlower,
    weightedBoundaryExitMass_le R S r F weight hF hS hscale hcutOuter
      hy hx hlower⟩

end

end Erdos1165.PoissonKernelHarnack

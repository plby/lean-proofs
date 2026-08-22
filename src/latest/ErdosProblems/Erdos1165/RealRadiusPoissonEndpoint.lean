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

import ErdosProblems.Erdos1165.RealRadiusPoissonKernel

/-!
# Separated-radius endpoint Harnack for literal real boundaries

This module packages a fixed-endpoint comparison for literal real-radius
boundaries when an intermediate cut is sufficiently separated from both the
starting shell and the outer boundary.  The two stopped paths retain the same
prescribed outer endpoint.  The natural-number box radius used in the
underlying finite-domain proof is only a finiteness witness; no radius in the
stopped events is rounded.

The separation and positive-lower-bound hypotheses are essential.  In
particular, this result is not the consecutive-scale input to Appendix A.6:
at radii whose ratio stays bounded (including the HLOZ ratio `e`), a
fixed-endpoint Poisson kernel has order-one angular variation.  Appendix A.6
instead sums the spatial endpoint and uses an integrated radial row estimate.
-/

open scoped ENNReal
open scoped BigOperators
open MeasureTheory

namespace Erdos1165.RealRadiusPoissonEndpoint

open BoundaryStoppedHarnack MarkedBoundaryVisitKernel
open PotentialEuclideanGeometry RealRadiusPoissonKernel
open TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-- A literal real-radius inner vertex boundary lies inside its defining
disc, so every translated boundary point has Euclidean radius at most the
same real radius. -/
theorem euclideanRadius_sub_center_le_of_mem_discBoundary
    {center u : Point} {r : ℝ}
    (hu : u ∈ ThickPoint.discBoundary center r) :
    euclideanRadius (u - center) ≤ r := by
  have hu0 : u - center ∈ ThickPoint.discBoundary 0 r :=
    (mem_discBoundary_translate center r u).mp hu
  exact (discBoundary_zero_euclideanRadius_bounds_real hu0).2

/-- Fixed-endpoint `1 ± error` comparison for two starts on a literal
real-radius inner boundary and a common endpoint on a literal real-radius
outer boundary, under the stated separated-cut and positive-lower-bound
hypotheses.  This generic result is intended for separated-radius consumers,
not consecutive-scale Appendix-A.6 transitions. -/
theorem fairSteps_boundaryExitEndpointSteps_annular_toReal_two_sided
    (R S inner : ℝ) (center : Point)
    {u v exit : Point}
    (hinner0 : 0 ≤ inner) (hR : inner + 2 ≤ R)
    (hS : inner + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hu : u ∈ ThickPoint.discBoundary center inner)
    (hv : v ∈ ThickPoint.discBoundary center inner)
    (hexit : exit ∈ ThickPoint.discBoundary center R)
    (hlower : 0 < realGreenPoleLower R S inner)
    (herror1 : realPoissonKernelRelativeError R S inner ≤ 1) :
    (1 - realPoissonKernelRelativeError R S inner) *
          (fairSteps (boundaryExitEndpointSteps
            (ThickPoint.discBoundary center R) u exit)).toReal ≤
        (fairSteps (boundaryExitEndpointSteps
          (ThickPoint.discBoundary center R) v exit)).toReal ∧
      (fairSteps (boundaryExitEndpointSteps
          (ThickPoint.discBoundary center R) v exit)).toReal ≤
        (1 + realPoissonKernelRelativeError R S inner) *
          (fairSteps (boundaryExitEndpointSteps
            (ThickPoint.discBoundary center R) u exit)).toReal := by
  have huRadius := euclideanRadius_sub_center_le_of_mem_discBoundary hu
  have hvRadius := euclideanRadius_sub_center_le_of_mem_discBoundary hv
  have hcompare := skeletonExitKernel_centered_literalRealDisc_toReal_two_sided
    R S inner center hinner0 hR hS hcutOuter
      hexit huRadius hvRadius hlower herror1
  simpa only [← terminalSkeletonKernel_eq_skeletonExitKernel,
    terminalSkeletonKernel] using hcompare

/-! ## Arbitrary continuation weights -/

/-- A finite continuation weight integrated against the literal real-radius
exit distribution.  This is the real-radius counterpart of
`PoissonKernelHarnack.weightedBoundaryExitMass`. -/
def weightedBoundaryExitMass
    (R : ℝ) (center : Point) (F : Finset Point)
    (weight : Point → ℝ≥0∞) (start : Point) : ℝ≥0∞ :=
  ∑ exit ∈ F, weight exit *
    skeletonExitKernel (ThickPoint.discBoundary center R) start exit

/-- Separated-radius endpoint Harnack remains valid after integration
against an arbitrary nonnegative continuation weight. -/
theorem weightedBoundaryExitMass_le
    (R S inner : ℝ) (center : Point) (F : Finset Point)
    (weight : Point → ℝ≥0∞)
    (hF : ∀ exit ∈ F, exit ∈ ThickPoint.discBoundary center R)
    {u v : Point}
    (hinner0 : 0 ≤ inner) (hR : inner + 2 ≤ R)
    (hS : inner + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hu : u ∈ ThickPoint.discBoundary center inner)
    (hv : v ∈ ThickPoint.discBoundary center inner)
    (hlower : 0 < realGreenPoleLower R S inner)
    (herror1 : realPoissonKernelRelativeError R S inner ≤ 1) :
    weightedBoundaryExitMass R center F weight v ≤
      ENNReal.ofReal (1 + realPoissonKernelRelativeError R S inner) *
        weightedBoundaryExitMass R center F weight u := by
  let error := realPoissonKernelRelativeError R S inner
  have herror0 : 0 ≤ error :=
    realPoissonKernelRelativeError_nonneg hinner0 hR hS hlower
  have hfactor0 : 0 ≤ 1 + error := by linarith
  have hpoint (exit : Point) (hexit : exit ∈ F) :
      skeletonExitKernel (ThickPoint.discBoundary center R) v exit ≤
        ENNReal.ofReal (1 + error) *
          skeletonExitKernel (ThickPoint.discBoundary center R) u exit := by
    have hreal :=
      (fairSteps_boundaryExitEndpointSteps_annular_toReal_two_sided
        R S inner center hinner0 hR hS hcutOuter hu hv (hF exit hexit)
          hlower herror1).2
    have hleftFinite :
        skeletonExitKernel (ThickPoint.discBoundary center R) v exit ≠ ∞ :=
      measure_ne_top fairSteps _
    have hrightFinite :
        ENNReal.ofReal (1 + error) *
            skeletonExitKernel (ThickPoint.discBoundary center R) u exit ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top fairSteps _)
    apply (ENNReal.toReal_le_toReal hleftFinite hrightFinite).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfactor0]
    simpa only [← terminalSkeletonKernel_eq_skeletonExitKernel,
      terminalSkeletonKernel, error] using hreal
  unfold weightedBoundaryExitMass
  calc
    (∑ exit ∈ F, weight exit *
        skeletonExitKernel (ThickPoint.discBoundary center R) v exit) ≤
        ∑ exit ∈ F, weight exit *
          (ENNReal.ofReal (1 + error) *
            skeletonExitKernel (ThickPoint.discBoundary center R) u exit) := by
      exact Finset.sum_le_sum fun exit hexit ↦ by
        gcongr
        exact hpoint exit hexit
    _ = ENNReal.ofReal (1 + error) *
        ∑ exit ∈ F, weight exit *
          skeletonExitKernel (ThickPoint.discBoundary center R) u exit := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro exit _
      ac_rfl

/-- Two-sided arbitrary-continuation comparison. -/
theorem weightedBoundaryExitMass_compare
    (R S inner : ℝ) (center : Point) (F : Finset Point)
    (weight : Point → ℝ≥0∞)
    (hF : ∀ exit ∈ F, exit ∈ ThickPoint.discBoundary center R)
    {u v : Point}
    (hinner0 : 0 ≤ inner) (hR : inner + 2 ≤ R)
    (hS : inner + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hu : u ∈ ThickPoint.discBoundary center inner)
    (hv : v ∈ ThickPoint.discBoundary center inner)
    (hlower : 0 < realGreenPoleLower R S inner)
    (herror1 : realPoissonKernelRelativeError R S inner ≤ 1) :
    weightedBoundaryExitMass R center F weight v ≤
        ENNReal.ofReal (1 + realPoissonKernelRelativeError R S inner) *
          weightedBoundaryExitMass R center F weight u ∧
      weightedBoundaryExitMass R center F weight u ≤
        ENNReal.ofReal (1 + realPoissonKernelRelativeError R S inner) *
          weightedBoundaryExitMass R center F weight v := by
  exact ⟨weightedBoundaryExitMass_le R S inner center F weight hF
      hinner0 hR hS hcutOuter hu hv hlower herror1,
    weightedBoundaryExitMass_le R S inner center F weight hF
      hinner0 hR hS hcutOuter hv hu hlower herror1⟩

end

end Erdos1165.RealRadiusPoissonEndpoint

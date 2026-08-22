/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AnnularOffspringKernelRadialExit

/-!
# The endpoint-integrated literal profile offspring law

This module packages the exact real-radius row estimate, recurrence identity,
and strong-Markov renewal equation into the interfaces consumed by the
geometric/negative-binomial offspring algebra.
-/

open scoped BigOperators

namespace Erdos1165.AnnularOffspringKernelRadialProfile

open AnnularOffspringKernel AnnularOffspringKernelRadial
open AnnularOffspringKernelRadialExit AnnularProfileClocks
open AppendixFirstMoment
open LiteralRealAnnulusRadialExit ThickPoint

noncomputable section

/-- The explicit radial error for the actual three profile radii. -/
def profileAnnularRowError (n k : ℕ) : ℝ :=
  literalRealAnnulusRowError
    (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))

/-- The exact literal profile cycle satisfies the abstract integrated
half-row interface. -/
theorem profileAnnularCycleKernelReal_halfRowComparison
    {n k : ℕ} {center : Point} {boxRadius : ℕ}
    (hrInner : 2 < scaleRadius n (k + 1))
    (hrMiddle : 2 < scaleRadius n k)
    (hrOuter : 2 < scaleRadius n (k - 1))
    (hOuterBox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ))
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (hmiddle : (profileInnerBoundary n k center).Nonempty)
    (hdelta : 0 <
      realBoundaryPotentialValue (scaleRadius n (k - 1)) -
        realBoundaryPotentialValue (scaleRadius n (k + 1)))
    (hmidpoint :
      2 * realBoundaryPotentialValue (scaleRadius n k) =
        realBoundaryPotentialValue (scaleRadius n (k + 1)) +
          realBoundaryPotentialValue (scaleRadius n (k - 1))) :
    HalfRowComparison (profileAnnularRowError n k)
      (profileAnnularCycleKernelReal n k center) := by
  intro u
  exact sum_profileAnnularCycleKernelReal_half_bounds_of_radial_midpoint
    hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep hmiddle
      hdelta hmidpoint u

/-- One literal profile gap has the geometric offspring law up to the
explicit real-radius row error.  All spatial exit endpoints are integrated;
no fixed-endpoint comparison is used. -/
theorem profileIntegratedMarkedOffspringKernel_two_sided
    {n k : ℕ} {center : Point} {boxRadius q : ℕ}
    (hrInner : 2 < scaleRadius n (k + 1))
    (hrMiddle : 2 < scaleRadius n k)
    (hrOuter : 2 < scaleRadius n (k - 1))
    (hOuterBox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ))
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (hmiddle : (profileInnerBoundary n k center).Nonempty)
    (houter : (profileOuterBoundary n k center).Nonempty)
    (hdelta : 0 <
      realBoundaryPotentialValue (scaleRadius n (k - 1)) -
        realBoundaryPotentialValue (scaleRadius n (k + 1)))
    (hmidpoint :
      2 * realBoundaryPotentialValue (scaleRadius n k) =
        realBoundaryPotentialValue (scaleRadius n (k + 1)) +
          realBoundaryPotentialValue (scaleRadius n (k - 1)))
    (herror1 : profileAnnularRowError n k ≤ 1)
    (u : ProfileCycleMiddlePoint n k center) :
    (1 - profileAnnularRowError n k) ^ (q + 1) * halfGeometricMass q ≤
        integratedMarkedOffspringKernel
          (profileAnnularCycleKernelReal n k center)
          (profileAnnularEscapeRowReal n k center) q u ∧
      integratedMarkedOffspringKernel
          (profileAnnularCycleKernelReal n k center)
          (profileAnnularEscapeRowReal n k center) q u ≤
        (1 + profileAnnularRowError n k) ^ (q + 1) * halfGeometricMass q := by
  have herror0 : 0 ≤ profileAnnularRowError n k := by
    unfold profileAnnularRowError
    exact literalRealAnnulusRowError_nonneg
      (rInner := scaleRadius n (k + 1))
      (rMiddle := scaleRadius n k)
      (rOuter := scaleRadius n (k - 1))
      (by linarith) (by linarith) hdelta
  apply integratedMarkedOffspringKernel_two_sided
    herror0 herror1
  · exact fun a b ↦ annularCycleKernelReal_nonneg
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center)
      (fun v : ProfileCycleMiddlePoint n k center ↦ v.1)
      (fun z : ProfileCycleInnerPoint n k center ↦ z.1) a b
  · exact profileAnnularCycle_escape_isStochasticRenewalRow
      houter (by linarith) hOuterSep
  · exact profileAnnularCycleKernelReal_halfRowComparison
      hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep hmiddle
        hdelta hmidpoint

end

end Erdos1165.AnnularOffspringKernelRadialProfile

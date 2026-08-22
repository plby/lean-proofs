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

import ErdosProblems.Erdos1165.ProfileAnnularRowRegular

/-!
# Literal profile-gap offspring kernel

This module is the final path-to-algebra adapter for one nonterminal profile
gap.  It identifies the probability of the literal completed-excursion count
event with the endpoint-integrated renewal kernel, then transfers the radial
half-row estimate to that event-defined probability.
-/

open Filter Set

namespace Erdos1165.AnnularOffspringKernelLiteralProfile

open AnnularOffspringKernel AnnularOffspringKernelRadial
open AnnularOffspringKernelRadialExit AnnularOffspringRenewal
open AppendixFirstMoment
open AnnularProfileClocks RealDiscFinite ThickPoint
open ProfileAnnularRowRegular

noncomputable section

/-- The final no-further-inner-excursion kernel with its exact outer endpoint
retained. -/
noncomputable def profileAnnularEscapeKernelReal
    (n k : ℕ) (center : Point) :
    ProfileCycleMiddlePoint n k center → ProfileCycleOuterPoint n k center → ℝ :=
  annularEscapeKernelReal
    (profileOuterBoundary n k center)
    (profileInnerBoundary n (k + 1) center)
    (fun v : ProfileCycleMiddlePoint n k center ↦ v.1)
    (fun w : ProfileCycleOuterPoint n k center ↦ w.1)

/-- Endpoint-retaining form of the exact literal identification.  The count
`q`, entrance `u`, and outer exit endpoint `w` are all kept in the joint
kernel. -/
theorem literalProfileGapMarkedKernel_toReal_eq
    {n k q : ℕ} {center : Point}
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    (literalGapMarkedKernel
        (profileOuterBoundary n k center)
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) u.1 q w.1).toReal =
      markedOffspringKernel
        (profileAnnularCycleKernelReal n k center)
        (profileAnnularEscapeKernelReal n k center) q u w := by
  unfold literalGapMarkedKernel profileAnnularCycleKernelReal
    profileAnnularEscapeKernelReal
  apply boundaryExcursionExitKernel_toReal_eq_markedOffspringKernel
  · exact enumeratesBoundary_boundaryFinsetPoint center (scaleRadius n k)
  · exact enumeratesBoundary_boundaryFinsetPoint center (scaleRadius n (k + 1))
  · exact enumeratesBoundary_boundaryFinsetPoint center (scaleRadius n (k - 1))
  · exact (discBoundaries_disjoint_of_separated center hInnerSep).symm
  · apply discBoundaries_disjoint_of_separated
    linarith
  · exact discBoundaries_disjoint_of_separated center hOuterSep
  · intro z
    exact FirstHitSeparates.discBoundaries
      (mem_discBoundaryFinset.mp z.2) (by linarith) hOuterSep

/-- For the three actual profile boundaries, the literal exact-count event
has precisely the mass of the integrated cycle/escape renewal iterate. -/
theorem literalProfileGapIntegratedMarkedKernel_toReal_eq
    {n k q : ℕ} {center : Point}
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (u : ProfileCycleMiddlePoint n k center) :
    (literalGapIntegratedMarkedKernel
        (profileOuterBoundary n k center)
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) u.1 q).toReal =
      integratedMarkedOffspringKernel
        (profileAnnularCycleKernelReal n k center)
        (profileAnnularEscapeRowReal n k center) q u := by
  unfold profileAnnularCycleKernelReal profileAnnularEscapeRowReal
  apply literalGapIntegratedMarkedKernel_toReal_eq_integratedMarkedOffspringKernel
  · exact enumeratesBoundary_boundaryFinsetPoint center (scaleRadius n k)
  · exact enumeratesBoundary_boundaryFinsetPoint center (scaleRadius n (k + 1))
  · exact enumeratesBoundary_boundaryFinsetPoint center (scaleRadius n (k - 1))
  · exact (discBoundaries_disjoint_of_separated center hInnerSep).symm
  · apply discBoundaries_disjoint_of_separated
    linarith
  · exact discBoundaries_disjoint_of_separated center hOuterSep
  · intro z
    exact FirstHitSeparates.discBoundaries
      (mem_discBoundaryFinset.mp z.2) (by linarith) hOuterSep

/-- The regular-level radial comparison, stated directly for the probability
of the literal exact-count event.  Intermediate and outer spatial endpoints
are integrated; the entrance point and offspring count remain fixed. -/
theorem literalProfileGapIntegratedMarkedKernel_two_sided_regularLevel
    {n k q : ℕ} {center : Point} {boxRadius : ℕ}
    (hn : 0 < n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (hrInner : 2 < scaleRadius n (k + 1))
    (hrMiddle : 2 < scaleRadius n k)
    (hrOuter : 2 < scaleRadius n (k - 1))
    (hOuterBox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ))
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (hmiddle : (profileInnerBoundary n k center).Nonempty)
    (houter : (profileOuterBoundary n k center).Nonempty)
    (herror1 : LiteralRealAnnulusRadialExit.literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k)
        (scaleRadius n (k - 1)) ≤ 1)
    (u : ProfileCycleMiddlePoint n k center) :
    let rowError := LiteralRealAnnulusRadialExit.literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    (1 - rowError) ^ (q + 1) * halfGeometricMass q ≤
        (literalGapIntegratedMarkedKernel
          (profileOuterBoundary n k center)
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) u.1 q).toReal ∧
      (literalGapIntegratedMarkedKernel
          (profileOuterBoundary n k center)
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) u.1 q).toReal ≤
        (1 + rowError) ^ (q + 1) * halfGeometricMass q := by
  dsimp only
  rw [literalProfileGapIntegratedMarkedKernel_toReal_eq hInnerSep hOuterSep u]
  exact integratedMarkedOffspringKernel_profile_two_sided_regularLevel
    hn hk hkn hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep
      hmiddle houter herror1 u

/-- Fully automatic literal one-gap comparison at every nonterminal regular
level, eventually in the HLOZ scale.  This is the walk-facing form: its
middle term is the probability of the exact completed-excursion-count event,
not an abstract renewal kernel. -/
theorem eventually_literalProfileGapIntegratedMarkedKernel_two_sided_regular :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (q : ℕ) (center : Point) (u : ProfileCycleMiddlePoint n k center),
        let rowError := LiteralRealAnnulusRadialExit.literalRealAnnulusRowError
          (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
        (1 - rowError) ^ (q + 1) * halfGeometricMass q ≤
            (literalGapIntegratedMarkedKernel
              (profileOuterBoundary n k center)
              (profileInnerBoundary n k center)
              (profileInnerBoundary n (k + 1) center) u.1 q).toReal ∧
          (literalGapIntegratedMarkedKernel
              (profileOuterBoundary n k center)
              (profileInnerBoundary n k center)
              (profileInnerBoundary n (k + 1) center) u.1 q).toReal ≤
            (1 + rowError) ^ (q + 1) * halfGeometricMass q := by
  filter_upwards
    [eventually_integratedMarkedOffspringKernel_profile_two_sided_regular,
      eventually_ge_atTop 2] with n hbound hn
  intro k hk0 hk q center u
  obtain ⟨_hinner, _hmiddle, _houter, hInnerSep, hOuterSep,
      _hdelta, _hmidpoint⟩ := profile_regular_geometry hn hk0 hk
  dsimp only
  rw [literalProfileGapIntegratedMarkedKernel_toReal_eq
    hInnerSep hOuterSep u]
  exact hbound k hk0 hk q center u

end

end Erdos1165.AnnularOffspringKernelLiteralProfile

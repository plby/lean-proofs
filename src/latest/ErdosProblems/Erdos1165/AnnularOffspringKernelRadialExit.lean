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

import ErdosProblems.Erdos1165.AnnularOffspringKernelRadial
import ErdosProblems.Erdos1165.LiteralRealAnnulusRadialExit

/-!
# Endpoint-integrated radial offspring row

This file connects the exact middle-to-inner-to-middle cycle kernel with the
radial exit probability of the literal real annulus.  All three stopped
boundaries remain the exact `discBoundary 0 r`; the finite graph annulus is
used only to evaluate the resulting row probability.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularOffspringKernelRadialExit

open Annulus AnnulusHarnack AnnularOffspringKernel
open AnnularOffspringKernelRadial
open AnnularProfileClocks
open AppendixFirstMoment
open LiteralRealAnnulus LiteralRealAnnulusRadialExit
open MarkedBoundaryVisitKernel RealDiscFinite ThickPoint

noncomputable section

/-- The exact cycle row is the inner-side exit probability of the finite
literal annulus. -/
theorem sum_annularCycleKernelReal_eq_literalRealAnnulusInnerExit
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ}
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    (hmiddleNonempty : (discBoundary 0 rMiddle).Nonempty)
    (u : DiscBoundaryPoint 0 rMiddle) :
    (∑ v : DiscBoundaryPoint 0 rMiddle,
      annularCycleKernelReal
        (discBoundary 0 rOuter) (discBoundary 0 rMiddle)
        (discBoundary 0 rInner)
        (fun y : DiscBoundaryPoint 0 rMiddle ↦ y.1)
        (fun z : DiscBoundaryPoint 0 rInner ↦ z.1) u v) =
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) u.1).toReal := by
  let outer := discBoundary 0 rOuter
  let middle := discBoundary 0 rMiddle
  let inner := discBoundary 0 rInner
  let D := literalRealAnnulus rInner rOuter boxRadius
  let B := discBoundaryFinset 0 rInner
  have hreturn (z : DiscBoundaryPoint 0 rInner) :
      ∑ v : DiscBoundaryPoint 0 rMiddle,
        (skeletonExitKernel middle z.1 v.1).toReal = 1 := by
    calc
      (∑ v : DiscBoundaryPoint 0 rMiddle,
          (skeletonExitKernel middle z.1 v.1).toReal) =
          ∑ y ∈ (finite_discBoundary 0 rMiddle).toFinset,
            (skeletonExitKernel middle z.1 y).toReal := by
        symm
        exact Finset.sum_subtype
          (finite_discBoundary 0 rMiddle).toFinset
          (fun y ↦ by simp)
          (fun y ↦ (skeletonExitKernel middle z.1 y).toReal)
      _ = 1 := sum_skeletonExitKernel_toReal_eq_one
        (finite_discBoundary 0 rMiddle) hmiddleNonempty z.1
  have hcycle := sum_annularCycleKernelReal_eq_of_return_rows
    outer middle inner
    (fun y : DiscBoundaryPoint 0 rMiddle ↦ y.1)
    (fun z : DiscBoundaryPoint 0 rInner ↦ z.1)
    hreturn u
  rw [hcycle]
  calc
    (∑ z : DiscBoundaryPoint 0 rInner,
        (skeletonExitKernel (inner ∪ outer) u.1 z.1).toReal) =
        ∑ z ∈ B,
          (skeletonExitKernel (inner ∪ outer) u.1 z).toReal := by
      symm
      exact Finset.sum_subtype B
        (fun z ↦ by simp [B])
        (fun z ↦ (skeletonExitKernel (inner ∪ outer) u.1 z).toReal)
    _ = (exitMass D B u.1).toReal := by
      apply sum_skeletonExitKernel_finset_toReal_eq_exitMass
      · exact mem_literalRealAnnulus_of_mem_intermediate_discBoundary
          hrOuter hOuterBox hInnerSep hOuterSep u.2
      · intro z hz
        have hzUnion : z ∈
            literalRealAnnulusInnerExit rInner rOuter boxRadius ∪
              literalRealAnnulusOuterExit rInner rOuter boxRadius := by
          rw [literalRealAnnulus_exit_union]
          exact hz
        rcases Finset.mem_union.mp hzUnion with hzInner | hzOuterExit
        · exact Or.inl (literalRealAnnulusInnerExit_subset_discBoundary hzInner)
        · exact Or.inr (literalRealAnnulusOuterExit_subset_discBoundary
            hrOuter hOuterBox hzOuterExit)
      · intro z hzD hzBoundary
        rcases hzBoundary with hzInner | hzOuterBoundary
        · exact (mem_literalRealAnnulus_raw.mp hzD).2.2.2 hzInner.1
        · exact (mem_literalRealAnnulus_raw.mp hzD).2.2.1 hzOuterBoundary
      · rw [Finset.disjoint_left]
        intro z hzD hzB
        exact (mem_literalRealAnnulus_raw.mp hzD).2.2.2
          (mem_discBoundaryFinset.mp hzB).1
    _ = (exitMass D
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) u.1).toReal := by
      rw [exitMass_discBoundaryFinset_eq_literalRealAnnulusInnerExit
        (mem_literalRealAnnulus_of_mem_intermediate_discBoundary
          hrOuter hOuterBox hInnerSep hOuterSep u.2)]

/-- Combining the exact row bridge with the radial potential estimate gives
the genuine `1/2 ± error` cycle-row comparison. -/
theorem sum_annularCycleKernelReal_half_bounds_of_midpoint
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ}
    (hrInner : 2 < rInner) (hrMiddle : 2 < rMiddle)
    (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    (hmiddleNonempty : (discBoundary 0 rMiddle).Nonempty)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner)
    (hmidpoint : 2 * realBoundaryPotentialValue rMiddle =
      realBoundaryPotentialValue rInner +
        realBoundaryPotentialValue rOuter)
    (u : DiscBoundaryPoint 0 rMiddle) :
    let rowError := literalRealAnnulusRowError rInner rMiddle rOuter
    (1 - rowError) / 2 ≤
      ∑ v : DiscBoundaryPoint 0 rMiddle,
        annularCycleKernelReal
          (discBoundary 0 rOuter) (discBoundary 0 rMiddle)
          (discBoundary 0 rInner)
          (fun y : DiscBoundaryPoint 0 rMiddle ↦ y.1)
          (fun z : DiscBoundaryPoint 0 rInner ↦ z.1) u v ∧
    (∑ v : DiscBoundaryPoint 0 rMiddle,
        annularCycleKernelReal
          (discBoundary 0 rOuter) (discBoundary 0 rMiddle)
          (discBoundary 0 rInner)
          (fun y : DiscBoundaryPoint 0 rMiddle ↦ y.1)
          (fun z : DiscBoundaryPoint 0 rInner ↦ z.1) u v) ≤
      (1 + rowError) / 2 := by
  dsimp only
  rw [sum_annularCycleKernelReal_eq_literalRealAnnulusInnerExit
    (by linarith : 0 ≤ rOuter) hOuterBox hInnerSep hOuterSep
      hmiddleNonempty u]
  exact literalRealAnnulusInnerExit_half_bounds_of_midpoint
    hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep u.2
    hdelta hmidpoint

/-- The centered exact-inner-boundary sum (using the canonical boundary
finset subtype) is the same literal-annulus exit mass.  This is the form
produced after translating a profile row to center zero. -/
theorem sum_skeletonExitKernel_literalInnerBoundary_eq_exitMass
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ}
    (hrOuter : 0 ≤ rOuter) (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    (u : LiteralMiddlePoint rMiddle) :
    (∑ z : LiteralMiddlePoint rInner,
      (skeletonExitKernel
        (discBoundary 0 rInner ∪ discBoundary 0 rOuter) u.1 z.1).toReal) =
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) u.1).toReal := by
  let D := literalRealAnnulus rInner rOuter boxRadius
  let B := discBoundaryFinset 0 rInner
  have huBoundary : u.1 ∈ discBoundary 0 rMiddle := by
    exact mem_discBoundaryFinset.mp u.2
  have huD := mem_literalRealAnnulus_of_mem_intermediate_discBoundary
    hrOuter hOuterBox hInnerSep hOuterSep huBoundary
  calc
    (∑ z : LiteralMiddlePoint rInner,
        (skeletonExitKernel
          (discBoundary 0 rInner ∪ discBoundary 0 rOuter) u.1 z.1).toReal) =
        ∑ z ∈ B,
          (skeletonExitKernel
            (discBoundary 0 rInner ∪ discBoundary 0 rOuter) u.1 z).toReal := by
      rw [show (Finset.univ : Finset (LiteralMiddlePoint rInner)) = B.attach by
        ext z
        simp [B]]
      exact Finset.sum_attach B
        (fun z ↦ (skeletonExitKernel
          (discBoundary 0 rInner ∪ discBoundary 0 rOuter) u.1 z).toReal)
    _ = (exitMass D B u.1).toReal := by
      apply sum_skeletonExitKernel_finset_toReal_eq_exitMass
      · exact huD
      · intro z hz
        have hzUnion : z ∈
            literalRealAnnulusInnerExit rInner rOuter boxRadius ∪
              literalRealAnnulusOuterExit rInner rOuter boxRadius := by
          rw [literalRealAnnulus_exit_union]
          exact hz
        rcases Finset.mem_union.mp hzUnion with hzInner | hzOuterExit
        · exact Or.inl (literalRealAnnulusInnerExit_subset_discBoundary hzInner)
        · exact Or.inr (literalRealAnnulusOuterExit_subset_discBoundary
            hrOuter hOuterBox hzOuterExit)
      · intro z hzD hzBoundary
        rcases hzBoundary with hzInner | hzOuterBoundary
        · exact (mem_literalRealAnnulus_raw.mp hzD).2.2.2 hzInner.1
        · exact (mem_literalRealAnnulus_raw.mp hzD).2.2.1 hzOuterBoundary
      · rw [Finset.disjoint_left]
        intro z hzD hzB
        exact (mem_literalRealAnnulus_raw.mp hzD).2.2.2
          (mem_discBoundaryFinset.mp hzB).1
    _ = _ := by
      rw [exitMass_discBoundaryFinset_eq_literalRealAnnulusInnerExit huD]

/-- Radial half bounds for the centered exact-boundary sum returned by the
profile-center translation theorem. -/
theorem sum_skeletonExitKernel_literalInnerBoundary_half_bounds_of_midpoint
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ}
    (hrInner : 2 < rInner) (hrMiddle : 2 < rMiddle)
    (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner)
    (hmidpoint : 2 * realBoundaryPotentialValue rMiddle =
      realBoundaryPotentialValue rInner +
        realBoundaryPotentialValue rOuter)
    (u : LiteralMiddlePoint rMiddle) :
    let rowError := literalRealAnnulusRowError rInner rMiddle rOuter
    (1 - rowError) / 2 ≤
      ∑ z : LiteralMiddlePoint rInner,
        (skeletonExitKernel
          (discBoundary 0 rInner ∪ discBoundary 0 rOuter) u.1 z.1).toReal ∧
    (∑ z : LiteralMiddlePoint rInner,
        (skeletonExitKernel
          (discBoundary 0 rInner ∪ discBoundary 0 rOuter) u.1 z.1).toReal) ≤
      (1 + rowError) / 2 := by
  dsimp only
  rw [sum_skeletonExitKernel_literalInnerBoundary_eq_exitMass
    (by linarith : 0 ≤ rOuter) hOuterBox hInnerSep hOuterSep u]
  exact literalRealAnnulusInnerExit_half_bounds_of_midpoint
    hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep
    (mem_discBoundaryFinset.mp u.2) hdelta hmidpoint

/-- Arbitrary-center HLOZ profile-cycle row, reduced by translation to the
centered literal real-annulus estimate. -/
theorem sum_profileAnnularCycleKernelReal_half_bounds_of_radial_midpoint
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
          realBoundaryPotentialValue (scaleRadius n (k - 1)))
    (u : ProfileCycleMiddlePoint n k center) :
    let rowError := literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    (1 - rowError) / 2 ≤
      ∑ v : ProfileCycleMiddlePoint n k center,
        profileAnnularCycleKernelReal n k center u v ∧
    (∑ v : ProfileCycleMiddlePoint n k center,
        profileAnnularCycleKernelReal n k center u v) ≤
      (1 + rowError) / 2 := by
  dsimp only
  apply sum_profileAnnularCycleKernelReal_two_sided_of_inwardRow hmiddle u
  rw [profileInwardRow_eq_centeredInwardRow u]
  let u0 : LiteralMiddlePoint (scaleRadius n k) :=
    ⟨u.1 - center, mem_discBoundaryFinset.mpr
      ((BoundaryStoppedHarnack.mem_discBoundary_translate
        center (scaleRadius n k) u.1).mp
          (mem_discBoundaryFinset.mp u.2))⟩
  exact sum_skeletonExitKernel_literalInnerBoundary_half_bounds_of_midpoint
    hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep
    hdelta hmidpoint u0

/-- Regular-level specialization: the logarithmic midpoint and positivity
of its denominator are discharged from the exact HLOZ radius formulas. -/
theorem sum_profileAnnularCycleKernelReal_half_bounds_regularLevel
    {n k : ℕ} {center : Point} {boxRadius : ℕ}
    (hn : 0 < n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (hrInner : 2 < scaleRadius n (k + 1))
    (hrMiddle : 2 < scaleRadius n k)
    (hrOuter : 2 < scaleRadius n (k - 1))
    (hOuterBox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ))
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (hmiddle : (profileInnerBoundary n k center).Nonempty)
    (u : ProfileCycleMiddlePoint n k center) :
    let rowError := literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    (1 - rowError) / 2 ≤
      ∑ v : ProfileCycleMiddlePoint n k center,
        profileAnnularCycleKernelReal n k center u v ∧
    (∑ v : ProfileCycleMiddlePoint n k center,
        profileAnnularCycleKernelReal n k center u v) ≤
      (1 + rowError) / 2 := by
  exact sum_profileAnnularCycleKernelReal_half_bounds_of_radial_midpoint
    hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep hmiddle
    (realBoundaryPotentialValue_scaleRadius_outer_sub_inner_pos hn hk hkn)
    (realBoundaryPotentialValue_scaleRadius_midpoint hn hk hkn) u

/-- `HalfRowComparison` wrapper consumed by the endpoint-integrated offspring
algebra. -/
theorem profileAnnularCycleKernelReal_halfRowComparison_regularLevel
    {n k : ℕ} {center : Point} {boxRadius : ℕ}
    (hn : 0 < n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (hrInner : 2 < scaleRadius n (k + 1))
    (hrMiddle : 2 < scaleRadius n k)
    (hrOuter : 2 < scaleRadius n (k - 1))
    (hOuterBox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ))
    (hInnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k)
    (hOuterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1))
    (hmiddle : (profileInnerBoundary n k center).Nonempty) :
    HalfRowComparison
      (literalRealAnnulusRowError
        (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1)))
      (profileAnnularCycleKernelReal n k center) := by
  intro u
  exact sum_profileAnnularCycleKernelReal_half_bounds_regularLevel
    hn hk hkn hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep
    hmiddle u

/-- Full one-parent integrated geometric comparison for a regular profile
level.  Only the final numerical check `rowError ≤ 1` remains external. -/
theorem integratedMarkedOffspringKernel_profile_two_sided_regularLevel
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
    (herror1 : literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k)
        (scaleRadius n (k - 1)) ≤ 1)
    (u : ProfileCycleMiddlePoint n k center) :
    let rowError := literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    (1 - rowError) ^ (q + 1) * halfGeometricMass q ≤
      integratedMarkedOffspringKernel
        (profileAnnularCycleKernelReal n k center)
        (profileAnnularEscapeRowReal n k center) q u ∧
    integratedMarkedOffspringKernel
        (profileAnnularCycleKernelReal n k center)
        (profileAnnularEscapeRowReal n k center) q u ≤
      (1 + rowError) ^ (q + 1) * halfGeometricMass q := by
  dsimp only
  apply integratedMarkedOffspringKernel_two_sided
  · exact literalRealAnnulusRowError_nonneg
      (by linarith) (by linarith)
      (realBoundaryPotentialValue_scaleRadius_outer_sub_inner_pos hn hk hkn)
  · exact herror1
  · intro a b
    exact annularCycleKernelReal_nonneg _ _ _ _ _ a b
  · exact profileAnnularCycle_escape_isStochasticRenewalRow
      houter (by linarith) hOuterSep
  · exact profileAnnularCycleKernelReal_halfRowComparison_regularLevel
      hn hk hkn hrInner hrMiddle hrOuter hOuterBox hInnerSep hOuterSep
      hmiddle

end

end Erdos1165.AnnularOffspringKernelRadialExit

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

import ErdosProblems.Erdos1165.LiteralRealBoundaryPotential
import ErdosProblems.Erdos1165.GreenHarnack
import ErdosProblems.Erdos1165.RealDiscFinite

/-!
# Radial exit probabilities for a literal real-radius annulus

The finite carrier in `literalRealAnnulus` is only a finiteness witness.
This file applies optional stopping to its two actual graph-exit pieces and
bounds those pieces using the potential kernel on the two literal real-radius
boundaries.  No radius is rounded.
-/

open Real Set
open scoped ENNReal

namespace Erdos1165.LiteralRealAnnulusRadialExit

open Annulus AnnulusHarnack GreenHarnack
open LiteralRealAnnulus LiteralRealBoundaryPotential
open PotentialConvergence PotentialEuclideanGeometry PotentialRadialAsymptotic
open ThickPoint

noncomputable section

/-- The radial main term for the potential on `discBoundary 0 r`. -/
def realBoundaryPotentialValue (r : ℝ) : ℝ :=
  (2 / Real.pi) * Real.log r + cPotential

/-- The uniform error on the unit-thick literal boundary at radius `r`. -/
def realBoundaryPotentialError (r : ℝ) : ℝ :=
  (PotentialRadialGlobal.globalRadialConstant + 2) / (r - 1)

theorem realBoundaryPotentialError_nonneg {r : ℝ} (hr : 1 < r) :
    0 ≤ realBoundaryPotentialError r := by
  unfold realBoundaryPotentialError
  exact div_nonneg
    (by linarith [PotentialRadialGlobal.globalRadialConstant_pos]) (by linarith)

theorem realBoundaryPotentialError_antitone
    {r s : ℝ} (hr : 1 < r) (hrs : r ≤ s) :
    realBoundaryPotentialError s ≤ realBoundaryPotentialError r := by
  unfold realBoundaryPotentialError
  have hnum : 0 ≤ PotentialRadialGlobal.globalRadialConstant + 2 := by
    linarith [PotentialRadialGlobal.globalRadialConstant_pos]
  exact div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

/-- A literal boundary point lies in its radial potential window. -/
theorem abs_planarPotentialKernel_sub_realBoundaryPotentialValue_le
    {r : ℝ} {z : Point} (hr : 2 < r) (hz : z ∈ discBoundary 0 r) :
    |planarPotentialKernel z - realBoundaryPotentialValue r| ≤
      realBoundaryPotentialError r := by
  have h := abs_planarPotentialKernel_sub_log_realRadius_le hr hz
  unfold realBoundaryPotentialValue realBoundaryPotentialError
  rw [show planarPotentialKernel z -
      (2 / Real.pi * Real.log r + cPotential) =
        planarPotentialKernel z - 2 / Real.pi * Real.log r - cPotential by ring]
  exact h

/-- Optional stopping on the exact finite graph annulus, with the two radial
boundary errors combined by `max`. -/
theorem abs_planarPotentialKernel_sub_literalRealAnnulusExitMixture_le
    {rInner rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hrInner : 2 < rInner) (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hx : x ∈ literalRealAnnulus rInner rOuter boxRadius) :
    let D := literalRealAnnulus rInner rOuter boxRadius
    let B := literalRealAnnulusInnerExit rInner rOuter boxRadius
    let C := literalRealAnnulusOuterExit rInner rOuter boxRadius
    let innerValue := realBoundaryPotentialValue rInner
    let outerValue := realBoundaryPotentialValue rOuter
    let epsilon := max (realBoundaryPotentialError rInner)
      (realBoundaryPotentialError rOuter)
    |planarPotentialKernel x -
        (innerValue * (exitMass D B x).toReal +
          outerValue * (exitMass D C x).toReal)| ≤ epsilon := by
  dsimp only
  let D := literalRealAnnulus rInner rOuter boxRadius
  let B := literalRealAnnulusInnerExit rInner rOuter boxRadius
  let C := literalRealAnnulusOuterExit rInner rOuter boxRadius
  let innerError := realBoundaryPotentialError rInner
  let outerError := realBoundaryPotentialError rOuter
  have hrOuter0 : 0 ≤ rOuter := hrOuter.le.trans' (by norm_num)
  have hzero : (0 : Point) ∉ D := by
    intro hzeroD
    have hnot := (mem_literalRealAnnulus_iff hrOuter0 hOuterBox).mp hzeroD |>.2.2
    apply hnot
    simp [ThickPoint.disc, ThickPoint.latticeDistance,
      ThickPoint.squaredDistance]
    linarith
  apply abs_potential_sub_twoBoundaryExitMixture_le
    D boxRadius hx (literalRealAnnulus_subset_coordinateBox _ _ _)
    hzero B C
  · intro z hz
    exact (mem_literalRealAnnulusInnerExit _ _ _ z).mp hz |>.1
  · intro z hz
    exact (mem_literalRealAnnulusOuterExit _ _ _ z).mp hz |>.1
  · exact literalRealAnnulus_exit_disjoint _ _ _
  · exact literalRealAnnulus_exit_union _ _ _
  · exact le_max_of_le_left (realBoundaryPotentialError_nonneg (by linarith))
  · intro z hz
    exact (abs_planarPotentialKernel_sub_realBoundaryPotentialValue_le
      hrInner (literalRealAnnulusInnerExit_subset_discBoundary hz)).trans
        (le_max_left _ _)
  · intro z hz
    exact (abs_planarPotentialKernel_sub_realBoundaryPotentialValue_le
      hrOuter (literalRealAnnulusOuterExit_subset_discBoundary
        hrOuter0 hOuterBox hz)).trans (le_max_right _ _)

/-- The two graph-exit masses of a literal real annulus sum to one. -/
theorem literalRealAnnulus_exitMass_toReal_add_eq_one
    {rInner rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hx : x ∈ literalRealAnnulus rInner rOuter boxRadius) :
    (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal +
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusOuterExit rInner rOuter boxRadius) x).toReal = 1 := by
  apply exitMass_partition_toReal_add_eq_one
    (literalRealAnnulus rInner rOuter boxRadius) boxRadius hx
    (literalRealAnnulus_subset_coordinateBox _ _ _)
  · intro z hz
    exact (mem_literalRealAnnulusInnerExit _ _ _ z).mp hz |>.1
  · intro z hz
    exact (mem_literalRealAnnulusOuterExit _ _ _ z).mp hz |>.1
  · exact literalRealAnnulus_exit_disjoint _ _ _
  · exact literalRealAnnulus_exit_union _ _ _

/-- Exit mass depends only on membership of the target mark on the actual
one-step outer boundary. -/
theorem exitMass_eq_of_agree_on_outerBoundary
    {D B C : Finset Point} {x : Point}
    (hx : x ∈ D) (hDB : Disjoint D B) (hDC : Disjoint D C)
    (hagree : ∀ z, z ∈ outerBoundary D → (z ∈ B ↔ z ∈ C)) :
    exitMass D B x = exitMass D C x := by
  have hfinite (n : ℕ) : finiteExitMass D B n x = finiteExitMass D C n x := by
    unfold finiteExitMass
    apply le_antisymm
    · apply stoppedExpectation_mono_of_mem_or_outerBoundary D _ n (Or.inl hx)
      intro z hz
      rcases hz with hzD | hzOuter
      · have hzB : z ∉ B := fun hzB ↦ Finset.disjoint_left.mp hDB hzD hzB
        have hzC : z ∉ C := fun hzC ↦ Finset.disjoint_left.mp hDC hzD hzC
        simp [boundaryIndicator, hzB, hzC]
      · simp only [boundaryIndicator]
        by_cases hzB : z ∈ B
        · have hzC := (hagree z hzOuter).mp hzB
          simp [hzB, hzC]
        · have hzC : z ∉ C := fun hzC ↦
            hzB ((hagree z hzOuter).mpr hzC)
          simp [hzB, hzC]
    · apply stoppedExpectation_mono_of_mem_or_outerBoundary D _ n (Or.inl hx)
      intro z hz
      rcases hz with hzD | hzOuter
      · have hzB : z ∉ B := fun hzB ↦ Finset.disjoint_left.mp hDB hzD hzB
        have hzC : z ∉ C := fun hzC ↦ Finset.disjoint_left.mp hDC hzD hzC
        simp [boundaryIndicator, hzB, hzC]
      · simp only [boundaryIndicator]
        by_cases hzB : z ∈ B
        · have hzC := (hagree z hzOuter).mp hzB
          simp [hzB, hzC]
        · have hzC : z ∉ C := fun hzC ↦
            hzB ((hagree z hzOuter).mpr hzC)
          simp [hzB, hzC]
  unfold exitMass
  congr 1
  funext n
  rw [hfinite]

/-- Marking the whole literal inner disc boundary gives the same exit mass
as marking the actual inner-side graph-exit piece. -/
theorem exitMass_discBoundaryFinset_eq_literalRealAnnulusInnerExit
    {rInner rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hx : x ∈ literalRealAnnulus rInner rOuter boxRadius) :
    exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (RealDiscFinite.discBoundaryFinset 0 rInner) x =
      exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) x := by
  let D := literalRealAnnulus rInner rOuter boxRadius
  let B := RealDiscFinite.discBoundaryFinset 0 rInner
  let C := literalRealAnnulusInnerExit rInner rOuter boxRadius
  have hDB : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro z hzD hzB
    have hzNotInner := (mem_literalRealAnnulus_raw.mp hzD).2.2.2
    exact hzNotInner (RealDiscFinite.mem_discBoundaryFinset.mp hzB).1
  have hDC : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro z hzD hzC
    exact (mem_outerBoundary D z).mp
      ((mem_literalRealAnnulusInnerExit _ _ _ z).mp hzC).1 |>.1 hzD
  apply exitMass_eq_of_agree_on_outerBoundary hx hDB hDC
  intro z hzOuter
  constructor
  · intro hzB
    apply (mem_literalRealAnnulusInnerExit _ _ _ z).mpr
    exact ⟨hzOuter, (RealDiscFinite.mem_discBoundaryFinset.mp hzB).1⟩
  · intro hzC
    apply RealDiscFinite.mem_discBoundaryFinset.mpr
    exact literalRealAnnulusInnerExit_subset_discBoundary hzC

/-- Quantitative outer-before-inner probability for arbitrary real radii. -/
theorem literalRealAnnulusOuterExit_ratio_bounds
    {rInner rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hrInner : 2 < rInner) (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hx : x ∈ literalRealAnnulus rInner rOuter boxRadius)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner) :
    let epsilon := max (realBoundaryPotentialError rInner)
      (realBoundaryPotentialError rOuter)
    (planarPotentialKernel x - realBoundaryPotentialValue rInner - epsilon) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rInner) ≤
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusOuterExit rInner rOuter boxRadius) x).toReal ∧
    (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusOuterExit rInner rOuter boxRadius) x).toReal ≤
      (planarPotentialKernel x - realBoundaryPotentialValue rInner + epsilon) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rInner) := by
  dsimp only
  let pInner := (exitMass (literalRealAnnulus rInner rOuter boxRadius)
    (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal
  let pOuter := (exitMass (literalRealAnnulus rInner rOuter boxRadius)
    (literalRealAnnulusOuterExit rInner rOuter boxRadius) x).toReal
  have htotal : pInner + pOuter = 1 :=
    literalRealAnnulus_exitMass_toReal_add_eq_one hx
  have hmix := abs_planarPotentialKernel_sub_literalRealAnnulusExitMixture_le
    hrInner hrOuter hOuterBox hx
  have hrewrite :
      realBoundaryPotentialValue rInner * pInner +
          realBoundaryPotentialValue rOuter * pOuter =
        realBoundaryPotentialValue rInner +
          (realBoundaryPotentialValue rOuter -
            realBoundaryPotentialValue rInner) * pOuter := by
    linear_combination realBoundaryPotentialValue rInner * htotal
  change |planarPotentialKernel x -
    (realBoundaryPotentialValue rInner * pInner +
      realBoundaryPotentialValue rOuter * pOuter)| ≤ _ at hmix
  rw [hrewrite, abs_le] at hmix
  constructor
  · rw [div_le_iff₀ hdelta]
    linarith
  · rw [le_div_iff₀ hdelta]
    linarith

/-- The complementary inner-before-outer probability. -/
theorem literalRealAnnulusInnerExit_ratio_bounds
    {rInner rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hrInner : 2 < rInner) (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hx : x ∈ literalRealAnnulus rInner rOuter boxRadius)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner) :
    let epsilon := max (realBoundaryPotentialError rInner)
      (realBoundaryPotentialError rOuter)
    (realBoundaryPotentialValue rOuter - planarPotentialKernel x - epsilon) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rInner) ≤
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ∧
    (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ≤
      (realBoundaryPotentialValue rOuter - planarPotentialKernel x + epsilon) /
        (realBoundaryPotentialValue rOuter -
          realBoundaryPotentialValue rInner) := by
  dsimp only
  let pInner := (exitMass (literalRealAnnulus rInner rOuter boxRadius)
    (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal
  let pOuter := (exitMass (literalRealAnnulus rInner rOuter boxRadius)
    (literalRealAnnulusOuterExit rInner rOuter boxRadius) x).toReal
  have htotal : pInner + pOuter = 1 :=
    literalRealAnnulus_exitMass_toReal_add_eq_one hx
  have hmix := abs_planarPotentialKernel_sub_literalRealAnnulusExitMixture_le
    hrInner hrOuter hOuterBox hx
  have hrewrite :
      realBoundaryPotentialValue rInner * pInner +
          realBoundaryPotentialValue rOuter * pOuter =
        realBoundaryPotentialValue rOuter -
          (realBoundaryPotentialValue rOuter -
            realBoundaryPotentialValue rInner) * pInner := by
    linear_combination realBoundaryPotentialValue rOuter * htotal
  change |planarPotentialKernel x -
    (realBoundaryPotentialValue rInner * pInner +
      realBoundaryPotentialValue rOuter * pOuter)| ≤ _ at hmix
  rw [hrewrite, abs_le] at hmix
  constructor
  · rw [div_le_iff₀ hdelta]
    linarith
  · rw [le_div_iff₀ hdelta]
    linarith

/-! ## The midpoint form used by one regular HLOZ scale gap -/

/-- Relative row error when the middle radial main term is exactly halfway
between the two annular boundary main terms. -/
def literalRealAnnulusRowError
    (rInner rMiddle rOuter : ℝ) : ℝ :=
  2 * (max (realBoundaryPotentialError rInner)
      (realBoundaryPotentialError rOuter) +
    realBoundaryPotentialError rMiddle) /
      (realBoundaryPotentialValue rOuter -
        realBoundaryPotentialValue rInner)

theorem literalRealAnnulusRowError_nonneg
    {rInner rMiddle rOuter : ℝ}
    (hrInner : 1 < rInner) (hrMiddle : 1 < rMiddle)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner) :
    0 ≤ literalRealAnnulusRowError rInner rMiddle rOuter := by
  unfold literalRealAnnulusRowError
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (add_nonneg
        ((realBoundaryPotentialError_nonneg hrInner).trans
          (le_max_left _ _))
        (realBoundaryPotentialError_nonneg hrMiddle)))
    hdelta.le

/-- At a radial-potential midpoint, the endpoint-integrated probability of
first leaving through the inner side is `1/2` up to the explicit boundary
errors.  This is the valid row estimate; it does not condition on one outer
endpoint. -/
theorem literalRealAnnulusInnerExit_half_bounds_of_midpoint
    {rInner rMiddle rOuter : ℝ} {boxRadius : ℕ} {x : Point}
    (hrInner : 2 < rInner) (hrMiddle : 2 < rMiddle)
    (hrOuter : 2 < rOuter)
    (hOuterBox : rOuter ≤ (boxRadius : ℝ))
    (hInnerSep : rInner + 1 ≤ rMiddle)
    (hOuterSep : rMiddle + 1 ≤ rOuter)
    (hxMiddle : x ∈ discBoundary 0 rMiddle)
    (hdelta : 0 < realBoundaryPotentialValue rOuter -
      realBoundaryPotentialValue rInner)
    (hmidpoint : 2 * realBoundaryPotentialValue rMiddle =
      realBoundaryPotentialValue rInner +
        realBoundaryPotentialValue rOuter) :
    let rowError := literalRealAnnulusRowError rInner rMiddle rOuter
    (1 - rowError) / 2 ≤
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ∧
    (exitMass (literalRealAnnulus rInner rOuter boxRadius)
        (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ≤
      (1 + rowError) / 2 := by
  dsimp only
  let innerValue := realBoundaryPotentialValue rInner
  let middleValue := realBoundaryPotentialValue rMiddle
  let outerValue := realBoundaryPotentialValue rOuter
  let epsilon := max (realBoundaryPotentialError rInner)
    (realBoundaryPotentialError rOuter)
  let middleError := realBoundaryPotentialError rMiddle
  let delta := outerValue - innerValue
  let rowError := 2 * (epsilon + middleError) / delta
  have hrOuter0 : 0 ≤ rOuter := by linarith
  have hx := mem_literalRealAnnulus_of_mem_intermediate_discBoundary
    hrOuter0 hOuterBox hInnerSep hOuterSep hxMiddle
  have hratio := literalRealAnnulusInnerExit_ratio_bounds
    hrInner hrOuter hOuterBox hx hdelta
  have hmiddle :=
    abs_planarPotentialKernel_sub_realBoundaryPotentialValue_le
      hrMiddle hxMiddle
  change |planarPotentialKernel x - middleValue| ≤ middleError at hmiddle
  rw [abs_le] at hmiddle
  have hdelta' : 0 < delta := hdelta
  have hmidpoint' : 2 * middleValue = innerValue + outerValue := hmidpoint
  have hmidgap : outerValue - middleValue = delta / 2 := by
    dsimp only [delta]
    linarith
  have hrowMul : ((1 - rowError) / 2) * delta =
      delta / 2 - (epsilon + middleError) := by
    dsimp only [rowError]
    field_simp [ne_of_gt hdelta']
  have hrowMulUpper : ((1 + rowError) / 2) * delta =
      delta / 2 + (epsilon + middleError) := by
    dsimp only [rowError]
    field_simp [ne_of_gt hdelta']
  change
    (1 - rowError) / 2 ≤
        (exitMass (literalRealAnnulus rInner rOuter boxRadius)
          (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ∧
      (exitMass (literalRealAnnulus rInner rOuter boxRadius)
          (literalRealAnnulusInnerExit rInner rOuter boxRadius) x).toReal ≤
        (1 + rowError) / 2
  constructor
  · calc
      (1 - rowError) / 2 ≤
          (outerValue - planarPotentialKernel x - epsilon) / delta := by
        rw [le_div_iff₀ hdelta']
        rw [hrowMul]
        linarith
      _ ≤ _ := hratio.1
  · calc
      _ ≤ (outerValue - planarPotentialKernel x + epsilon) / delta := hratio.2
      _ ≤ (1 + rowError) / 2 := by
        rw [div_le_iff₀ hdelta']
        rw [hrowMulUpper]
        linarith

/-- Logarithm of a regular HLOZ radius. -/
theorem log_regularRadius (n k : ℕ) (hn : 0 < n) :
    Real.log (regularRadius n k) =
      (n : ℝ) - (k : ℝ) + 9 * Real.log n := by
  unfold regularRadius
  rw [Real.log_mul (Real.exp_ne_zero _)]
  · rw [Real.log_exp, Real.log_pow]
    norm_num
  · exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hn))

/-- Three consecutive regular radii have exactly affine logarithms. -/
theorem realBoundaryPotentialValue_regularRadius_midpoint
    (n k : ℕ) (hn : 0 < n) :
    2 * realBoundaryPotentialValue (regularRadius n (k + 1)) =
      realBoundaryPotentialValue (regularRadius n k) +
        realBoundaryPotentialValue (regularRadius n (k + 2)) := by
  unfold realBoundaryPotentialValue
  rw [log_regularRadius n (k + 1) hn,
    log_regularRadius n k hn, log_regularRadius n (k + 2) hn]
  push_cast
  ring

/-- The radial-potential gap across two consecutive regular steps is the
positive constant `4 / π`. -/
theorem realBoundaryPotentialValue_regularRadius_two_step_gap
    (n k : ℕ) (hn : 0 < n) :
    realBoundaryPotentialValue (regularRadius n k) -
        realBoundaryPotentialValue (regularRadius n (k + 2)) =
      4 / Real.pi := by
  unfold realBoundaryPotentialValue
  rw [log_regularRadius n k hn, log_regularRadius n (k + 2) hn]
  push_cast
  ring

/-- Exact midpoint identity for the three radii used at a nonterminal HLOZ
profile level. -/
theorem realBoundaryPotentialValue_scaleRadius_midpoint
    {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    2 * realBoundaryPotentialValue (scaleRadius n k) =
      realBoundaryPotentialValue (scaleRadius n (k + 1)) +
        realBoundaryPotentialValue (scaleRadius n (k - 1)) := by
  rw [scaleRadius_of_le (by omega : k ≤ n),
    scaleRadius_of_le hkn,
    scaleRadius_of_le (by omega : k - 1 ≤ n)]
  have h := realBoundaryPotentialValue_regularRadius_midpoint
    n (k - 1) hn
  rw [show k - 1 + 1 = k by omega,
    show k - 1 + 2 = k + 1 by omega] at h
  linarith

/-- Positivity of the outer-minus-inner radial-potential gap at a regular
HLOZ profile level. -/
theorem realBoundaryPotentialValue_scaleRadius_outer_sub_inner_pos
    {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    0 < realBoundaryPotentialValue (scaleRadius n (k - 1)) -
      realBoundaryPotentialValue (scaleRadius n (k + 1)) := by
  rw [scaleRadius_of_le (by omega : k - 1 ≤ n),
    scaleRadius_of_le hkn]
  have hgap := realBoundaryPotentialValue_regularRadius_two_step_gap
    n (k - 1) hn
  rw [show k - 1 + 2 = k + 1 by omega] at hgap
  rw [hgap]
  exact div_pos (by norm_num) Real.pi_pos

theorem realBoundaryPotentialValue_scaleRadius_outer_sub_inner
    {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    realBoundaryPotentialValue (scaleRadius n (k - 1)) -
        realBoundaryPotentialValue (scaleRadius n (k + 1)) =
      4 / Real.pi := by
  rw [scaleRadius_of_le (by omega : k - 1 ≤ n),
    scaleRadius_of_le hkn]
  have hgap := realBoundaryPotentialValue_regularRadius_two_step_gap
    n (k - 1) hn
  rwa [show k - 1 + 2 = k + 1 by omega] at hgap

/-- A simple upper bound for the regular-level row error in terms of the
smallest of the three radii. -/
theorem literalRealAnnulusRowError_le_pi_mul_innerError
    {rInner rMiddle rOuter : ℝ}
    (hrInner : 1 < rInner) (hInnerMiddle : rInner ≤ rMiddle)
    (hMiddleOuter : rMiddle ≤ rOuter)
    (hgap : realBoundaryPotentialValue rOuter -
        realBoundaryPotentialValue rInner = 4 / Real.pi) :
    literalRealAnnulusRowError rInner rMiddle rOuter ≤
      Real.pi * realBoundaryPotentialError rInner := by
  have hmiddleError := realBoundaryPotentialError_antitone
    hrInner hInnerMiddle
  have houterError := realBoundaryPotentialError_antitone
    hrInner (hInnerMiddle.trans hMiddleOuter)
  unfold literalRealAnnulusRowError
  rw [hgap, max_eq_left houterError]
  have hden : 0 < 4 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hinnerError0 := realBoundaryPotentialError_nonneg hrInner
  calc
    2 * (realBoundaryPotentialError rInner +
          realBoundaryPotentialError rMiddle) / (4 / Real.pi) ≤
        2 * (realBoundaryPotentialError rInner +
          realBoundaryPotentialError rInner) / (4 / Real.pi) := by
      gcongr
    _ = Real.pi * realBoundaryPotentialError rInner := by
      field_simp [ne_of_gt Real.pi_pos]
      ring

end

end Erdos1165.LiteralRealAnnulusRadialExit

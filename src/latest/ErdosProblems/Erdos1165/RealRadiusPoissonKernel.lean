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

import ErdosProblems.Erdos1165.PoissonKernelHarnack
import ErdosProblems.Erdos1165.MarkedBoundaryVisitKernel

/-!
# Poisson-kernel Harnack on a literal real-radius lattice disc

The HLOZ radii are real numbers.  The natural-number carrier below is used
only to exhibit finiteness: membership is exactly membership in the
real-radius disc with its literal inner vertex boundary removed.  In
particular, none of the stopped events, boundaries, or kernels is rounded.

The moving-pole comparison is derived directly from the global radial
potential-kernel estimate.  Its final endpoint form is stated for the
unmarked kernel used by `AnnularOffspringKernel`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.RealRadiusPoissonKernel

open Annulus AnnulusHarnack BoundaryStoppedHarnack GreenFunction GreenProbability
open GreenHarnack
open MarkedBoundaryVisitKernel PlanarPotential
open PoissonKernelExitFlux PoissonKernelGreenPole PoissonKernelLastExit
open PoissonKernelRadial PotentialConvergence PotentialEuclideanGeometry
open PotentialRadialAsymptotic PotentialRadialGlobal
open RadialHarnackSpecialization TerminalSequentialVisitLaw ThickPoint

noncomputable section

/-! ## The exact finite domain -/

/-- The graph interior of the literal real-radius disc.  `boxRadius` is
only a finiteness witness and is erased by `mem_realBoundaryInterior_iff`. -/
noncomputable def realBoundaryInterior (R : ℝ) (boxRadius : ℕ) : Finset Point := by
  classical
  exact (closedDisc boxRadius).filter fun z ↦
    z ∈ ThickPoint.disc 0 R ∧ z ∉ ThickPoint.discBoundary 0 R

/-- Canonical exact finite domain, using the ceiling only as a containing
box.  The radius occurring in membership and in every stopped event remains
the original real number `R`. -/
noncomputable def literalRealBoundaryInterior (R : ℝ) : Finset Point :=
  realBoundaryInterior R ⌈R⌉₊

theorem real_le_literal_boxRadius (R : ℝ) : R ≤ (⌈R⌉₊ : ℝ) :=
  Nat.le_ceil R

theorem mem_realBoundaryInterior_iff
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius) {z : Point} :
    z ∈ realBoundaryInterior R boxRadius ↔
      z ∈ ThickPoint.disc 0 R ∧
        z ∉ ThickPoint.discBoundary 0 R := by
  classical
  rw [realBoundaryInterior, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨mem_closedDisc_of_euclideanRadius_le ?_, h⟩
    have hz : euclideanRadius z ≤ R := by
      simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using h.1
    exact hz.trans hRbox

theorem mem_literalRealBoundaryInterior_iff {R : ℝ} {z : Point} :
    z ∈ literalRealBoundaryInterior R ↔
      z ∈ ThickPoint.disc 0 R ∧
        z ∉ ThickPoint.discBoundary 0 R := by
  exact mem_realBoundaryInterior_iff (real_le_literal_boxRadius R)

theorem realBoundaryInterior_subset_coordinateBox
    (R : ℝ) (boxRadius : ℕ) :
    realBoundaryInterior R boxRadius ⊆ coordinateBox boxRadius := by
  classical
  intro z hz
  rw [realBoundaryInterior] at hz
  exact (mem_closedDisc boxRadius z).mp
    ((Finset.mem_filter.mp hz).1) |>.1

/-- Every real-radius inner-boundary vertex lies in the exact unit shell
`(R-1,R]`. -/
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

theorem neighbor_mem_realBoundaryInterior_or_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius)
    {x : Point} (hx : x ∈ realBoundaryInterior R boxRadius)
    (d : Direction) :
    neighbor x d ∈ realBoundaryInterior R boxRadius ∨
      neighbor x d ∈ ThickPoint.discBoundary 0 R := by
  have hxData := (mem_realBoundaryInterior_iff hRbox).mp hx
  have hnDisc : neighbor x d ∈ ThickPoint.disc 0 R := by
    by_contra hnDisc
    apply hxData.2
    refine ⟨hxData.1, neighbor x d, hnDisc, ?_⟩
    rcases x with ⟨x1, x2⟩
    fin_cases d <;> simp [ThickPoint.Adjacent, neighbor, directionVector]
  by_cases hnBoundary : neighbor x d ∈ ThickPoint.discBoundary 0 R
  · exact Or.inr hnBoundary
  · exact Or.inl ((mem_realBoundaryInterior_iff hRbox).mpr
      ⟨hnDisc, hnBoundary⟩)

theorem outerBoundary_realBoundaryInterior_subset_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius) :
    ∀ {z}, z ∈ outerBoundary (realBoundaryInterior R boxRadius) →
      z ∈ ThickPoint.discBoundary 0 R := by
  intro z hz
  rw [mem_outerBoundary] at hz
  obtain ⟨hzNot, x, hx, d, rfl⟩ := hz
  exact (neighbor_mem_realBoundaryInterior_or_discBoundary hRbox hx d).resolve_left
    hzNot

theorem zero_mem_realBoundaryInterior
    {R : ℝ} {boxRadius : ℕ} (hR : 1 ≤ R)
    (hRbox : R ≤ boxRadius) :
    (0 : Point) ∈ realBoundaryInterior R boxRadius := by
  apply (mem_realBoundaryInterior_iff hRbox).mpr
  constructor
  · simp [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius,
      euclideanRadius, euclideanRadiusSq]
    linarith
  · intro hboundary
    have hlower :=
      (discBoundary_zero_euclideanRadius_bounds_real hboundary).1
    have hzero : euclideanRadius (0 : Point) = 0 := by
      simp [euclideanRadius, euclideanRadiusSq]
    rw [hzero] at hlower
    linarith

/-! ## A real radial cut -/

noncomputable def realThickRadialCut
    (R : ℝ) (boxRadius : ℕ) (S : ℝ) : Finset Point :=
  (realBoundaryInterior R boxRadius).filter fun z ↦
    S < euclideanRadius z ∧ euclideanRadius z < S + 2

noncomputable def realCutBoundaryInterior
    (R : ℝ) (boxRadius : ℕ) (S : ℝ) : Finset Point :=
  realBoundaryInterior R boxRadius \ realThickRadialCut R boxRadius S

@[simp] theorem mem_realThickRadialCut
    {R S : ℝ} {boxRadius : ℕ} {z : Point} :
    z ∈ realThickRadialCut R boxRadius S ↔
      z ∈ realBoundaryInterior R boxRadius ∧
        S < euclideanRadius z ∧ euclideanRadius z < S + 2 := by
  simp [realThickRadialCut]

@[simp] theorem mem_realCutBoundaryInterior
    {R S : ℝ} {boxRadius : ℕ} {z : Point} :
    z ∈ realCutBoundaryInterior R boxRadius S ↔
      z ∈ realBoundaryInterior R boxRadius ∧
        ¬ (S < euclideanRadius z ∧ euclideanRadius z < S + 2) := by
  rw [realCutBoundaryInterior, Finset.mem_sdiff, mem_realThickRadialCut]
  tauto

theorem euclideanRadius_le_of_neighbor_mem_realCutBoundaryInterior
    {R S : ℝ} {boxRadius : ℕ} {x z : Point}
    (hx : euclideanRadius x ≤ S)
    (hz : z ∈ realCutBoundaryInterior R boxRadius S)
    (hneighbor : ∃ d : Direction, z = x + directionVector d) :
    euclideanRadius z ≤ S := by
  obtain ⟨d, rfl⟩ := hneighbor
  have hgap := abs_euclideanRadius_sub_neighbor_le
    (x + directionVector d) d
  rw [add_sub_cancel_right] at hgap
  by_contra hnot
  have hSlower : S < euclideanRadius (x + directionVector d) :=
    lt_of_not_ge hnot
  have hupper : euclideanRadius (x + directionVector d) < S + 2 := by
    linarith [(abs_le.mp hgap).2]
  exact (mem_realCutBoundaryInterior.mp hz).2 ⟨hSlower, hupper⟩

theorem killedPower_realCutBoundaryInterior_eq_zero
    {R S : ℝ} {boxRadius n : ℕ} {x y : Point}
    (hx : euclideanRadius x ≤ S)
    (hy : S + 2 ≤ euclideanRadius y) :
    killedPower planarKernel (realCutBoundaryInterior R boxRadius S) n x y = 0 := by
  induction n generalizing x with
  | zero =>
      have hxy : x ≠ y := by
        intro h
        subst y
        linarith
      exact killedPower_zero_ne planarKernel _ hxy
  | succ n ih =>
      rw [killedPower_succ]
      by_cases hxD : x ∈ realCutBoundaryInterior R boxRadius S
      · rw [if_pos hxD]
        apply Finset.sum_eq_zero
        intro z hz
        by_cases hneighbor : ∃ d : Direction, z = x + directionVector d
        · rw [ih (euclideanRadius_le_of_neighbor_mem_realCutBoundaryInterior
              hx hz hneighbor), mul_zero]
        · have hkernel : planarKernel x z = 0 := by
            apply planarKernel_eq_zero_of_not_neighbor
            intro d hzx
            exact hneighbor ⟨d, hzx⟩
          rw [hkernel, zero_mul]
      · rw [if_neg hxD]

theorem infiniteGreen_realCutBoundaryInterior_eq_zero
    {R S : ℝ} {boxRadius : ℕ} {x y : Point}
    (hx : euclideanRadius x ≤ S)
    (hy : S + 2 ≤ euclideanRadius y) :
    infiniteGreen (realCutBoundaryInterior R boxRadius S) x y = 0 := by
  simp [infiniteGreen, killedPower_realCutBoundaryInterior_eq_zero hx hy]

/-! ## Explicit real-radius errors -/

def realBoundaryPoleGap (R r : ℝ) : ℝ := R - r - 1
def realIntermediatePoleGap (S r : ℝ) : ℝ := S - r

def realBoundaryPoleError (R r : ℝ) : ℝ :=
  (2 * globalRadialConstant + (2 * r + 1)) / realBoundaryPoleGap R r

def realReferencePoleError (R r : ℝ) : ℝ :=
  (2 * globalRadialConstant + 2 * r) / realBoundaryPoleGap R r

def realIntermediatePoleError (S r : ℝ) : ℝ :=
  (2 * globalRadialConstant + 2 * r) / realIntermediatePoleGap S r

def realGreenPoleAdditiveError (R S r : ℝ) : ℝ :=
  2 * realBoundaryPoleError R r + realReferencePoleError R r +
    realIntermediatePoleError S r

def realGreenPoleLower (R S r : ℝ) : ℝ :=
  (2 / Real.pi) * Real.log
      (realBoundaryPoleGap R r / (S + r + 2)) -
    globalRadialConstant / realBoundaryPoleGap R r -
    globalRadialConstant / realIntermediatePoleGap S r -
    realBoundaryPoleError R r

def realPoissonKernelRelativeError (R S r : ℝ) : ℝ :=
  realGreenPoleAdditiveError R S r / realGreenPoleLower R S r

theorem realBoundaryPoleGap_pos
    {R r : ℝ} (hR : r + 2 ≤ R) :
    0 < realBoundaryPoleGap R r := by
  unfold realBoundaryPoleGap
  linarith

theorem realIntermediatePoleGap_pos
    {S r : ℝ} (hS : r + 2 ≤ S) :
    0 < realIntermediatePoleGap S r := by
  unfold realIntermediatePoleGap
  linarith

theorem realGreenPoleAdditiveError_nonneg
    {R S r : ℝ} (hr : 0 ≤ r) (hR : r + 2 ≤ R)
    (hS : r + 2 ≤ S) :
    0 ≤ realGreenPoleAdditiveError R S r := by
  have hb := (realBoundaryPoleGap_pos hR).le
  have hi := (realIntermediatePoleGap_pos hS).le
  unfold realGreenPoleAdditiveError realBoundaryPoleError
    realReferencePoleError realIntermediatePoleError
  have hC := globalRadialConstant_pos.le
  positivity

theorem realPoissonKernelRelativeError_nonneg
    {R S r : ℝ} (hr : 0 ≤ r) (hR : r + 2 ≤ R)
    (hS : r + 2 ≤ S)
    (hlower : 0 < realGreenPoleLower R S r) :
    0 ≤ realPoissonKernelRelativeError R S r := by
  exact div_nonneg (realGreenPoleAdditiveError_nonneg hr hR hS) hlower.le

/-! ## Radial verification for an arbitrary real radius -/

private theorem realBoundary_sub_inner_bounds
    {R r : ℝ} {w x : Point}
    (hw : w ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) :
    realBoundaryPoleGap R r ≤ euclideanRadius (w - x) ∧
      euclideanRadius (w - x) ≤ R + r := by
  have hwBounds := discBoundary_zero_euclideanRadius_bounds_real hw
  have hlower := euclideanRadius_sub_lower w x
  have hupper := euclideanRadius_sub_le_add w x
  constructor
  · unfold realBoundaryPoleGap
    linarith
  · linarith

private theorem realThickShell_sub_inner_bounds
    {S r : ℝ} {start x : Point}
    (hstartLower : S < euclideanRadius start)
    (hstartUpper : euclideanRadius start < S + 2)
    (hx : euclideanRadius x ≤ r) :
    realIntermediatePoleGap S r ≤ euclideanRadius (start - x) ∧
      euclideanRadius (start - x) ≤ S + r + 2 := by
  have hlower := euclideanRadius_sub_lower start x
  have hupper := euclideanRadius_sub_le_add start x
  constructor
  · unfold realIntermediatePoleGap
    linarith
  · linarith

theorem outerBoundary_shifted_potential_oscillation_real
    {R r : ℝ} {boxRadius : ℕ}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R)
    (hRbox : R ≤ boxRadius) {q x : Point}
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) :
    ∀ w, w ∈ outerBoundary (realBoundaryInterior R boxRadius) →
      |planarPotentialKernel (w - x) -
        planarPotentialKernel (q - x)| ≤ realBoundaryPoleError R r := by
  intro w hw
  have hwBoundary :=
    outerBoundary_realBoundaryInterior_subset_discBoundary hRbox hw
  have hwBounds := realBoundary_sub_inner_bounds hwBoundary hx
  have hqBounds := realBoundary_sub_inner_bounds hq hx
  have hgapPos := realBoundaryPoleGap_pos hR
  have hw0 : w - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hgapPos.trans_le hwBounds.1)
  have hq0 : q - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hgapPos.trans_le hqBounds.1)
  have hgap :
      |euclideanRadius (w - x) - euclideanRadius (q - x)| ≤
        2 * r + 1 := by
    rw [abs_le]
    constructor <;> unfold realBoundaryPoleGap at * <;> linarith
  simpa [realBoundaryPoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := w - x) (y := q - x) hgapPos hw0 hq0
      hwBounds.1 hqBounds.1 hgap)

theorem boundaryReference_potential_oscillation_inner_poles_real
    {R r : ℝ} (hr : 0 ≤ r) (hR : r + 2 ≤ R)
    {q x y : Point} (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |planarPotentialKernel (q - y) - planarPotentialKernel (q - x)| ≤
      realReferencePoleError R r := by
  have hxBounds := realBoundary_sub_inner_bounds hq hx
  have hyBounds := realBoundary_sub_inner_bounds hq hy
  have hgapPos := realBoundaryPoleGap_pos hR
  have hx0 : q - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hgapPos.trans_le hxBounds.1)
  have hy0 : q - y ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hgapPos.trans_le hyBounds.1)
  have hxy : euclideanRadius (y - x) ≤ 2 * r :=
    euclideanRadius_sub_le_two_mul_of_le hy hx
  have hgap := (abs_euclideanRadius_sub_sub_le q y x).trans hxy
  simpa [realReferencePoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := q - y) (y := q - x) hgapPos hy0 hx0
      hyBounds.1 hxBounds.1 hgap)

theorem intermediate_potential_oscillation_inner_poles_real
    {S r : ℝ} (hS : r + 2 ≤ S) {start x y : Point}
    (hstartLower : S < euclideanRadius start)
    (hstartUpper : euclideanRadius start < S + 2)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |planarPotentialKernel (start - y) -
      planarPotentialKernel (start - x)| ≤
        realIntermediatePoleError S r := by
  have hxBounds := realThickShell_sub_inner_bounds hstartLower hstartUpper hx
  have hyBounds := realThickShell_sub_inner_bounds hstartLower hstartUpper hy
  have hgapPos := realIntermediatePoleGap_pos hS
  have hx0 : start - x ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hgapPos.trans_le hxBounds.1)
  have hy0 : start - y ≠ 0 :=
    (euclideanRadius_pos_iff _).mp (hgapPos.trans_le hyBounds.1)
  have hxy : euclideanRadius (y - x) ≤ 2 * r :=
    euclideanRadius_sub_le_two_mul_of_le hy hx
  have hgap := (abs_euclideanRadius_sub_sub_le start y x).trans hxy
  simpa [realIntermediatePoleError] using
    (abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
      (x := start - y) (y := start - x) hgapPos hy0 hx0
      hyBounds.1 hxBounds.1 hgap)

theorem abs_potentialReferenceDifference_inner_poles_real
    {R S r : ℝ} (hr : 0 ≤ r) (hR : r + 2 ≤ R)
    (hS : r + 2 ≤ S) {q start x y : Point}
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hstartLower : S < euclideanRadius start)
    (hstartUpper : euclideanRadius start < S + 2)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r) :
    |(planarPotentialKernel (q - y) -
        planarPotentialKernel (start - y)) -
      (planarPotentialKernel (q - x) -
        planarPotentialKernel (start - x))| ≤
      realReferencePoleError R r + realIntermediatePoleError S r := by
  have houter := boundaryReference_potential_oscillation_inner_poles_real
    hr hR hq hx hy
  have hinner := intermediate_potential_oscillation_inner_poles_real
    hS hstartLower hstartUpper hx hy
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
    _ ≤ realReferencePoleError R r + realIntermediatePoleError S r :=
      add_le_add houter hinner

theorem realGreenPoleLower_le_potentialReference
    {R S r : ℝ} (hr : 0 ≤ r) (hR : r + 2 ≤ R)
    (hS : r + 2 ≤ S) {q start x : Point}
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hstartLower : S < euclideanRadius start)
    (hstartUpper : euclideanRadius start < S + 2)
    (hx : euclideanRadius x ≤ r) :
    realGreenPoleLower R S r ≤
      planarPotentialKernel (q - x) -
        planarPotentialKernel (start - x) - realBoundaryPoleError R r := by
  let qx := q - x
  let sx := start - x
  have hqBounds := realBoundary_sub_inner_bounds hq hx
  have hsBounds := realThickShell_sub_inner_bounds hstartLower hstartUpper hx
  have hqGap := realBoundaryPoleGap_pos hR
  have hsGap := realIntermediatePoleGap_pos hS
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
        globalRadialConstant / realBoundaryPoleGap R r :=
    div_le_div_of_nonneg_left hC hqGap hqBounds.1
  have hsRemainder :
      globalRadialConstant / euclideanRadius sx ≤
        globalRadialConstant / realIntermediatePoleGap S r :=
    div_le_div_of_nonneg_left hC hsGap hsBounds.1
  have hqLog :
      Real.log (realBoundaryPoleGap R r) ≤ Real.log (euclideanRadius qx) :=
    Real.log_le_log hqGap hqBounds.1
  have hsumPos : 0 < S + r + 2 := by linarith
  have hsLog : Real.log (euclideanRadius sx) ≤ Real.log (S + r + 2) := by
    apply Real.log_le_log hsPos
    exact hsBounds.2
  have hcoef : 0 ≤ (2 : ℝ) / Real.pi := by positivity
  have hqMainLower :
      (2 / Real.pi) * Real.log (realBoundaryPoleGap R r) + cPotential -
          globalRadialConstant / realBoundaryPoleGap R r ≤
        planarPotentialKernel qx := by
    calc
      (2 / Real.pi) * Real.log (realBoundaryPoleGap R r) + cPotential -
          globalRadialConstant / realBoundaryPoleGap R r ≤
        (2 / Real.pi) * Real.log (euclideanRadius qx) + cPotential -
          globalRadialConstant / euclideanRadius qx := by
            have hm := mul_le_mul_of_nonneg_left hqLog hcoef
            linarith
      _ ≤ planarPotentialKernel qx := hqExpansionLower
  have hsMainUpper :
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (S + r + 2) + cPotential +
          globalRadialConstant / realIntermediatePoleGap S r := by
    calc
      planarPotentialKernel sx ≤
        (2 / Real.pi) * Real.log (euclideanRadius sx) + cPotential +
          globalRadialConstant / euclideanRadius sx := hsExpansionUpper
      _ ≤ (2 / Real.pi) * Real.log (S + r + 2) + cPotential +
          globalRadialConstant / realIntermediatePoleGap S r := by
            have hm := mul_le_mul_of_nonneg_left hsLog hcoef
            linarith
  dsimp only [qx, sx] at hqMainLower hsMainUpper ⊢
  unfold realGreenPoleLower
  rw [Real.log_div hqGap.ne' hsumPos.ne']
  linarith

/-! ## Moving-pole Green comparison -/

theorem infiniteGreen_realBoundaryInterior_compare_inner_poles
    (R S r : ℝ) (boxRadius : ℕ) {q start x y : Point}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hRbox : R ≤ boxRadius)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hstart : start ∈ realThickRadialCut R boxRadius S)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < realGreenPoleLower R S r) :
    let error := realPoissonKernelRelativeError R S r
    (1 - error) *
        (infiniteGreen (realBoundaryInterior R boxRadius) start x).toReal ≤
      (infiniteGreen (realBoundaryInterior R boxRadius) start y).toReal ∧
    (infiniteGreen (realBoundaryInterior R boxRadius) start y).toReal ≤
      (1 + error) *
        (infiniteGreen (realBoundaryInterior R boxRadius) start x).toReal := by
  dsimp only
  have hstartData := mem_realThickRadialCut.mp hstart
  have hboundaryX := outerBoundary_shifted_potential_oscillation_real
    hr hR hRbox hq hx
  have hboundaryY := outerBoundary_shifted_potential_oscillation_real
    hr hR hRbox hq hy
  have hpole := abs_potentialReferenceDifference_inner_poles_real
    hr hR hS hq hstartData.2.1 hstartData.2.2 hx hy
  have hlowerReference := realGreenPoleLower_le_potentialReference
    hr hR hS hq hstartData.2.1 hstartData.2.2 hx
  have hboundary0 : 0 ≤ realBoundaryPoleError R r := by
    unfold realBoundaryPoleError
    apply div_nonneg
    · linarith [globalRadialConstant_pos.le]
    · exact (realBoundaryPoleGap_pos hR).le
  have href0 : 0 ≤ realReferencePoleError R r := by
    unfold realReferencePoleError
    apply div_nonneg
    · linarith [globalRadialConstant_pos.le]
    · exact (realBoundaryPoleGap_pos hR).le
  have hintermediate0 : 0 ≤ realIntermediatePoleError S r := by
    unfold realIntermediatePoleError
    apply div_nonneg
    · linarith [globalRadialConstant_pos.le]
    · exact (realIntermediatePoleGap_pos hS).le
  have hcompare := infiniteGreen_compare_of_boundaryReferences
    (realBoundaryInterior R boxRadius) boxRadius hstartData.1
    (realBoundaryInterior_subset_coordinateBox R boxRadius)
    hboundary0 hboundary0 hboundaryX hboundaryY
    (add_nonneg href0 hintermediate0) hpole hlower hlowerReference
  simpa only [realGreenPoleAdditiveError, realPoissonKernelRelativeError,
    add_assoc, two_mul, div_eq_mul_inv] using hcompare

theorem mem_realBoundaryInterior_of_euclideanRadius_le
    {R r : ℝ} {boxRadius : ℕ} {x : Point}
    (hR : r + 2 ≤ R) (hRbox : R ≤ boxRadius)
    (hx : euclideanRadius x ≤ r) :
    x ∈ realBoundaryInterior R boxRadius := by
  apply (mem_realBoundaryInterior_iff hRbox).mpr
  constructor
  · change ThickPoint.latticeDistance 0 x ≤ R
    rw [latticeDistance_zero_eq_euclideanRadius]
    linarith
  · intro hboundary
    have hlower :=
      (discBoundary_zero_euclideanRadius_bounds_real hboundary).1
    linarith

/-! ## Propagation from the cut to the exit endpoint -/

theorem infiniteGreen_realBoundaryInterior_le_of_outer_target
    (R S r : ℝ) (boxRadius : ℕ) {q x y a : Point}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hRbox : R ≤ boxRadius)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (ha : S + 2 ≤ euclideanRadius a)
    (hlower : 0 < realGreenPoleLower R S r) :
    infiniteGreen (realBoundaryInterior R boxRadius) y a ≤
      ENNReal.ofReal (1 + realPoissonKernelRelativeError R S r) *
        infiniteGreen (realBoundaryInterior R boxRadius) x a := by
  let D := realBoundaryInterior R boxRadius
  let C := realThickRadialCut R boxRadius S
  let c : ℝ≥0∞ := ENNReal.ofReal (1 + realPoissonKernelRelativeError R S r)
  have hxS : euclideanRadius x ≤ S := hx.trans (by linarith)
  have hyS : euclideanRadius y ≤ S := hy.trans (by linarith)
  have hxAvoid : infiniteGreen (D \ C) x a = 0 := by
    simpa only [D, C, realCutBoundaryInterior] using
      (infiniteGreen_realCutBoundaryInterior_eq_zero
        (R := R) (boxRadius := boxRadius) hxS ha)
  have hyAvoid : infiniteGreen (D \ C) y a = 0 := by
    simpa only [D, C, realCutBoundaryInterior] using
      (infiniteGreen_realCutBoundaryInterior_eq_zero
        (R := R) (boxRadius := boxRadius) hyS ha)
  have herror0 : 0 ≤ realPoissonKernelRelativeError R S r :=
    realPoissonKernelRelativeError_nonneg hr hR hS hlower
  have hcReal : c.toReal = 1 + realPoissonKernelRelativeError R S r := by
    simp [c, ENNReal.toReal_ofReal (by linarith :
      0 ≤ 1 + realPoissonKernelRelativeError R S r)]
  apply infiniteGreen_le_mul_of_cut D C y x a c hyAvoid hxAvoid
  intro z hz
  have hzC : z ∈ realThickRadialCut R boxRadius S :=
    (Finset.mem_inter.mp hz).2
  have hcompare := infiniteGreen_realBoundaryInterior_compare_inner_poles
    R S r boxRadius hr hR hS hRbox hq hzC hx hy hlower
  have hfiniteY : infiniteGreen D z y ≠ ⊤ :=
    infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius z y
      (realBoundaryInterior_subset_coordinateBox R boxRadius)
  have hfiniteX : infiniteGreen D z x ≠ ⊤ :=
    infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius z x
      (realBoundaryInterior_subset_coordinateBox R boxRadius)
  rw [infiniteGreen_symm D y z, infiniteGreen_symm D x z]
  apply (ENNReal.toReal_le_toReal hfiniteY
    (ENNReal.mul_ne_top (by simp [c]) hfiniteX)).mp
  rw [ENNReal.toReal_mul, hcReal]
  exact hcompare.2

theorem realBoundaryInterior_disjoint_finset_of_subset_discBoundary
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius)
    (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R) :
    Disjoint (realBoundaryInterior R boxRadius) B := by
  rw [Finset.disjoint_left]
  intro z hzD hzB
  exact ((mem_realBoundaryInterior_iff hRbox).mp hzD).2 (hB z hzB)

theorem real_sub_two_le_euclideanRadius_of_exitFlux_ne_zero
    {R : ℝ} (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R)
    {a : Point} (hflux : exitFlux B a ≠ 0) :
    R - 2 ≤ euclideanRadius a := by
  obtain ⟨b, hbB, hbKernel⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := B) (f := planarKernel a) hflux
  have hneighbor : ∃ d : Direction, b = a + directionVector d := by
    by_contra h
    have hzero : planarKernel a b = 0 := by
      apply planarKernel_eq_zero_of_not_neighbor
      intro d hd
      exact h ⟨d, hd⟩
    exact hbKernel hzero
  obtain ⟨d, rfl⟩ := hneighbor
  have hboundary := hB (a + directionVector d) hbB
  have hlower :=
    (discBoundary_zero_euclideanRadius_bounds_real hboundary).1
  have hgap := abs_euclideanRadius_sub_neighbor_le
    (a + directionVector d) d
  rw [add_sub_cancel_right] at hgap
  linarith [(abs_le.mp hgap).2]

theorem cutRadius_le_euclideanRadius_of_realBoundaryInterior_exitFlux_ne_zero
    {R S : ℝ} (hSR : S + 4 ≤ R) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R)
    {a : Point} (hflux : exitFlux B a ≠ 0) :
    S + 2 ≤ euclideanRadius a := by
  have hradius := real_sub_two_le_euclideanRadius_of_exitFlux_ne_zero B hB hflux
  linarith

theorem exitMass_realBoundaryInterior_le
    (R S r : ℝ) (boxRadius : ℕ) (B : Finset Point)
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hRbox : R ≤ boxRadius)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R)
    {q x y : Point} (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < realGreenPoleLower R S r) :
    exitMass (realBoundaryInterior R boxRadius) B y ≤
      ENNReal.ofReal (1 + realPoissonKernelRelativeError R S r) *
        exitMass (realBoundaryInterior R boxRadius) B x := by
  have hxD := mem_realBoundaryInterior_of_euclideanRadius_le
    hR hRbox hx
  have hyD := mem_realBoundaryInterior_of_euclideanRadius_le
    hR hRbox hy
  apply exitMass_le_of_infiniteGreen_le_on_exitFlux_support
    (realBoundaryInterior R boxRadius) B
    (realBoundaryInterior_disjoint_finset_of_subset_discBoundary hRbox B hB)
    hxD hyD
  intro a _ha hflux
  exact infiniteGreen_realBoundaryInterior_le_of_outer_target
    R S r boxRadius hr hR hS hRbox hq hx hy
    (cutRadius_le_euclideanRadius_of_realBoundaryInterior_exitFlux_ne_zero
      hcutOuter B hB hflux)
    hlower

theorem exitMass_realBoundaryInterior_compare
    (R S r : ℝ) (boxRadius : ℕ) (B : Finset Point)
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hRbox : R ≤ boxRadius)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 R)
    {q x y : Point} (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < realGreenPoleLower R S r) :
    exitMass (realBoundaryInterior R boxRadius) B y ≤
        ENNReal.ofReal (1 + realPoissonKernelRelativeError R S r) *
          exitMass (realBoundaryInterior R boxRadius) B x ∧
      exitMass (realBoundaryInterior R boxRadius) B x ≤
        ENNReal.ofReal (1 + realPoissonKernelRelativeError R S r) *
          exitMass (realBoundaryInterior R boxRadius) B y := by
  exact ⟨exitMass_realBoundaryInterior_le R S r boxRadius B hr hR hS
      hcutOuter hRbox hB hq hx hy hlower,
    exitMass_realBoundaryInterior_le R S r boxRadius B hr hR hS
      hcutOuter hRbox hB hq hy hx hlower⟩

/-- The endpoint form used by the annular offspring kernel. -/
theorem exitMass_realBoundaryInterior_singleton_toReal_two_sided
    (R S r : ℝ) (boxRadius : ℕ) {q x y exit : Point}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hRbox : R ≤ boxRadius)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < realGreenPoleLower R S r)
    (herror1 : realPoissonKernelRelativeError R S r ≤ 1) :
    (1 - realPoissonKernelRelativeError R S r) *
          (exitMass (realBoundaryInterior R boxRadius) {exit} x).toReal ≤
        (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal ∧
      (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal ≤
        (1 + realPoissonKernelRelativeError R S r) *
          (exitMass (realBoundaryInterior R boxRadius) {exit} x).toReal := by
  let e := realPoissonKernelRelativeError R S r
  have he0 : 0 ≤ e := realPoissonKernelRelativeError_nonneg hr hR hS hlower
  have hc0 : 0 ≤ 1 + e := by linarith
  have hB : ∀ b ∈ ({exit} : Finset Point),
      b ∈ ThickPoint.discBoundary 0 R := by
    intro b hb
    simpa using (show b = exit from Finset.mem_singleton.mp hb) ▸ hexit
  have hcompare := exitMass_realBoundaryInterior_compare
    R S r boxRadius {exit} hr hR hS hcutOuter hRbox hB hq hx hy hlower
  have hcompare' :
      exitMass (realBoundaryInterior R boxRadius) {exit} y ≤
          ENNReal.ofReal (1 + e) *
            exitMass (realBoundaryInterior R boxRadius) {exit} x ∧
        exitMass (realBoundaryInterior R boxRadius) {exit} x ≤
          ENNReal.ofReal (1 + e) *
            exitMass (realBoundaryInterior R boxRadius) {exit} y := by
    simpa only [e] using hcompare
  have hfiniteX : exitMass (realBoundaryInterior R boxRadius) {exit} x ≠ ⊤ :=
    ne_of_lt ((exitMass_le_one _ _ _).trans_lt ENNReal.one_lt_top)
  have hfiniteY : exitMass (realBoundaryInterior R boxRadius) {exit} y ≠ ⊤ :=
    ne_of_lt ((exitMass_le_one _ _ _).trans_lt ENNReal.one_lt_top)
  have hfactorFinite : ENNReal.ofReal (1 + e) ≠ ⊤ := by simp
  have hxy := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfactorFinite hfiniteX) hcompare'.1
  have hyx := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfactorFinite hfiniteY) hcompare'.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at hxy hyx
  change (1 - e) *
        (exitMass (realBoundaryInterior R boxRadius) {exit} x).toReal ≤
      (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal ∧
    (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal ≤
      (1 + e) *
        (exitMass (realBoundaryInterior R boxRadius) {exit} x).toReal
  constructor
  · have hfactor : (1 - e) * (1 + e) ≤ 1 := by nlinarith
    calc
      (1 - e) * (exitMass (realBoundaryInterior R boxRadius) {exit} x).toReal ≤
          (1 - e) * ((1 + e) *
            (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal) := by
        exact mul_le_mul_of_nonneg_left hyx (sub_nonneg.mpr herror1)
      _ = ((1 - e) * (1 + e)) *
          (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal := by ring
      _ ≤ 1 * (exitMass (realBoundaryInterior R boxRadius) {exit} y).toReal :=
        mul_le_mul_of_nonneg_right hfactor ENNReal.toReal_nonneg
      _ = _ := one_mul _
  · exact hxy

/-! ## Exact stopped-event bridge -/

private lemma absorbedPosition_eq_trajectoryFrom_of_absorbed_stays_real
    (D : Finset Point) (start : Point) (omega : StepPath) :
    ∀ n, (∀ k < n, absorbedPosition D start omega k ∈ D) →
      absorbedPosition D start omega n = trajectoryFrom start omega n := by
  intro n hstay
  induction n with
  | zero => simp [trajectoryFrom]
  | succ n ih =>
      rw [absorbedPosition_succ,
        absorbedStep_of_mem D (hstay n (Nat.lt_succ_self n)),
        ih (fun k hk ↦ hstay k (hk.trans (Nat.lt_succ_self n))),
        trajectoryFrom_succ]
      rfl

private lemma absorbedPosition_eq_trajectoryFrom_of_trajectory_stays_real
    (D : Finset Point) (start : Point) (omega : StepPath) :
    ∀ n, (∀ k < n, trajectoryFrom start omega k ∈ D) →
      absorbedPosition D start omega n = trajectoryFrom start omega n := by
  intro n hstay
  induction n with
  | zero => simp [trajectoryFrom]
  | succ n ih =>
      rw [absorbedPosition_succ,
        ih (fun k hk ↦ hstay k (hk.trans (Nat.lt_succ_self n))),
        absorbedStep_of_mem D (hstay n (Nat.lt_succ_self n)),
        trajectoryFrom_succ]
      rfl

private lemma trajectoryFrom_mem_realBoundaryInterior_before_firstBoundary
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius)
    {start : Point} (hstart : start ∈ realBoundaryInterior R boxRadius)
    {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt
      (ThickPoint.discBoundary 0 R) start omega N) :
    ∀ k < N, trajectoryFrom start omega k ∈
      realBoundaryInterior R boxRadius := by
  intro k hk
  induction k with
  | zero => simpa only [trajectoryFrom_zero] using hstart
  | succ k ih =>
      have hkN : k < N := (Nat.lt_succ_self k).trans hk
      have hprev := ih hkN
      have hcases := neighbor_mem_realBoundaryInterior_or_discBoundary
        hRbox hprev (omega k)
      have hstep : trajectoryFrom start omega (k + 1) =
          neighbor (trajectoryFrom start omega k) (omega k) := by
        rw [trajectoryFrom_succ]
        rfl
      rw [hstep]
      exact hcases.resolve_right (by
        rw [← hstep]
        exact hfirst.2 (k + 1) hk)

theorem boundaryExitEndpointSteps_realDisc_eq_absorbedExit
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius)
    {start exit : Point}
    (hstart : start ∈ realBoundaryInterior R boxRadius)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    boundaryExitEndpointSteps (ThickPoint.discBoundary 0 R) start exit =
      ⋃ n : ℕ, absorbedExitAt (realBoundaryInterior R boxRadius)
        {exit} n start := by
  let D := realBoundaryInterior R boxRadius
  ext omega
  simp only [boundaryExitEndpointSteps, mem_iUnion, mem_setOf_eq,
    absorbedExitAt]
  constructor
  · rintro ⟨N, hfirst, hendpoint⟩
    have hstay : ∀ k < N, trajectoryFrom start omega k ∈ D :=
      trajectoryFrom_mem_realBoundaryInterior_before_firstBoundary
        hRbox hstart hfirst
    have heq := absorbedPosition_eq_trajectoryFrom_of_trajectory_stays_real
      D start omega N hstay
    refine ⟨N, ?_⟩
    rw [heq, hendpoint]
    simp
  · rintro ⟨n, hn⟩
    have hnEndpoint : absorbedPosition D start omega n = exit := by
      simpa only [Finset.mem_singleton] using hn
    have hexitNotD : exit ∉ D := by
      exact fun hmem ↦ ((mem_realBoundaryInterior_iff hRbox).mp hmem).2 hexit
    let P : ℕ → Prop := fun q ↦ absorbedPosition D start omega q ∉ D
    have hP : ∃ q, P q := ⟨n, by simpa [P, hnEndpoint] using hexitNotD⟩
    let q := Nat.find hP
    have hqNot : absorbedPosition D start omega q ∉ D := Nat.find_spec hP
    have hqle : q ≤ n :=
      Nat.find_min' hP (by simpa [P, hnEndpoint] using hexitNotD)
    have hbefore : ∀ k < q, absorbedPosition D start omega k ∈ D := by
      intro k hk
      by_contra hkNot
      exact (Nat.find_min hP hk) hkNot
    have hqne : q ≠ 0 := by
      intro hq0
      apply hqNot
      rw [hq0]
      simpa [D] using hstart
    obtain ⟨t, hqt⟩ := Nat.exists_eq_succ_of_ne_zero hqne
    rw [hqt] at hqNot hqle hbefore
    have hqNot' : absorbedPosition D start omega (t + 1) ∉ D := by
      simpa [Nat.succ_eq_add_one] using hqNot
    have hqle' : t + 1 ≤ n := by
      simpa [Nat.succ_eq_add_one] using hqle
    have hbefore' : ∀ k < t + 1, absorbedPosition D start omega k ∈ D := by
      intro k hk
      exact hbefore k (by simpa [Nat.succ_eq_add_one] using hk)
    have htMem : absorbedPosition D start omega t ∈ D :=
      hbefore' t (Nat.lt_succ_self t)
    have houter : absorbedPosition D start omega (t + 1) ∈ outerBoundary D :=
      absorbedPosition_exit_mem_outerBoundary D start omega htMem hqNot'
    have hboundary : absorbedPosition D start omega (t + 1) ∈
        ThickPoint.discBoundary 0 R :=
      outerBoundary_realBoundaryInterior_subset_discBoundary hRbox houter
    have hstable := absorbedPosition_stable_after_exit D start omega hqNot'
      (n - (t + 1))
    rw [Nat.add_sub_of_le hqle'] at hstable
    have hqEndpoint : absorbedPosition D start omega (t + 1) = exit :=
      hstable.symm.trans hnEndpoint
    have hqTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays_real
      D start omega (t + 1) hbefore'
    refine ⟨t + 1, ⟨?_, ?_⟩, ?_⟩
    · rw [← hqTrajectory]
      exact hboundary
    · intro k hk
      have hkD := hbefore' k hk
      have hkTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays_real
        D start omega k (fun j hj ↦ hbefore' j (hj.trans hk))
      rw [← hkTrajectory]
      exact ((mem_realBoundaryInterior_iff hRbox).mp hkD).2
    · rw [← hqTrajectory]
      exact hqEndpoint

theorem terminalSkeletonKernel_realDisc_eq_exitMass
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius)
    {start exit : Point}
    (hstart : start ∈ realBoundaryInterior R boxRadius)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    terminalSkeletonKernel (ThickPoint.discBoundary 0 R) start exit =
      exitMass (realBoundaryInterior R boxRadius) {exit} start := by
  rw [terminalSkeletonKernel,
    boundaryExitEndpointSteps_realDisc_eq_absorbedExit hRbox hstart hexit]
  apply fairSteps_iUnion_absorbedExitAt_eq_exitMass
  rw [Finset.disjoint_left]
  intro z hzD hzExit
  have hzEq : z = exit := by simpa using hzExit
  subst z
  exact ((mem_realBoundaryInterior_iff hRbox).mp hzD).2 hexit

theorem skeletonExitKernel_realDisc_eq_exitMass
    {R : ℝ} {boxRadius : ℕ} (hRbox : R ≤ boxRadius)
    {start exit : Point}
    (hstart : start ∈ realBoundaryInterior R boxRadius)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R) :
    skeletonExitKernel (ThickPoint.discBoundary 0 R) start exit =
      exitMass (realBoundaryInterior R boxRadius) {exit} start := by
  rw [← terminalSkeletonKernel_eq_skeletonExitKernel]
  exact terminalSkeletonKernel_realDisc_eq_exitMass hRbox hstart hexit

theorem skeletonExitKernel_realDisc_toReal_two_sided
    (R S r : ℝ) (boxRadius : ℕ) {q x y exit : Point}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hRbox : R ≤ boxRadius)
    (hq : q ∈ ThickPoint.discBoundary 0 R)
    (hexit : exit ∈ ThickPoint.discBoundary 0 R)
    (hx : euclideanRadius x ≤ r) (hy : euclideanRadius y ≤ r)
    (hlower : 0 < realGreenPoleLower R S r)
    (herror1 : realPoissonKernelRelativeError R S r ≤ 1) :
    (1 - realPoissonKernelRelativeError R S r) *
          (skeletonExitKernel (ThickPoint.discBoundary 0 R) x exit).toReal ≤
        (skeletonExitKernel (ThickPoint.discBoundary 0 R) y exit).toReal ∧
      (skeletonExitKernel (ThickPoint.discBoundary 0 R) y exit).toReal ≤
        (1 + realPoissonKernelRelativeError R S r) *
          (skeletonExitKernel (ThickPoint.discBoundary 0 R) x exit).toReal := by
  have hxD := mem_realBoundaryInterior_of_euclideanRadius_le
    hR hRbox hx
  have hyD := mem_realBoundaryInterior_of_euclideanRadius_le
    hR hRbox hy
  rw [skeletonExitKernel_realDisc_eq_exitMass hRbox hxD hexit,
    skeletonExitKernel_realDisc_eq_exitMass hRbox hyD hexit]
  exact exitMass_realBoundaryInterior_singleton_toReal_two_sided
    R S r boxRadius hr hR hS hcutOuter hRbox hq hexit hx hy
      hlower herror1

/-! ## Translation to an arbitrary annular center -/

theorem boundaryExitEndpointSteps_centered_eq_zero_real
    (R : ℝ) (center start exit : Point) :
    boundaryExitEndpointSteps (ThickPoint.discBoundary center R) start exit =
      boundaryExitEndpointSteps (ThickPoint.discBoundary 0 R)
        (start - center) (exit - center) := by
  ext omega
  simp only [boundaryExitEndpointSteps, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨N, ⟨hboundary, hbefore⟩, hend⟩
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · have htranslated :=
        (mem_discBoundary_translate center R _).mp hboundary
      simpa only [trajectoryFrom_sub_center] using htranslated
    · intro k hk hkBoundary
      apply hbefore k hk
      apply (mem_discBoundary_translate center R _).mpr
      simpa only [trajectoryFrom_sub_center] using hkBoundary
    · simpa only [← trajectoryFrom_sub_center, hend]
  · rintro ⟨N, ⟨hboundary, hbefore⟩, hend⟩
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · apply (mem_discBoundary_translate center R _).mpr
      simpa only [trajectoryFrom_sub_center] using hboundary
    · intro k hk hkBoundary
      apply hbefore k hk
      have htranslated :=
        (mem_discBoundary_translate center R _).mp hkBoundary
      simpa only [trajectoryFrom_sub_center] using htranslated
    · apply sub_left_injective
      simpa only [trajectoryFrom_sub_center] using hend

theorem skeletonExitKernel_centered_eq_zero_real
    (R : ℝ) (center start exit : Point) :
    skeletonExitKernel (ThickPoint.discBoundary center R) start exit =
      skeletonExitKernel (ThickPoint.discBoundary 0 R)
        (start - center) (exit - center) := by
  rw [← terminalSkeletonKernel_eq_skeletonExitKernel,
    ← terminalSkeletonKernel_eq_skeletonExitKernel]
  unfold terminalSkeletonKernel
  rw [boundaryExitEndpointSteps_centered_eq_zero_real]

theorem skeletonExitKernel_centered_realDisc_toReal_two_sided
    (R S r : ℝ) (boxRadius : ℕ) (center : Point)
    {q x y exit : Point}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hRbox : R ≤ boxRadius)
    (hq : q - center ∈ ThickPoint.discBoundary 0 R)
    (hexit : exit ∈ ThickPoint.discBoundary center R)
    (hx : euclideanRadius (x - center) ≤ r)
    (hy : euclideanRadius (y - center) ≤ r)
    (hlower : 0 < realGreenPoleLower R S r)
    (herror1 : realPoissonKernelRelativeError R S r ≤ 1) :
    (1 - realPoissonKernelRelativeError R S r) *
          (skeletonExitKernel (ThickPoint.discBoundary center R) x exit).toReal ≤
        (skeletonExitKernel (ThickPoint.discBoundary center R) y exit).toReal ∧
      (skeletonExitKernel (ThickPoint.discBoundary center R) y exit).toReal ≤
        (1 + realPoissonKernelRelativeError R S r) *
          (skeletonExitKernel (ThickPoint.discBoundary center R) x exit).toReal := by
  have hexit0 : exit - center ∈ ThickPoint.discBoundary 0 R :=
    (mem_discBoundary_translate center R exit).mp hexit
  rw [skeletonExitKernel_centered_eq_zero_real R center x exit,
    skeletonExitKernel_centered_eq_zero_real R center y exit]
  exact skeletonExitKernel_realDisc_toReal_two_sided
    R S r boxRadius hr hR hS hcutOuter hRbox hq hexit0 hx hy
      hlower herror1

/-- Canonical fixed-endpoint annular API.  The retained endpoint itself is
used as the boundary reference, and the ceiling is hidden as a finiteness
witness. -/
theorem skeletonExitKernel_centered_literalRealDisc_toReal_two_sided
    (R S r : ℝ) (center : Point) {x y exit : Point}
    (hr : 0 ≤ r) (hR : r + 2 ≤ R) (hS : r + 2 ≤ S)
    (hcutOuter : S + 4 ≤ R)
    (hexit : exit ∈ ThickPoint.discBoundary center R)
    (hx : euclideanRadius (x - center) ≤ r)
    (hy : euclideanRadius (y - center) ≤ r)
    (hlower : 0 < realGreenPoleLower R S r)
    (herror1 : realPoissonKernelRelativeError R S r ≤ 1) :
    (1 - realPoissonKernelRelativeError R S r) *
          (skeletonExitKernel (ThickPoint.discBoundary center R) x exit).toReal ≤
        (skeletonExitKernel (ThickPoint.discBoundary center R) y exit).toReal ∧
      (skeletonExitKernel (ThickPoint.discBoundary center R) y exit).toReal ≤
        (1 + realPoissonKernelRelativeError R S r) *
          (skeletonExitKernel (ThickPoint.discBoundary center R) x exit).toReal := by
  have hexit0 : exit - center ∈ ThickPoint.discBoundary 0 R :=
    (mem_discBoundary_translate center R exit).mp hexit
  exact skeletonExitKernel_centered_realDisc_toReal_two_sided
    R S r ⌈R⌉₊ center hr hR hS hcutOuter
      (real_le_literal_boxRadius R) hexit0 hexit hx hy hlower herror1




end

end Erdos1165.RealRadiusPoissonKernel

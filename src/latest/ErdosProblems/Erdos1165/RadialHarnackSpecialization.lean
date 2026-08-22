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

import ErdosProblems.Erdos1165.PotentialRadialGlobal
import ErdosProblems.Erdos1165.TerminalKernelRadial

/-!
# Euclidean-shell specialization of the sharp annular Harnack theorem

The whole-lattice radial potential asymptotic makes the geometry needed for
HLOZ's terminal annulus particularly transparent.  Potential values at two
lattice points whose Euclidean radii differ by at most one oscillate by
`O(1/r)`, uniformly in their angles and parities.  This module packages that
estimate, proves the literal outer boundary of `closedDisc R` lies in the
shell `(R,R+1]`, and feeds the result into `SharpAnnulusHarnack`.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace Erdos1165.RadialHarnackSpecialization

open Annulus AnnulusHarnack GreenProbability PlanarPotential
open PotentialConvergence PotentialEuclideanGeometry PotentialRadialAll
open PotentialRadialAsymptotic SharpAnnulusHarnack

noncomputable section

def euclideanShellError (rho : ℕ) : ℝ := 13000000002 / (rho : ℝ)

theorem euclideanShellError_nonneg (rho : ℕ) : 0 ≤ euclideanShellError rho := by
  unfold euclideanShellError
  positivity

/-- Whole-lattice angularly uniform comparison for a unit-thick Euclidean
shell. -/
theorem abs_planarPotentialKernel_sub_le_of_euclideanRadius_gap
    {u v : Point} {rho : ℕ} (hrho : 4 ≤ rho)
    (hu : (rho : ℝ) ≤ euclideanRadius u) (hv : (rho : ℝ) ≤ euclideanRadius v)
    (hgap : |euclideanRadius u - euclideanRadius v| ≤ 1) :
    |planarPotentialKernel v - planarPotentialKernel u| ≤
      euclideanShellError rho := by
  simpa [euclideanShellError] using
    PotentialRadialGlobal.abs_planarPotentialKernel_sub_le_of_euclidean_shell
      (x := v) (y := u) hrho hv hu (by simpa only [abs_sub_comm] using hgap)

private theorem neighbor_sub_directionVector (x : Point) (d : Direction) :
    neighbor x d - directionVector d = x := by
  rcases x with ⟨x1, x2⟩
  fin_cases d <;> simp [neighbor, directionVector]

theorem euclideanRadius_le_of_mem_closedDisc {R : ℕ} {x : Point}
    (hx : x ∈ closedDisc R) : euclideanRadius x ≤ R := by
  have hsquare : euclideanRadius x ^ 2 ≤ (R : ℝ) ^ 2 := by
    rw [euclideanRadius_sq]
    unfold euclideanRadiusSq
    have hx' := (mem_closedDisc_iff_radiusSqInt_le R x).mp hx
    unfold radiusSqInt at hx'
    exact_mod_cast hx'
  exact (sq_le_sq₀ (euclideanRadius_nonneg x) (Nat.cast_nonneg R)).1 hsquare

theorem natCast_lt_euclideanRadius_of_not_mem_closedDisc {R : ℕ} {x : Point}
    (hx : x ∉ closedDisc R) : (R : ℝ) < euclideanRadius x := by
  by_contra h
  have hr : euclideanRadius x ≤ R := le_of_not_gt h
  have hsquare : euclideanRadius x ^ 2 ≤ (R : ℝ) ^ 2 :=
    (sq_le_sq₀ (euclideanRadius_nonneg x) (Nat.cast_nonneg R)).2 hr
  apply hx
  rw [mem_closedDisc_iff_radiusSqInt_le]
  rw [euclideanRadius_sq] at hsquare
  unfold euclideanRadiusSq at hsquare
  unfold radiusSqInt
  exact_mod_cast hsquare

theorem mem_closedDisc_of_euclideanRadius_le {R : ℕ} {x : Point}
    (hx : euclideanRadius x ≤ R) : x ∈ closedDisc R := by
  by_contra h
  linarith [natCast_lt_euclideanRadius_of_not_mem_closedDisc h]

theorem latticeDistance_zero_eq_euclideanRadius (x : Point) :
    ThickPoint.latticeDistance 0 x = euclideanRadius x := by
  unfold ThickPoint.latticeDistance ThickPoint.squaredDistance
  unfold euclideanRadius euclideanRadiusSq
  congr 1
  norm_num

private theorem adjacent_eq_neighbor
    {x y : Point} (hxy : ThickPoint.Adjacent x y) :
    ∃ d : Direction, x = neighbor y d := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp only [ThickPoint.Adjacent] at hxy
  have hcases :
      (x1 - y1).natAbs = 0 ∧ (x2 - y2).natAbs = 1 ∨
        (x1 - y1).natAbs = 1 ∧ (x2 - y2).natAbs = 0 := by omega
  rcases hcases with h | h
  · have hx0 := Int.natAbs_eq_zero.mp h.1
    rcases Int.natAbs_eq_iff.mp h.2 with hy | hy
    · refine ⟨2, ?_⟩
      simp [neighbor, directionVector]
      constructor <;> omega
    · refine ⟨3, ?_⟩
      simp [neighbor, directionVector]
      constructor <;> omega
  · have hy0 := Int.natAbs_eq_zero.mp h.2
    rcases Int.natAbs_eq_iff.mp h.1 with hx | hx
    · refine ⟨0, ?_⟩
      simp [neighbor, directionVector]
      constructor <;> omega
    · refine ⟨1, ?_⟩
      simp [neighbor, directionVector]
      constructor <;> omega

theorem abs_euclideanRadius_sub_le_of_adjacent
    {x y : Point} (hxy : ThickPoint.Adjacent x y) :
    |euclideanRadius x - euclideanRadius y| ≤ 1 := by
  obtain ⟨d, rfl⟩ := adjacent_eq_neighbor hxy
  have h := abs_euclideanRadius_sub_neighbor_le (neighbor y d) d
  rw [neighbor_sub_directionVector] at h
  exact h

/-- The inner vertex boundary of the real-radius disc `D(0,rho+1)` lies in
the unit shell `(rho,rho+1]`. -/
theorem discBoundary_zero_euclideanRadius_bounds
    {rho : ℕ} {z : Point}
    (hz : z ∈ ThickPoint.discBoundary 0 (rho + 1 : ℝ)) :
    (rho : ℝ) < euclideanRadius z ∧ euclideanRadius z ≤ rho + 1 := by
  rcases hz with ⟨hzIn, y, hyOut, hzy⟩
  have hzUpper : euclideanRadius z ≤ rho + 1 := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hzIn
  have hyLower : (rho + 1 : ℝ) < euclideanRadius y := by
    simpa [ThickPoint.disc, latticeDistance_zero_eq_euclideanRadius] using hyOut
  have hgap := abs_euclideanRadius_sub_le_of_adjacent hzy
  refine ⟨?_, hzUpper⟩
  linarith [(abs_le.mp hgap).1]

/-- The HLOZ terminal entrance boundary at radius `rho+1`, packaged as a
finite type using the containing exact lattice disc. -/
def terminalEntrance (R rho : ℕ) :=
  {z : ↥(closedDisc R) //
    (z.1 : Point) ∈ ThickPoint.discBoundary 0 (rho + 1 : ℝ)}

noncomputable instance terminalEntrance.instFintype (R rho : ℕ) :
    Fintype (terminalEntrance R rho) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun z : ↥(closedDisc R) ↦
      (z.1 : Point) ∈ ThickPoint.discBoundary 0 (rho + 1 : ℝ))
    (fun _ ↦ by simp)

def terminalEntrancePoint {R rho : ℕ} (u : terminalEntrance R rho) : Point := u.1

theorem terminalEntrance_radius_lower {R rho : ℕ}
    (u : terminalEntrance R rho) :
    (rho : ℝ) ≤ euclideanRadius (terminalEntrancePoint u) :=
  (discBoundary_zero_euclideanRadius_bounds u.2).1.le

theorem terminalEntrance_radius_gap {R rho : ℕ}
    (u v : terminalEntrance R rho) :
    |euclideanRadius (terminalEntrancePoint u) -
      euclideanRadius (terminalEntrancePoint v)| ≤ 1 := by
  have hu := discBoundary_zero_euclideanRadius_bounds u.2
  have hv := discBoundary_zero_euclideanRadius_bounds v.2
  have hu' : (rho : ℝ) < euclideanRadius (terminalEntrancePoint u) ∧
      euclideanRadius (terminalEntrancePoint u) ≤ rho + 1 := by
    simpa [terminalEntrancePoint] using hu
  have hv' : (rho : ℝ) < euclideanRadius (terminalEntrancePoint v) ∧
      euclideanRadius (terminalEntrancePoint v) ≤ rho + 1 := by
    simpa [terminalEntrancePoint] using hv
  rw [abs_le]
  constructor <;> linarith

/-- The graph outer boundary of the exact lattice disc lies in the Euclidean
shell `(R,R+1]`. -/
theorem outerBoundary_closedDisc_euclideanRadius_bounds
    {R : ℕ} {z : Point} (hz : z ∈ outerBoundary (closedDisc R)) :
    (R : ℝ) < euclideanRadius z ∧ euclideanRadius z ≤ R + 1 := by
  rw [mem_outerBoundary] at hz
  refine ⟨natCast_lt_euclideanRadius_of_not_mem_closedDisc hz.1, ?_⟩
  obtain ⟨x, hx, d, rfl⟩ := hz.2
  have hxR := euclideanRadius_le_of_mem_closedDisc hx
  have hgap := abs_euclideanRadius_sub_neighbor_le (neighbor x d) d
  rw [neighbor_sub_directionVector] at hgap
  linarith [(abs_le.mp hgap).2]

/-- Explicit lower window for the boundary-reference Green numerator at
outer radius `R` and unit-thick inner shell `(rho,rho+1]`. -/
def euclideanReferenceLower (R rho : ℕ) : ℝ :=
  (2 / Real.pi) * (Real.log R - Real.log (rho + 1)) -
    2 * euclideanShellError R - euclideanShellError rho

private theorem potential_lower_on_outerBoundary
    {R : ℕ} (hR : 4 ≤ R) {q : Point}
    (hq : q ∈ outerBoundary (closedDisc R)) :
    (2 / Real.pi) * Real.log R + PotentialRadialAsymptotic.cPotential -
        euclideanShellError R ≤ planarPotentialKernel q := by
  have hqBounds := outerBoundary_closedDisc_euclideanRadius_bounds hq
  have hRreal : (4 : ℝ) ≤ R := by exact_mod_cast hR
  have hqAsym :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le
      (hRreal.trans hqBounds.1.le)
  have hRpos : (0 : ℝ) < R := by positivity
  have hqpos : 0 < euclideanRadius q := hRpos.trans hqBounds.1
  have herr : 6500000000 / euclideanRadius q ≤ euclideanShellError R := by
    unfold euclideanShellError
    calc
      6500000000 / euclideanRadius q ≤ 6500000000 / (R : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hRpos hqBounds.1.le
      _ ≤ 13000000002 / (R : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num) hRpos.le
  have hlog : Real.log R ≤ Real.log (euclideanRadius q) :=
    Real.log_le_log hRpos hqBounds.1.le
  have hmain : (2 / Real.pi) * Real.log R ≤
      (2 / Real.pi) * Real.log (euclideanRadius q) :=
    mul_le_mul_of_nonneg_left hlog (div_nonneg (by norm_num) Real.pi_nonneg)
  linarith [(abs_le.mp hqAsym).1]

private theorem potential_upper_on_terminalEntrance
    {R rho : ℕ} (hrho : 4 ≤ rho) (u : terminalEntrance R rho) :
    planarPotentialKernel (terminalEntrancePoint u) ≤
      (2 / Real.pi) * Real.log (rho + 1) +
        PotentialRadialAsymptotic.cPotential + euclideanShellError rho := by
  have huBounds := discBoundary_zero_euclideanRadius_bounds u.2
  have hrhoReal : (4 : ℝ) ≤ rho := by exact_mod_cast hrho
  have huAsym :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le
      (hrhoReal.trans huBounds.1.le)
  have huAsym' :
      |planarPotentialKernel (terminalEntrancePoint u) -
          (2 / Real.pi) * Real.log (euclideanRadius (terminalEntrancePoint u)) -
          PotentialRadialAsymptotic.cPotential| ≤
        6500000000 / euclideanRadius (terminalEntrancePoint u) := by
    simpa [terminalEntrancePoint] using huAsym
  have hrhoPos : (0 : ℝ) < rho := by positivity
  have huPos : 0 < euclideanRadius (terminalEntrancePoint u) := by
    simpa [terminalEntrancePoint] using hrhoPos.trans huBounds.1
  have huLower : (rho : ℝ) ≤ euclideanRadius (terminalEntrancePoint u) :=
    terminalEntrance_radius_lower u
  have huUpper : euclideanRadius (terminalEntrancePoint u) ≤ rho + 1 := by
    simpa [terminalEntrancePoint] using huBounds.2
  have herr : 6500000000 / euclideanRadius (terminalEntrancePoint u) ≤
      euclideanShellError rho := by
    unfold euclideanShellError
    calc
      6500000000 / euclideanRadius (terminalEntrancePoint u) ≤
          6500000000 / (rho : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hrhoPos huLower
      _ ≤ 13000000002 / (rho : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num) hrhoPos.le
  have hlog : Real.log (euclideanRadius (terminalEntrancePoint u)) ≤
      Real.log (rho + 1) := by
    apply Real.log_le_log huPos huUpper
  have hmain :
      (2 / Real.pi) * Real.log (euclideanRadius (terminalEntrancePoint u)) ≤
        (2 / Real.pi) * Real.log (rho + 1) :=
    mul_le_mul_of_nonneg_left hlog (div_nonneg (by norm_num) Real.pi_nonneg)
  linarith [(abs_le.mp huAsym').2]

/-- The explicit radial window really is a lower bound for every reference
Green numerator at the HLOZ terminal entrance boundary. -/
theorem euclideanReferenceLower_le_boundaryReference
    {R rho : ℕ} (hR : 4 ≤ R) (hrho : 4 ≤ rho)
    {q : Point} (hq : q ∈ outerBoundary (closedDisc R))
    (u : terminalEntrance R rho) :
    euclideanReferenceLower R rho ≤ planarPotentialKernel q -
      planarPotentialKernel (terminalEntrancePoint u) - euclideanShellError R := by
  have hqLower := potential_lower_on_outerBoundary hR hq
  have huUpper := potential_upper_on_terminalEntrance hrho u
  unfold euclideanReferenceLower
  linarith

/-- Concrete uniform oscillation on the whole exit boundary of a disc,
with no remaining diagonal-coordinate geometry premise. -/
theorem closedDisc_boundary_potential_oscillation_le_euclideanShellError
    {R : ℕ} (hR : 4 ≤ R) {q : Point}
    (hq : q ∈ outerBoundary (closedDisc R)) :
    ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel z - planarPotentialKernel q| ≤
        euclideanShellError R := by
  intro z hz
  have hqBounds := outerBoundary_closedDisc_euclideanRadius_bounds hq
  have hzBounds := outerBoundary_closedDisc_euclideanRadius_bounds hz
  apply abs_planarPotentialKernel_sub_le_of_euclideanRadius_gap
  · exact hR
  · exact hqBounds.1.le
  · exact hzBounds.1.le
  · rw [abs_le]
    constructor <;> linarith

/-- Hit-probability comparison for starts in one unit-thick Euclidean shell,
with the exit-boundary oscillation fully discharged. -/
theorem hitBeforeExit_closedDisc_compare_via_euclideanShells
    (R rho : ℕ) {lower : ℝ} {x y q : Point}
    (hR : 4 ≤ R) (hq : q ∈ outerBoundary (closedDisc R))
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    (hrho : 4 ≤ rho)
    (hxrho : (rho : ℝ) ≤ euclideanRadius x)
    (hyrho : (rho : ℝ) ≤ euclideanRadius y)
    (hxygap : |euclideanRadius x - euclideanRadius y| ≤ 1)
    (hlower : 0 < lower)
    (href : lower ≤ planarPotentialKernel q - planarPotentialKernel x -
      euclideanShellError R) :
    let error := 2 * euclideanShellError R + euclideanShellError rho
    (1 - error / lower) *
        (simpleRandomWalkFrom x
          (walkHitBeforeExit (closedDisc R) 0)).toReal ≤
      (simpleRandomWalkFrom y
        (walkHitBeforeExit (closedDisc R) 0)).toReal ∧
    (simpleRandomWalkFrom y
        (walkHitBeforeExit (closedDisc R) 0)).toReal ≤
      (1 + error / lower) *
        (simpleRandomWalkFrom x
          (walkHitBeforeExit (closedDisc R) 0)).toReal := by
  apply hitBeforeExit_closedDisc_compare_of_boundaryReference
    R (by simp [radiusSqInt]) hx hy
    (euclideanShellError_nonneg R)
  · simpa using closedDisc_boundary_potential_oscillation_le_euclideanShellError hR hq
  · exact euclideanShellError_nonneg rho
  · simpa using abs_planarPotentialKernel_sub_le_of_euclideanRadius_gap
      hrho hxrho hyrho hxygap
  · exact hlower
  · simpa using href

/-- The error in the concrete one-excursion hit kernel. -/
def euclideanHitError (R rho : ℕ) (lower : ℝ) : ℝ :=
  (2 * euclideanShellError R + euclideanShellError rho) / lower

/-- Actual hit-before-exit probability as a kernel on a finite entrance
boundary. -/
def closedDiscHitKernel {Entrance : Type*} (R : ℕ)
    (entrance : Entrance → Point) (u : Entrance) : ℝ :=
  (simpleRandomWalkFrom (entrance u)
    (walkHitBeforeExit (closedDisc R) 0)).toReal

/-- The global radial asymptotic discharges all potential-oscillation
premises and yields Condition `(star)` for the actual one-excursion hit
kernel on a unit-thick inner shell. -/
theorem conditionStar_closedDiscHitKernel_of_euclideanShells
    {Entrance : Type*} [Fintype Entrance]
    (R rho : ℕ) {lower : ℝ} (q : Point) (entrance : Entrance → Point)
    (hR : 4 ≤ R) (hq : q ∈ outerBoundary (closedDisc R))
    (hinside : ∀ u, entrance u ∈ closedDisc R)
    (hrho : 4 ≤ rho)
    (hradius : ∀ u, (rho : ℝ) ≤ euclideanRadius (entrance u))
    (hgap : ∀ u v,
      |euclideanRadius (entrance u) - euclideanRadius (entrance v)| ≤ 1)
    (hlower : 0 < lower)
    (href : ∀ u, lower ≤ planarPotentialKernel q -
      planarPotentialKernel (entrance u) - euclideanShellError R) :
    AppendixDecoupling.ConditionStar (euclideanHitError R rho lower)
      (closedDiscHitKernel R entrance) := by
  intro u v
  simpa [euclideanHitError, closedDiscHitKernel] using
    (hitBeforeExit_closedDisc_compare_via_euclideanShells
      R rho hR hq (hinside u) (hinside v) hrho
      (hradius u) (hradius v) (hgap u v) hlower (href u))

/-- Literal HLOZ inner-boundary specialization: all entrance-shell geometry
is discharged by the definition of `terminalEntrance`. -/
theorem conditionStar_terminalEntrance_closedDiscHitKernel
    (R rho : ℕ) {lower : ℝ} (q : Point)
    (hR : 4 ≤ R) (hq : q ∈ outerBoundary (closedDisc R))
    (hrho : 4 ≤ rho) (hlower : 0 < lower)
    (href : ∀ u : terminalEntrance R rho,
      lower ≤ planarPotentialKernel q -
        planarPotentialKernel (terminalEntrancePoint u) - euclideanShellError R) :
    AppendixDecoupling.ConditionStar (euclideanHitError R rho lower)
      (closedDiscHitKernel R (@terminalEntrancePoint R rho)) := by
  exact conditionStar_closedDiscHitKernel_of_euclideanShells
    R rho q (@terminalEntrancePoint R rho) hR hq
    (fun u ↦ u.1.2) hrho terminalEntrance_radius_lower
    terminalEntrance_radius_gap hlower href

/-- Complete analytic-to-vector-kernel specialization.  The radial
potential theorem supplies one-excursion Condition `(star)`, and
`TerminalKernelRadial` converts it into the Bernoulli--geometric terminal
success kernel used by the Appendix transfer. -/
theorem terminalKernelComparison_closedDiscHit_of_euclideanShells
    {Entrance : Type*} [Fintype Entrance]
    {scale : ℕ} {profileDelta thickDelta qHit p : ℝ}
    (R rho : ℕ) {lower : ℝ} (q : Point) (entrance : Entrance → Point)
    (hR : 4 ≤ R) (hq : q ∈ outerBoundary (closedDisc R))
    (hinside : ∀ u, entrance u ∈ closedDisc R)
    (hrho : 4 ≤ rho)
    (hradius : ∀ u, (rho : ℝ) ≤ euclideanRadius (entrance u))
    (hgap : ∀ u v,
      |euclideanRadius (entrance u) - euclideanRadius (entrance v)| ≤ 1)
    (hlower : 0 < lower)
    (href : ∀ u, lower ≤ planarPotentialKernel q -
      planarPotentialKernel (entrance u) - euclideanShellError R)
    (hhitHalf : ∀ u, closedDiscHitKernel R entrance u ≤ 1 / 2)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (reference : Fin (AppendixLocalTime.requiredTerminalCount
      scale profileDelta) → Entrance)
    (hrefHit : ∀ j, closedDiscHitKernel R entrance (reference j) = qHit)
    (hqHit0 : 0 ≤ qHit) (hqHit1 : qHit ≤ 1)
    (hepsilon1 : euclideanHitError R rho lower ≤ 1)
    (hsmall : (1 + euclideanHitError R rho lower) ^
      AppendixLocalTime.requiredTerminalCount scale profileDelta ≤ 2) :
    AppendixLocalTimeTransfer.TerminalKernelComparison
      (2 * (AppendixLocalTime.requiredTerminalCount scale profileDelta : ℝ) *
        euclideanHitError R rho lower)
      (AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta qHit p hqHit0 hqHit1 hp0 hp1 thickDelta)
      (TerminalKernelRadial.terminalVisitKernel
        (m := AppendixLocalTime.requiredTerminalCount scale profileDelta)
        (fun _ ↦ closedDiscHitKernel R entrance) (fun _ ↦ p)
        (fun _ _ ↦ measureReal_nonneg)
        (fun _ u ↦ (hhitHalf u).trans (by norm_num))
        (fun _ ↦ hp0) (fun _ ↦ hp1)
        {v | ThickPoint.thickThreshold scale thickDelta ≤
          AppendixLocalTime.totalVisits v}) := by
  have hstar0 := conditionStar_closedDiscHitKernel_of_euclideanShells
    R rho q entrance hR hq hinside hrho hradius hgap hlower href
  have hepsilon0 : 0 ≤ euclideanHitError R rho lower := by
    unfold euclideanHitError
    exact div_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (euclideanShellError_nonneg R))
        (euclideanShellError_nonneg rho)) hlower.le
  exact TerminalKernelRadial.terminalKernelComparison_referenceSuccess_of_visitHit_conditionStar
    (hit := fun _ ↦ closedDiscHitKernel R entrance)
    (hhit0 := fun _ _ ↦ measureReal_nonneg)
    (hhitHalf := fun _ u ↦ hhitHalf u)
    (p := p) (q := qHit) (scale := scale)
    (profileDelta := profileDelta) (thickDelta := thickDelta)
    hp0 hp1
    (epsilon := euclideanHitError R rho lower)
    hepsilon0 hepsilon1 (fun _ ↦ hstar0) reference hrefHit hqHit0 hqHit1 hsmall

end

end Erdos1165.RadialHarnackSpecialization

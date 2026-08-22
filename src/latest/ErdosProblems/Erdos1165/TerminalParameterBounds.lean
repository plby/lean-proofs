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

import ErdosProblems.Erdos1165.BoundaryStoppedHarnack
import ErdosProblems.Erdos1165.BoundaryVisitLaw
import ErdosProblems.Erdos1165.PointBeforeReturn
import ErdosProblems.Erdos1165.PotentialRadialGlobal
import ErdosProblems.Erdos1165.Proposition13Scales

/-!
# Numerical parameters for the terminal Bernoulli--geometric law

This module identifies the two literal one-excursion parameters used in
Appendix A.7 with killed Green functions.  The important normalization is

`p * G_D(0,0) = 1`,

where `p` is escape to the literal vertex boundary before the first positive
return and `D` is the graph interior of that boundary.  Consequently the
ratio `q / p` is exactly the off-diagonal killed Green function.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1165.TerminalParameterBounds

open Annulus GreenFunction GreenProbability GreenHarnack
open PlanarPotential PotentialConvergence
open PotentialEuclideanGeometry
open BoundaryVisitRegeneration BoundaryVisitLaw
open SequentialAnnularKernel
open TerminalExcursionBridge TerminalExcursionDisintegration
open BoundaryStoppedHarnack

noncomputable section

/-- Escape before the first positive return for the literal radius-`R`
vertex boundary, in coordinates centred at the target. -/
def literalEscapeProbability (R : ℕ) : ℝ :=
  escapeBeforePositiveReturnProbability
    (ThickPoint.discBoundary 0 (R : ℝ))

theorem literalEscapeProbability_nonneg (R : ℕ) :
    0 ≤ literalEscapeProbability R :=
  escapeBeforePositiveReturnProbability_nonneg _

theorem literalEscapeProbability_le_one (R : ℕ) :
    literalEscapeProbability R ≤ 1 := by
  unfold literalEscapeProbability escapeBeforePositiveReturnProbability
  linarith [measureReal_nonneg (μ := fairSteps)
    (s := positiveReturnBeforeBoundary
      (ThickPoint.discBoundary 0 (R : ℝ)))]

private theorem zero_not_mem_discBoundary (R : ℕ) (hR : 2 ≤ R) :
    (0 : Point) ∉ ThickPoint.discBoundary 0 (R : ℝ) := by
  intro h
  have hlower :=
    (discBoundary_zero_euclideanRadius_bounds_nat (by omega) h).1
  have hzeroRadius : euclideanRadius (0 : Point) = 0 := by
    simp [euclideanRadius, euclideanRadiusSq]
  rw [hzeroRadius] at hlower
  have hcast : (1 : ℝ) ≤ (R - 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ R - 1 by omega)
  linarith

theorem zero_mem_boundaryInterior (R : ℕ) (hR : 2 ≤ R) :
    (0 : Point) ∈ boundaryInterior R := by
  rw [mem_boundaryInterior]
  exact ⟨by simp [mem_closedDisc, radiusSqInt], zero_not_mem_discBoundary R hR⟩

theorem neighbor_mem_boundaryInterior (R : ℕ) (hR : 3 ≤ R)
    (d : Direction) : directionVector d ∈ boundaryInterior R := by
  have hzero := zero_mem_boundaryInterior R (by omega)
  have hcases := neighbor_mem_boundaryInterior_or_discBoundary hzero d
  simp only [neighbor, zero_add] at hcases
  exact hcases.resolve_right (by
    intro hd
    have hlower :=
      (discBoundary_zero_euclideanRadius_bounds_nat (by omega) hd).1
    have hdir : euclideanRadius (directionVector d) = 1 := by
      fin_cases d <;> norm_num [euclideanRadius, euclideanRadiusSq,
        directionVector]
    rw [hdir] at hlower
    have hcast : (2 : ℝ) ≤ (R - 1 : ℕ) := by
      exact_mod_cast (show 2 ≤ R - 1 by omega)
    linarith)

theorem literalBoundaryHitKernel_neighbor (R : ℕ) (hR : 3 ≤ R)
    (d : Direction) :
    boundaryStoppedHitKernel (ThickPoint.discBoundary 0 (R : ℝ))
        0 (directionVector d) =
      (infiniteHitMass (boundaryInterior R) (directionVector d) 0).toReal := by
  rw [boundaryStoppedHitKernel_eq_boundaryInteriorHitKernel
    (R := R) (neighbor_mem_boundaryInterior R hR d)
    (zero_mem_boundaryInterior R (by omega))]
  rw [simpleRandomWalkFrom_walkHitBeforeExit]

private theorem trajectoryFrom_firstDirection_shift (omega : StepPath) (n : ℕ) :
    trajectoryFrom (directionVector (omega 0)) (shiftSteps 1 omega) n =
      trajectory omega (n + 1) := by
  have hshift := trajectory_add_sub_trajectory omega 1 n
  have hone : trajectory omega 1 = directionVector (omega 0) := by
    rw [show 1 = 0 + 1 by omega, trajectory_succ]
    simp
  rw [hone] at hshift
  unfold trajectoryFrom
  rw [← hshift]
  abel

private theorem firstPositiveReturnTime_spec
    {omega : StepPath} {n : ℕ} (h : firstPositiveReturnTime omega = n) :
    1 ≤ n ∧ trajectory omega n = 0 ∧
      ∀ k < n, 1 ≤ k → trajectory omega k ≠ 0 := by
  have hs := (firstHitSetAfter_eq_coe_iff
    (stoppingTimeSucc zeroClock) ({0} : Set Point) omega n).mp h
  refine ⟨?_, by simpa using hs.2.1, ?_⟩
  · simpa [stoppingTimeSucc, zeroClock] using hs.1
  · intro k hk hk1 hkzero
    exact hs.2.2 k hk ⟨by simpa [stoppingTimeSucc, zeroClock] using hk1,
      by simpa using hkzero⟩

private def firstStepBoundaryHitPiece (R : ℕ) (d : Direction) : Set StepPath :=
  {omega | omega 0 = d} ∩ shiftSteps 1 ⁻¹'
    boundaryHitSteps (ThickPoint.discBoundary 0 (R : ℝ)) 0
      (directionVector d)

private theorem positiveReturnBeforeBoundary_eq_iUnion_firstStep
    (R : ℕ) (hR : 3 ≤ R) :
    positiveReturnBeforeBoundary (ThickPoint.discBoundary 0 (R : ℝ)) =
      ⋃ d : Direction, firstStepBoundaryHitPiece R d := by
  ext omega
  simp only [Set.mem_iUnion]
  constructor
  · intro hreturn
    obtain ⟨n, hn, havoid⟩ := Set.mem_iUnion.mp hreturn
    have hspec := firstPositiveReturnTime_spec hn
    let m := n - 1
    have hnm : m + 1 = n := by omega
    refine ⟨omega 0, ?_⟩
    refine ⟨rfl, ?_⟩
    change trajectoryFrom (directionVector (omega 0)) (shiftSteps 1 omega) ∈
      walkHitBeforeBoundary (ThickPoint.discBoundary 0 (R : ℝ)) 0
    rw [mem_walkHitBeforeBoundary_iff_exists]
    refine ⟨m, ?_, ?_⟩
    · rw [trajectoryFrom_firstDirection_shift, hnm]
      exact hspec.2.1
    · intro k hk
      rw [trajectoryFrom_firstDirection_shift]
      exact havoid (k + 1) (by omega)
  · rintro ⟨d, hpiece⟩
    rcases hpiece with ⟨hd, hhit⟩
    change trajectoryFrom (directionVector d) (shiftSteps 1 omega) ∈
      walkHitBeforeBoundary (ThickPoint.discBoundary 0 (R : ℝ)) 0 at hhit
    rw [mem_walkHitBeforeBoundary_iff_exists] at hhit
    obtain ⟨m, hmzero, hmavoid⟩ := hhit
    have hexists : ∃ n : ℕ,
        firstPositiveReturnTime omega = (n : WithTop ℕ) := by
      have hle : firstPositiveReturnTime omega ≤ (m + 1 : ℕ) :=
        (firstHitSetAfter_le_iff (stoppingTimeSucc zeroClock) ({0} : Set Point)
          omega (m + 1)).2 ⟨m + 1, le_rfl, by
            simp [stoppingTimeSucc, zeroClock], by
            have htraj := trajectoryFrom_firstDirection_shift omega m
            rw [hd] at htraj
            rw [← htraj]
            exact hmzero⟩
      have hfinite : firstPositiveReturnTime omega ≠ ⊤ :=
        WithTop.lt_top_iff_ne_top.mp
          (hle.trans_lt (WithTop.coe_lt_top (m + 1)))
      lift firstPositiveReturnTime omega to ℕ using hfinite with n hn
      exact ⟨n, rfl⟩
    obtain ⟨n, hn⟩ := hexists
    have hnle : n ≤ m + 1 := by
      have hle : firstPositiveReturnTime omega ≤ (m + 1 : ℕ) :=
        (firstHitSetAfter_le_iff (stoppingTimeSucc zeroClock) ({0} : Set Point)
          omega (m + 1)).2 ⟨m + 1, le_rfl, by
            simp [stoppingTimeSucc, zeroClock], by
            have htraj := trajectoryFrom_firstDirection_shift omega m
            rw [hd] at htraj
            rw [← htraj]
            exact hmzero⟩
      rw [hn] at hle
      exact WithTop.coe_le_coe.mp hle
    refine Set.mem_iUnion.mpr ⟨n, hn, ?_⟩
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [trajectory] using zero_not_mem_discBoundary R (by omega)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      rw [← trajectoryFrom_firstDirection_shift, hd]
      exact hmavoid j (by omega)

private theorem firstStepBoundaryHitPiece_pairwiseDisjoint (R : ℕ) :
    Pairwise fun d e : Direction ↦
      Disjoint (firstStepBoundaryHitPiece R d) (firstStepBoundaryHitPiece R e) := by
  intro d e hde
  rw [Set.disjoint_left]
  intro omega hd he
  exact hde (hd.1.symm.trans he.1)

private theorem measurableSet_firstDirection (d : Direction) :
    MeasurableSet[incrementFiltration 1] {omega : StepPath | omega 0 = d} := by
  rw [incrementFiltration_apply]
  refine ⟨{u : Fin 1 → Direction | u 0 = d},
    (Set.to_countable _).measurableSet, ?_⟩
  ext omega
  simp [stepPrefix]

private theorem isMeasurableAtWithTopStopping_firstDirection (d : Direction) :
    IsMeasurableAtWithTopStopping (fun _ : StepPath ↦ (1 : WithTop ℕ))
      {omega : StepPath | omega 0 = d} := by
  intro n
  by_cases hn : n = 1
  · subst n
    simpa using measurableSet_firstDirection d
  · have hempty : {omega : StepPath | omega 0 = d} ∩
        {omega | (1 : WithTop ℕ) = (n : WithTop ℕ)} = ∅ := by
      ext omega
      constructor
      · rintro ⟨_homega, hcoe⟩
        exact (hn (WithTop.coe_eq_coe.mp hcoe.symm)).elim
      · intro h
        exact h.elim
    rw [hempty]
    exact (incrementFiltration n).measurableSet_empty

private theorem fairSteps_firstDirection (d : Direction) :
    fairSteps {omega : StepPath | omega 0 = d} = 1 / 4 := by
  change fairSteps ((fun omega : StepPath ↦ omega 0) ⁻¹' {d}) = 1 / 4
  rw [← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.singleton d),
    fairSteps_eval, fairStep_singleton]

private theorem postWithTopStoppingSteps_const_one :
    postWithTopStoppingSteps
      (fun _ : StepPath ↦ ((1 : ℕ) : WithTop ℕ)) = shiftSteps 1 := by
  rfl

private theorem measure_firstStepBoundaryHitPiece (R : ℕ) (d : Direction) :
    fairSteps (firstStepBoundaryHitPiece R d) =
      (1 / 4 : ℝ≥0∞) * fairSteps
        (boundaryHitSteps (ThickPoint.discBoundary 0 (R : ℝ)) 0
          (directionVector d)) := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    (isStoppingTime_const incrementFiltration 1)
    (isMeasurableAtWithTopStopping_firstDirection d)
    (measurableSet_boundaryHitSteps
      (ThickPoint.discBoundary 0 (R : ℝ)) 0 (directionVector d))
  convert hmarkov using 1
  · apply congrArg fairSteps
    ext omega
    simp [firstStepBoundaryHitPiece, postWithTopStoppingSteps]
  · simp [fairSteps_firstDirection]

private theorem measurableSet_firstStepBoundaryHitPiece (R : ℕ) (d : Direction) :
    MeasurableSet (firstStepBoundaryHitPiece R d) := by
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    ((measurable_shiftSteps 1)
      (measurableSet_boundaryHitSteps
        (ThickPoint.discBoundary 0 (R : ℝ)) 0 (directionVector d)))

/-- The probability of returning before the literal boundary is the average
of the four killed point-hitting probabilities from the first-step
neighbours. -/
theorem positiveReturnBeforeBoundary_probability_eq_neighborAverage
    (R : ℕ) (hR : 3 ≤ R) :
    fairSteps.real
        (positiveReturnBeforeBoundary (ThickPoint.discBoundary 0 (R : ℝ))) =
      ∑ d : Direction, (1 / 4 : ℝ) *
        (infiniteHitMass (boundaryInterior R) (directionVector d) 0).toReal := by
  rw [positiveReturnBeforeBoundary_eq_iUnion_firstStep R hR,
    measureReal_def, measure_iUnion
      (firstStepBoundaryHitPiece_pairwiseDisjoint R)
      (measurableSet_firstStepBoundaryHitPiece R),
    tsum_fintype, ENNReal.toReal_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [measure_firstStepBoundaryHitPiece, ENNReal.toReal_mul,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    fairSteps_boundaryHitSteps_toReal,
    literalBoundaryHitKernel_neighbor R hR d]
  norm_num

private theorem killedPower_succ_zero_eq_direction_sum
    (R n : ℕ) (hR : 3 ≤ R) :
    killedPower planarKernel (boundaryInterior R) (n + 1) 0 0 =
      ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
        killedPower planarKernel (boundaryInterior R) n
          (directionVector d) 0 := by
  rw [← fairSteps_killedPathEvent, measure_killedPathEvent_succ,
    if_pos (zero_mem_boundaryInterior R (by omega))]
  simp_rw [fairSteps_killedPathEvent]
  simp only [zero_add]

private theorem infiniteGreen_diagonal_firstStep
    (R : ℕ) (hR : 3 ≤ R) :
    infiniteGreen (boundaryInterior R) 0 0 =
      1 + ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
        infiniteGreen (boundaryInterior R) (directionVector d) 0 := by
  rw [infiniteGreen, tsum_eq_zero_add' ENNReal.summable,
    killedPower_zero_self planarKernel (boundaryInterior R)
      (zero_mem_boundaryInterior R (by omega))]
  congr 1
  simp_rw [killedPower_succ_zero_eq_direction_sum R _ hR]
  calc
    (∑' n : ℕ, ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
        killedPower planarKernel (boundaryInterior R) n
          (directionVector d) 0) =
        ∑' d : Direction, ∑' n : ℕ, (1 / 4 : ℝ≥0∞) *
          killedPower planarKernel (boundaryInterior R) n
            (directionVector d) 0 := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm :
          (∑' n : ℕ, ∑' d : Direction, (1 / 4 : ℝ≥0∞) *
            killedPower planarKernel (boundaryInterior R) n
              (directionVector d) 0) = _)
    _ = ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
        infiniteGreen (boundaryInterior R) (directionVector d) 0 := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [ENNReal.tsum_mul_left]
      rfl

/-- Killed renewal at the target: the diagonal Green function is one plus
the return-before-boundary mass times itself. -/
theorem infiniteGreen_diagonal_eq_one_add_return_mul
    (R : ℕ) (hR : 3 ≤ R) :
    infiniteGreen (boundaryInterior R) 0 0 =
      1 +
        (∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          infiniteHitMass (boundaryInterior R) (directionVector d) 0) *
        infiniteGreen (boundaryInterior R) 0 0 := by
  calc
    infiniteGreen (boundaryInterior R) 0 0 =
        1 + ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          infiniteGreen (boundaryInterior R) (directionVector d) 0 :=
      infiniteGreen_diagonal_firstStep R hR
    _ = 1 +
        (∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          infiniteHitMass (boundaryInterior R) (directionVector d) 0) *
        infiniteGreen (boundaryInterior R) 0 0 := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [infiniteGreen_eq_hit_mul_diagonal]
      ac_rfl

private def literalReturnMass (R : ℕ) : ℝ≥0∞ :=
  ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
    infiniteHitMass (boundaryInterior R) (directionVector d) 0

private theorem literalReturnMass_ne_top (R : ℕ) :
    literalReturnMass R ≠ ⊤ := by
  unfold literalReturnMass
  exact ENNReal.sum_ne_top.mpr fun d _hd ↦
    ENNReal.mul_ne_top (by norm_num)
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (infiniteHitMass_le_one (boundaryInterior R) (directionVector d) 0))

private theorem infiniteGreen_diagonal_ne_top (R : ℕ) :
    infiniteGreen (boundaryInterior R) 0 0 ≠ ⊤ :=
  infiniteGreen_ne_top_of_subset_coordinateBox
    (boundaryInterior R) R 0 0 (boundaryInterior_subset_coordinateBox R)

private theorem literalReturnMass_toReal (R : ℕ) (hR : 3 ≤ R) :
    (literalReturnMass R).toReal =
      fairSteps.real
        (positiveReturnBeforeBoundary (ThickPoint.discBoundary 0 (R : ℝ))) := by
  rw [positiveReturnBeforeBoundary_probability_eq_neighborAverage R hR]
  unfold literalReturnMass
  rw [ENNReal.toReal_sum (fun d _hd ↦
    ENNReal.mul_ne_top (by norm_num)
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (infiniteHitMass_le_one (boundaryInterior R) (directionVector d) 0)))]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat]

private theorem infiniteGreen_diagonal_toReal_renewal
    (R : ℕ) (hR : 3 ≤ R) :
    (infiniteGreen (boundaryInterior R) 0 0).toReal =
      1 + (literalReturnMass R).toReal *
        (infiniteGreen (boundaryInterior R) 0 0).toReal := by
  have h := congrArg ENNReal.toReal
    (infiniteGreen_diagonal_eq_one_add_return_mul R hR)
  change (infiniteGreen (boundaryInterior R) 0 0).toReal =
    (1 + literalReturnMass R *
      infiniteGreen (boundaryInterior R) 0 0).toReal at h
  rw [ENNReal.toReal_add (by norm_num)
      (ENNReal.mul_ne_top (literalReturnMass_ne_top R)
        (infiniteGreen_diagonal_ne_top R)),
    ENNReal.toReal_one, ENNReal.toReal_mul] at h
  simpa [literalReturnMass] using h

/-- Exact normalization of the literal escape probability by the killed
diagonal Green function. -/
theorem literalEscapeProbability_mul_infiniteGreen_diagonal
    (R : ℕ) (hR : 3 ≤ R) :
    literalEscapeProbability R *
        (infiniteGreen (boundaryInterior R) 0 0).toReal = 1 := by
  have hrenew := infiniteGreen_diagonal_toReal_renewal R hR
  have hreturn := literalReturnMass_toReal R hR
  unfold literalEscapeProbability escapeBeforePositiveReturnProbability
  rw [← hreturn]
  nlinarith

theorem literalEscapeProbability_pos (R : ℕ) (hR : 3 ≤ R) :
    0 < literalEscapeProbability R := by
  have hprod := literalEscapeProbability_mul_infiniteGreen_diagonal R hR
  have hgreen : 0 ≤ (infiniteGreen (boundaryInterior R) 0 0).toReal :=
    ENNReal.toReal_nonneg
  nlinarith

/-- The escape probability is the reciprocal diagonal Green value. -/
theorem literalEscapeProbability_eq_inv_infiniteGreen_diagonal
    (R : ℕ) (hR : 3 ≤ R) :
    literalEscapeProbability R =
      ((infiniteGreen (boundaryInterior R) 0 0).toReal)⁻¹ := by
  have hprod := literalEscapeProbability_mul_infiniteGreen_diagonal R hR
  have hp := literalEscapeProbability_pos R hR
  have hgreen : 0 < (infiniteGreen (boundaryInterior R) 0 0).toReal := by
    nlinarith
  calc
    literalEscapeProbability R =
        literalEscapeProbability R *
          ((infiniteGreen (boundaryInterior R) 0 0).toReal *
            ((infiniteGreen (boundaryInterior R) 0 0).toReal)⁻¹) := by
      rw [mul_inv_cancel₀ hgreen.ne', mul_one]
    _ = (literalEscapeProbability R *
          (infiniteGreen (boundaryInterior R) 0 0).toReal) *
            ((infiniteGreen (boundaryInterior R) 0 0).toReal)⁻¹ := by ring
    _ = ((infiniteGreen (boundaryInterior R) 0 0).toReal)⁻¹ := by
      rw [hprod, one_mul]

/-- Literal hit probability from a specified entrance. -/
def literalHitProbability (R : ℕ) (start : Point) : ℝ :=
  boundaryStoppedHitKernel (ThickPoint.discBoundary 0 (R : ℝ)) 0 start

theorem literalHitProbability_eq_hitMass
    (R : ℕ) {start : Point} (hR : 3 ≤ R)
    (hstart : start ∈ boundaryInterior R) :
    literalHitProbability R start =
      (infiniteHitMass (boundaryInterior R) start 0).toReal := by
  unfold literalHitProbability
  rw [boundaryStoppedHitKernel_eq_boundaryInteriorHitKernel R hstart
    (zero_mem_boundaryInterior R (by omega)),
    simpleRandomWalkFrom_walkHitBeforeExit]

theorem literalHitProbability_nonneg (R : ℕ) (start : Point) :
    0 ≤ literalHitProbability R start := by
  unfold literalHitProbability boundaryStoppedHitKernel
  exact ENNReal.toReal_nonneg

theorem literalHitProbability_le_one (R : ℕ) (start : Point) :
    literalHitProbability R start ≤ 1 := by
  unfold literalHitProbability boundaryStoppedHitKernel
  exact measureReal_le_one

/-- The literal hit probability is `p` times the off-diagonal Green value.
This is the convenient division-free form of `q / p = G_D(start,0)`. -/
theorem literalHitProbability_eq_escape_mul_infiniteGreen
    (R : ℕ) {start : Point} (hR : 3 ≤ R)
    (hstart : start ∈ boundaryInterior R) :
    literalHitProbability R start =
      literalEscapeProbability R *
        (infiniteGreen (boundaryInterior R) start 0).toReal := by
  have hfactor := congrArg ENNReal.toReal
    (infiniteGreen_eq_hit_mul_diagonal (boundaryInterior R) start 0)
  rw [ENNReal.toReal_mul] at hfactor
  rw [literalHitProbability_eq_hitMass R hR hstart]
  rw [hfactor]
  have hnorm := literalEscapeProbability_mul_infiniteGreen_diagonal R hR
  ring_nf at hnorm ⊢
  rw [hnorm]
  ring

theorem literalHitProbability_div_escape_eq_infiniteGreen
    (R : ℕ) {start : Point} (hR : 3 ≤ R)
    (hstart : start ∈ boundaryInterior R) :
    literalHitProbability R start / literalEscapeProbability R =
      (infiniteGreen (boundaryInterior R) start 0).toReal := by
  rw [literalHitProbability_eq_escape_mul_infiniteGreen R hR hstart]
  exact mul_div_cancel_left₀ _ (literalEscapeProbability_pos R hR).ne'

/-! ## Canonical terminal parameters -/

/-- Positive horizontal axis point at integer radius `r`. -/
def axisPoint (r : ℕ) : Point := ((r : ℤ), 0)

theorem axisPoint_mem_discBoundary (r : ℕ) :
    axisPoint r ∈ ThickPoint.discBoundary 0 (r : ℝ) := by
  change axisPoint r ∈ ThickPoint.discBoundary ((0, 0) : Point) (r : ℝ)
  refine ⟨?_, axisPoint (r + 1), ?_, ?_⟩
  · rw [ThickPoint.disc]
    change ThickPoint.latticeDistance 0 (axisPoint r) ≤ (r : ℝ)
    unfold ThickPoint.latticeDistance ThickPoint.squaredDistance axisPoint
    simp
  · rw [ThickPoint.disc]
    change ¬ThickPoint.latticeDistance 0 (axisPoint (r + 1)) ≤ (r : ℝ)
    unfold ThickPoint.latticeDistance ThickPoint.squaredDistance axisPoint
    simp only [show (0 : Point).1 = 0 by rfl,
      show (0 : Point).2 = 0 by rfl, Prod.fst, Prod.snd]
    simp only [sub_self, Int.cast_zero, zero_pow, add_zero, not_le]
    change (r : ℝ) < Real.sqrt
      (((((0 : ℤ) - ((r + 1 : ℕ) : ℤ) : ℤ) : ℝ) ^ 2) + (0 : ℝ) ^ 2)
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
      Real.sqrt_sq_eq_abs]
    norm_num only [Int.cast_sub, Int.cast_zero, Int.cast_natCast,
      Nat.cast_add, Nat.cast_one, zero_sub, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)]
    norm_num
    rw [show (-1 + -(r : ℝ)) = -((r : ℝ) + 1) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
    norm_num
  · unfold ThickPoint.Adjacent axisPoint
    simp

theorem axisPoint_mem_boundaryInterior_power
    (s : ℕ) (hs : 2 ≤ s) :
    axisPoint (s ^ 6) ∈ boundaryInterior (s ^ 9) := by
  have hsep : s ^ 6 - 1 + 2 ≤ s ^ 9 := by
    have hs3 : 2 ^ 3 ≤ s ^ 3 := Nat.pow_le_pow_left hs 3
    have hs6pos : 0 < s ^ 6 := pow_pos (by omega) 6
    have hs6 : 1 ≤ s ^ 6 := by omega
    calc
      s ^ 6 - 1 + 2 = s ^ 6 + 1 := by omega
      _ ≤ s ^ 6 + s ^ 6 := by
        omega
      _ = s ^ 6 * 2 := by ring
      _ ≤ s ^ 6 * s ^ 3 := Nat.mul_le_mul_left _ (by omega)
      _ = s ^ 9 := by ring
  apply centeredInnerBoundary_shift_mem_boundaryInterior
    (center := 0) (z := axisPoint (s ^ 6)) hsep
  have hs6pos : 0 < s ^ 6 := pow_pos (by omega) 6
  have hs6 : 1 ≤ s ^ 6 := by omega
  have hradius : (((s ^ 6 - 1 : ℕ) : ℝ) + 1) = (s ^ 6 : ℕ) := by
    rw [Nat.cast_sub hs6]
    norm_num
  rw [hradius]
  exact axisPoint_mem_discBoundary (s ^ 6)

/-- Literal escape parameter at the HLOZ terminal outer radius `s^9`. -/
def terminalEscapeProbability (s : ℕ) : ℝ :=
  literalEscapeProbability (s ^ 9)

/-- Literal hit parameter from the canonical inner-axis entrance `s^6` to
the target before the terminal outer boundary `s^9`. -/
def terminalHitProbability (s : ℕ) : ℝ :=
  literalHitProbability (s ^ 9) (axisPoint (s ^ 6))

theorem terminalEscapeProbability_pos (s : ℕ) (hs : 2 ≤ s) :
    0 < terminalEscapeProbability s := by
  apply literalEscapeProbability_pos
  have := Nat.pow_le_pow_left hs 9
  norm_num at this ⊢
  omega

theorem terminalEscapeProbability_le_one (s : ℕ) :
    terminalEscapeProbability s ≤ 1 :=
  literalEscapeProbability_le_one _

theorem terminalHitProbability_nonneg (s : ℕ) :
    0 ≤ terminalHitProbability s :=
  literalHitProbability_nonneg _ _

theorem terminalHitProbability_le_one (s : ℕ) :
    terminalHitProbability s ≤ 1 :=
  literalHitProbability_le_one _ _

/-- Exact HLOZ normalization: `q/p` is the off-diagonal Green function from
the canonical `s^6` entrance in the literal `s^9` graph interior. -/
theorem terminalHit_div_escape_eq_infiniteGreen
    (s : ℕ) (hs : 2 ≤ s) :
    terminalHitProbability s / terminalEscapeProbability s =
      (infiniteGreen (boundaryInterior (s ^ 9))
        (axisPoint (s ^ 6)) 0).toReal := by
  apply literalHitProbability_div_escape_eq_infiniteGreen
  · have := Nat.pow_le_pow_left hs 9
    norm_num at this ⊢
    omega
  · exact axisPoint_mem_boundaryInterior_power s hs

theorem euclideanRadius_axisPoint (r : ℕ) :
    euclideanRadius (axisPoint r) = r := by
  unfold euclideanRadius euclideanRadiusSq axisPoint
  simp

/-- Boundary-reference Green window for any literal-disc start, specialized
to the canonical positive-axis outer reference point. -/
theorem abs_infiniteGreen_sub_axisPotentialDifference_le
    (R : ℕ) {start : Point} (hR : 5 ≤ R)
    (hstart : start ∈ boundaryInterior R) :
    |(infiniteGreen (boundaryInterior R) start 0).toReal -
        (planarPotentialKernel (axisPoint R) -
          planarPotentialKernel start)| ≤ literalBoundaryError R := by
  have hbound := abs_infiniteGreen_toReal_sub_boundaryReference_le_of_subset_coordinateBox
    (D := boundaryInterior R) (boxRadius := R) (x := start)
    (target := 0) (q := axisPoint R) hstart
    (boundaryInterior_subset_coordinateBox R)
    (literalBoundaryError_nonneg R) ?_
  · simpa only [sub_zero] using hbound
  · intro z hz
    have hzBoundary := outerBoundary_boundaryInterior_subset_discBoundary R hz
    simpa only [sub_zero] using
      discBoundary_potential_oscillation_le_literalBoundaryError
        hR (axisPoint_mem_discBoundary R) z hzBoundary

/-- Diagonal version of the canonical boundary-reference Green window. -/
theorem abs_infiniteGreen_diagonal_sub_axisPotential_le
    (R : ℕ) (hR : 5 ≤ R) :
    |(infiniteGreen (boundaryInterior R) 0 0).toReal -
        planarPotentialKernel (axisPoint R)| ≤ literalBoundaryError R := by
  have h := abs_infiniteGreen_sub_axisPotentialDifference_le R hR
    (zero_mem_boundaryInterior R (by omega))
  simpa [AnnulusHarnack.planarPotentialKernel_zero] using h

/-- Total explicit error in the terminal off-diagonal Green asymptotic. -/
def terminalOffDiagonalError (s : ℕ) : ℝ :=
  literalBoundaryError (s ^ 9) +
    PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 9 +
    PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6

theorem terminalOffDiagonalError_nonneg (s : ℕ) :
    0 ≤ terminalOffDiagonalError s := by
  unfold terminalOffDiagonalError
  exact add_nonneg
    (add_nonneg (literalBoundaryError_nonneg _)
      (div_nonneg PotentialRadialGlobal.globalRadialConstant_pos.le (by positivity)))
    (div_nonneg PotentialRadialGlobal.globalRadialConstant_pos.le (by positivity))

/-- The exact Green value `q/p` differs from `(6/pi) log s` only by the
explicit radial and literal-boundary errors. -/
theorem abs_terminalGreen_sub_six_div_pi_log_le
    (s : ℕ) (hs : 2 ≤ s) :
    |(infiniteGreen (boundaryInterior (s ^ 9))
          (axisPoint (s ^ 6)) 0).toReal -
        (6 / Real.pi) * Real.log s| ≤ terminalOffDiagonalError s := by
  have hs9 : 5 ≤ s ^ 9 := by
    have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  have hgreen := abs_infiniteGreen_sub_axisPotentialDifference_le
    (s ^ 9) hs9 (axisPoint_mem_boundaryInterior_power s hs)
  have houter :=
    PotentialRadialGlobal.abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      (x := axisPoint (s ^ 9)) (by
        intro h
        have hfirst := congrArg Prod.fst h
        simp [axisPoint] at hfirst
        have : 0 < s ^ 9 := pow_pos (by omega) 9
        omega)
  have hinner :=
    PotentialRadialGlobal.abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      (x := axisPoint (s ^ 6)) (by
        intro h
        have hfirst := congrArg Prod.fst h
        simp [axisPoint] at hfirst
        have : 0 < s ^ 6 := pow_pos (by omega) 6
        omega)
  rw [euclideanRadius_axisPoint, Nat.cast_pow] at houter hinner
  have hsreal : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hlog9 : Real.log ((s : ℝ) ^ 9) = 9 * Real.log s := by
    rw [Real.log_pow]
    norm_num
  have hlog6 : Real.log ((s : ℝ) ^ 6) = 6 * Real.log s := by
    rw [Real.log_pow]
    norm_num
  rw [hlog9] at houter
  rw [hlog6] at hinner
  rw [abs_le] at hgreen houter hinner ⊢
  unfold terminalOffDiagonalError
  ring_nf at houter hinner ⊢
  constructor <;> linarith

/-- Total explicit error in the terminal diagonal Green asymptotic. -/
def terminalDiagonalError (s : ℕ) : ℝ :=
  literalBoundaryError (s ^ 9) +
    PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 9

theorem terminalDiagonalError_nonneg (s : ℕ) :
    0 ≤ terminalDiagonalError s := by
  unfold terminalDiagonalError
  exact add_nonneg (literalBoundaryError_nonneg _)
    (div_nonneg PotentialRadialGlobal.globalRadialConstant_pos.le (by positivity))

theorem abs_terminalDiagonalGreen_sub_log_le
    (s : ℕ) (hs : 2 ≤ s) :
    |(infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal -
        ((18 / Real.pi) * Real.log s +
          PotentialRadialAsymptotic.cPotential)| ≤ terminalDiagonalError s := by
  have hs9 : 5 ≤ s ^ 9 := by
    have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  have hgreen := abs_infiniteGreen_diagonal_sub_axisPotential_le (s ^ 9) hs9
  have houter :=
    PotentialRadialGlobal.abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      (x := axisPoint (s ^ 9)) (by
        intro h
        have hfirst := congrArg Prod.fst h
        simp [axisPoint] at hfirst
        have : 0 < s ^ 9 := pow_pos (by omega) 9
        omega)
  rw [euclideanRadius_axisPoint, Nat.cast_pow, Real.log_pow] at houter
  rw [abs_le] at hgreen houter ⊢
  unfold terminalDiagonalError
  ring_nf at houter ⊢
  constructor <;> linarith

theorem terminalEscapeProbability_inv_eq_diagonalGreen
    (s : ℕ) (hs : 2 ≤ s) :
    (terminalEscapeProbability s)⁻¹ =
      (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal := by
  unfold terminalEscapeProbability
  rw [literalEscapeProbability_eq_inv_infiniteGreen_diagonal]
  · rw [inv_inv]
  · have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega

theorem terminalHitProbability_eq_escape_mul_green
    (s : ℕ) (hs : 2 ≤ s) :
    terminalHitProbability s = terminalEscapeProbability s *
      (infiniteGreen (boundaryInterior (s ^ 9))
        (axisPoint (s ^ 6)) 0).toReal := by
  unfold terminalHitProbability terminalEscapeProbability
  apply literalHitProbability_eq_escape_mul_infiniteGreen
  · have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  · exact axisPoint_mem_boundaryInterior_power s hs

/-- A reusable exact criterion for the terminal hit probability to be at
most one half. -/
theorem terminalHitProbability_le_half_of_two_green_le_diagonal
    (s : ℕ) (hs : 2 ≤ s)
    (hsep : 2 * (infiniteGreen (boundaryInterior (s ^ 9))
        (axisPoint (s ^ 6)) 0).toReal ≤
      (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal) :
    terminalHitProbability s ≤ 1 / 2 := by
  have hp0 : 0 ≤ terminalEscapeProbability s :=
    literalEscapeProbability_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsep hp0
  have hq := terminalHitProbability_eq_escape_mul_green s hs
  have hnorm := literalEscapeProbability_mul_infiniteGreen_diagonal
    (s ^ 9) (by
      have hpow := Nat.pow_le_pow_left hs 9
      norm_num at hpow ⊢
      omega)
  change terminalEscapeProbability s *
      (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal = 1 at hnorm
  calc
    terminalHitProbability s = terminalEscapeProbability s *
        (infiniteGreen (boundaryInterior (s ^ 9))
          (axisPoint (s ^ 6)) 0).toReal := hq
    _ ≤ 1 / 2 := by nlinarith [hmul, hnorm]

/-- Explicit radial sufficient condition for `q ≤ 1/2`. -/
theorem terminalHitProbability_le_half_of_radial_separation
    (s : ℕ) (hs : 2 ≤ s)
    (hsep : 2 * ((6 / Real.pi) * Real.log s +
        terminalOffDiagonalError s) ≤
      (18 / Real.pi) * Real.log s +
        PotentialRadialAsymptotic.cPotential - terminalDiagonalError s) :
    terminalHitProbability s ≤ 1 / 2 := by
  apply terminalHitProbability_le_half_of_two_green_le_diagonal s hs
  have hoff := abs_le.mp (abs_terminalGreen_sub_six_div_pi_log_le s hs)
  have hdiag := abs_le.mp (abs_terminalDiagonalGreen_sub_log_le s hs)
  linarith

/-- The selected terminal block's exact mean is the excursion count times
the off-diagonal Green value. -/
theorem requiredTerminalVisitMean_eq_count_mul_green
    (s : ℕ) (hs : 2 ≤ s) (profileDelta : ℝ) :
    AppendixLocalTime.requiredTerminalVisitMean s profileDelta
        (terminalHitProbability s) (terminalEscapeProbability s) =
      (AppendixLocalTime.requiredTerminalCount s profileDelta : ℝ) *
        (infiniteGreen (boundaryInterior (s ^ 9))
          (axisPoint (s ^ 6)) 0).toReal := by
  unfold AppendixLocalTime.requiredTerminalVisitMean
  rw [div_eq_mul_inv]
  rw [terminalEscapeProbability_inv_eq_diagonalGreen s hs]
  rw [terminalHitProbability_eq_escape_mul_green s hs]
  have hnorm := literalEscapeProbability_mul_infiniteGreen_diagonal
    (s ^ 9) (by
      have hpow := Nat.pow_le_pow_left hs 9
      norm_num at hpow ⊢
      omega)
  change terminalEscapeProbability s *
      (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal = 1 at hnorm
  calc
    (AppendixLocalTime.requiredTerminalCount s profileDelta : ℝ) *
        (terminalEscapeProbability s *
          (infiniteGreen (boundaryInterior (s ^ 9))
            (axisPoint (s ^ 6)) 0).toReal) *
        (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal =
      (AppendixLocalTime.requiredTerminalCount s profileDelta : ℝ) *
        (infiniteGreen (boundaryInterior (s ^ 9))
          (axisPoint (s ^ 6)) 0).toReal *
        (terminalEscapeProbability s *
          (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal) := by ring
    _ = _ := by rw [hnorm]; ring

/-- The exact Bernoulli--geometric variance is bounded by twice the product
of the off-diagonal and diagonal Green values per selected excursion. -/
theorem requiredTerminalVisitVariance_le_two_count_mul_greens
    (s : ℕ) (hs : 2 ≤ s) (profileDelta : ℝ) :
    AppendixLocalTime.requiredTerminalVisitVariance s profileDelta
        (terminalHitProbability s) (terminalEscapeProbability s) ≤
      2 * (AppendixLocalTime.requiredTerminalCount s profileDelta : ℝ) *
        (infiniteGreen (boundaryInterior (s ^ 9))
          (axisPoint (s ^ 6)) 0).toReal *
        (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal := by
  let m : ℝ := AppendixLocalTime.requiredTerminalCount s profileDelta
  let q := terminalHitProbability s
  let p := terminalEscapeProbability s
  let goff := (infiniteGreen (boundaryInterior (s ^ 9))
    (axisPoint (s ^ 6)) 0).toReal
  let gdiag := (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal
  have hm0 : 0 ≤ m := by
    dsimp only [m]
    positivity
  have hq0 : 0 ≤ q := terminalHitProbability_nonneg s
  have hq1 : q ≤ 1 := terminalHitProbability_le_one s
  have hp0 : 0 < p := terminalEscapeProbability_pos s hs
  have hp1 : p ≤ 1 := terminalEscapeProbability_le_one s
  have hratio : q / p = goff := terminalHit_div_escape_eq_infiniteGreen s hs
  have hinv : p⁻¹ = gdiag := terminalEscapeProbability_inv_eq_diagonalGreen s hs
  have hfactor : 2 - p - q ≤ 2 := by linarith
  have hgoff0 : 0 ≤ goff := ENNReal.toReal_nonneg
  have hgdiag0 : 0 ≤ gdiag := ENNReal.toReal_nonneg
  have hprod0 : 0 ≤ m * goff * gdiag := by positivity
  have hid : q * (2 - p - q) / p ^ 2 =
      (q / p) * (2 - p - q) * p⁻¹ := by
    field_simp [hp0.ne']
  unfold AppendixLocalTime.requiredTerminalVisitVariance
  change m * (q * (2 - p - q) / p ^ 2) ≤ 2 * m * goff * gdiag
  rw [hid, hratio, hinv]
  calc
    m * (goff * (2 - p - q) * gdiag) =
        (m * goff * gdiag) * (2 - p - q) := by ring
    _ ≤ (m * goff * gdiag) * 2 :=
      mul_le_mul_of_nonneg_left hfactor hprod0
    _ = 2 * m * goff * gdiag := by ring

/-! ## Eventual half-bound for the canonical hit parameter -/

def terminalErrorConstant : ℝ :=
  13000000002 + 2 * PotentialRadialGlobal.globalRadialConstant

theorem terminalErrorConstant_pos : 0 < terminalErrorConstant := by
  unfold terminalErrorConstant
  linarith [PotentialRadialGlobal.globalRadialConstant_pos]

private theorem literalBoundaryError_le_constant
    {R : ℕ} (hR : 2 ≤ R) : literalBoundaryError R ≤ 13000000002 := by
  unfold literalBoundaryError RadialHarnackSpecialization.euclideanShellError
  have hdenNat : 1 ≤ R - 1 := by omega
  have hden : (1 : ℝ) ≤ (R - 1 : ℕ) := by exact_mod_cast hdenNat
  have hpos : (0 : ℝ) < (R - 1 : ℕ) := lt_of_lt_of_le zero_lt_one hden
  rw [div_le_iff₀ hpos]
  nlinarith

theorem terminalOffDiagonalError_le_constant
    (s : ℕ) (hs : 2 ≤ s) :
    terminalOffDiagonalError s ≤ terminalErrorConstant := by
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hpow9 : (1 : ℝ) ≤ (s : ℝ) ^ 9 := one_le_pow₀ hsreal
  have hpow6 : (1 : ℝ) ≤ (s : ℝ) ^ 6 := one_le_pow₀ hsreal
  have hrad9 : PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 9 ≤
      PotentialRadialGlobal.globalRadialConstant := by
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow9)]
    nlinarith [PotentialRadialGlobal.globalRadialConstant_pos]
  have hrad6 : PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6 ≤
      PotentialRadialGlobal.globalRadialConstant := by
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow6)]
    nlinarith [PotentialRadialGlobal.globalRadialConstant_pos]
  have hs9 : 2 ≤ s ^ 9 := by
    have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  have hboundary := literalBoundaryError_le_constant hs9
  unfold terminalOffDiagonalError terminalErrorConstant
  linarith

theorem terminalDiagonalError_le_constant
    (s : ℕ) (hs : 2 ≤ s) :
    terminalDiagonalError s ≤ terminalErrorConstant := by
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hpow9 : (1 : ℝ) ≤ (s : ℝ) ^ 9 := one_le_pow₀ hsreal
  have hrad9 : PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 9 ≤
      PotentialRadialGlobal.globalRadialConstant := by
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow9)]
    nlinarith [PotentialRadialGlobal.globalRadialConstant_pos]
  have hs9 : 2 ≤ s ^ 9 := by
    have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  have hboundary := literalBoundaryError_le_constant hs9
  unfold terminalDiagonalError terminalErrorConstant
  linarith [PotentialRadialGlobal.globalRadialConstant_pos]

/-- Eventually the canonical terminal point-hit probability is at most one
half.  This is the exact side condition consumed by the terminal visit law. -/
theorem eventually_terminalHitProbability_le_half :
    ∀ᶠ s : ℕ in atTop, terminalHitProbability s ≤ 1 / 2 := by
  have hcoef : 0 < (6 / Real.pi : ℝ) := by positivity
  have htend : Tendsto (fun s : ℕ ↦ (6 / Real.pi) * Real.log s)
      atTop atTop :=
    (Proposition13Scales.tendsto_log_nat_atTop.const_mul_atTop hcoef)
  have hlarge := htend.eventually
    (eventually_ge_atTop
      (3 * terminalErrorConstant - PotentialRadialAsymptotic.cPotential))
  filter_upwards [hlarge, eventually_ge_atTop 2] with s hslog hs
  apply terminalHitProbability_le_half_of_radial_separation s hs
  have hoff := terminalOffDiagonalError_le_constant s hs
  have hdiag := terminalDiagonalError_le_constant s hs
  ring_nf at hslog ⊢
  linarith

/-! ## Quantitative terminal-scale asymptotics -/

/-- A single constant dominating all three radial errors after extracting
the slowest `s⁻⁶` decay. -/
def terminalDecayConstant : ℝ :=
  26000000004 + 2 * PotentialRadialGlobal.globalRadialConstant

theorem terminalDecayConstant_pos : 0 < terminalDecayConstant := by
  unfold terminalDecayConstant
  linarith [PotentialRadialGlobal.globalRadialConstant_pos]

theorem terminalOffDiagonalError_le_decay
    (s : ℕ) (hs : 2 ≤ s) :
    terminalOffDiagonalError s ≤ terminalDecayConstant / (s : ℝ) ^ 6 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hs6 : (0 : ℝ) < (s : ℝ) ^ 6 := pow_pos hsR _
  have hs9 : (0 : ℝ) < (s : ℝ) ^ 9 := pow_pos hsR _
  have hs69 : (s : ℝ) ^ 6 ≤ (s : ℝ) ^ 9 :=
    pow_le_pow_right₀ hs1 (by norm_num)
  have hs9nat : 2 ≤ s ^ 9 := by
    have hpow := Nat.pow_le_pow_left hs 9
    norm_num at hpow ⊢
    omega
  have hcastSub : ((s ^ 9 - 1 : ℕ) : ℝ) = (s : ℝ) ^ 9 - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s ^ 9), Nat.cast_pow]
    norm_num
  have hden : (0 : ℝ) < (s ^ 9 - 1 : ℕ) := by exact_mod_cast (show 0 < s ^ 9 - 1 by omega)
  have hhalf : (s : ℝ) ^ 9 / 2 ≤ (s ^ 9 - 1 : ℕ) := by
    rw [hcastSub]
    have hs9two : (2 : ℝ) ≤ (s : ℝ) ^ 9 := by exact_mod_cast hs9nat
    linarith
  have hboundary : literalBoundaryError (s ^ 9) ≤
      26000000004 / (s : ℝ) ^ 9 := by
    unfold literalBoundaryError RadialHarnackSpecialization.euclideanShellError
    rw [div_le_iff₀ hden, div_mul_eq_mul_div]
    apply (le_div_iff₀ hs9).2
    nlinarith
  have hboundary6 : literalBoundaryError (s ^ 9) ≤
      26000000004 / (s : ℝ) ^ 6 :=
    hboundary.trans (div_le_div_of_nonneg_left (by norm_num) hs6 hs69)
  have hrad9 : PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 9 ≤
      PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6 :=
    div_le_div_of_nonneg_left
      PotentialRadialGlobal.globalRadialConstant_pos.le hs6 hs69
  unfold terminalOffDiagonalError terminalDecayConstant
  rw [add_div]
  have htwo :
      2 * PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6 =
        PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6 +
          PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6 := by ring
  rw [htwo]
  linarith

theorem terminalDiagonalError_le_decay
    (s : ℕ) (hs : 2 ≤ s) :
    terminalDiagonalError s ≤ terminalDecayConstant / (s : ℝ) ^ 6 := by
  have h := terminalOffDiagonalError_le_decay s hs
  unfold terminalOffDiagonalError at h
  unfold terminalDiagonalError
  have hnonneg : 0 ≤ PotentialRadialGlobal.globalRadialConstant / (s : ℝ) ^ 6 :=
    div_nonneg PotentialRadialGlobal.globalRadialConstant_pos.le (by positivity)
  linarith

theorem requiredTerminalCount_lower
    (s : ℕ) (profileDelta : ℝ) :
    ThickPoint.terminalLower s profileDelta ≤
      (AppendixLocalTime.requiredTerminalCount s profileDelta : ℝ) := by
  exact Nat.le_ceil _

theorem requiredTerminalCount_lt_upper
    (s : ℕ) (profileDelta : ℝ)
    (hlower : 0 ≤ ThickPoint.terminalLower s profileDelta) :
    (AppendixLocalTime.requiredTerminalCount s profileDelta : ℝ) <
      ThickPoint.terminalLower s profileDelta + 1 := by
  exact Nat.ceil_lt_add_one hlower

private theorem terminalLower_chosenProfile_nonneg
    (s : ℕ) (hs : 2 ≤ s) :
    0 ≤ ThickPoint.terminalLower s Proposition13Scales.chosenProfileDelta := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hpow : (s : ℝ) ^ (1 + Proposition13Scales.chosenProfileDelta) ≤
      (s : ℝ) ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hsR
    unfold Proposition13Scales.chosenProfileDelta
    norm_num
  have hlog : 0 < Real.log s := Real.log_pos (by exact_mod_cast hs)
  unfold ThickPoint.terminalLower
  exact div_nonneg (by
    rw [Real.rpow_two] at hpow
    linarith [sq_nonneg (s : ℝ)]) (by positivity)

/-- Sharp deterministic order of the selected terminal excursion count.
The ceiling costs at most the final one-third of `s² / log s`. -/
theorem requiredTerminalCount_le_sq_div_log
    (s : ℕ) (hs : 3 ≤ s) :
    (AppendixLocalTime.requiredTerminalCount s
        Proposition13Scales.chosenProfileDelta : ℝ) ≤
      (s : ℝ) ^ 2 / Real.log s := by
  have hs2 : 2 ≤ s := by omega
  have hT0 := terminalLower_chosenProfile_nonneg s hs2
  have hceil := requiredTerminalCount_lt_upper s
    Proposition13Scales.chosenProfileDelta hT0
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hsR3 : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hlog : 0 < Real.log s := Real.log_pos (by exact_mod_cast (show 1 < s by omega))
  have hlogLe : Real.log (s : ℝ) ≤ s := by
    have h := Real.log_le_sub_one_of_pos hsR
    linarith
  have hthreeLog : 3 * Real.log s ≤ (s : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((s : ℝ) - 3)]
  have hone : (1 : ℝ) ≤ (s : ℝ) ^ 2 / (3 * Real.log s) := by
    rw [le_div_iff₀ (by positivity : 0 < 3 * Real.log s)]
    simpa only [one_mul] using hthreeLog
  have hTle : ThickPoint.terminalLower s
      Proposition13Scales.chosenProfileDelta ≤
      2 * (s : ℝ) ^ 2 / (3 * Real.log s) := by
    unfold ThickPoint.terminalLower Proposition13Scales.chosenProfileDelta
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 3 * Real.log s)
    linarith [Real.rpow_nonneg hsR.le (1 + (1 / 5 : ℝ))]
  calc
    (AppendixLocalTime.requiredTerminalCount s
        Proposition13Scales.chosenProfileDelta : ℝ) ≤
        ThickPoint.terminalLower s Proposition13Scales.chosenProfileDelta + 1 :=
      hceil.le
    _ ≤ 2 * (s : ℝ) ^ 2 / (3 * Real.log s) +
        (s : ℝ) ^ 2 / (3 * Real.log s) := by gcongr
    _ = (s : ℝ) ^ 2 / Real.log s := by field_simp; ring

/-- Fixed-scale deterministic margin bound.  Its hypotheses are precisely
the four asymptotic comparisons proved below: radial error decay, logarithmic
outer-radius correction, strict power separation, and growth of the terminal
tail power. -/
theorem requiredHLOZTerminalMargin_ge_quarter_rpow
    (delta : ℝ) (hdelta : 0 < delta) (s : ℕ) (hs : 2 ≤ s)
    (hlog : 1 ≤ Real.log s)
    (herror : terminalOffDiagonalError s ≤ 1 / (s : ℝ) ^ 3)
    (hcorrection : Real.log 16 + 9 * Real.log s ≤
      (1 / 100 : ℝ) * (s : ℝ) ^ Proposition13Scales.chosenThickDelta delta)
    (hbetaPow : (s : ℝ) ^ Proposition13Scales.chosenThickDelta delta ≤ s)
    (hlowerPower :
      (2 / Real.pi) * (s : ℝ) ^ (6 / 5 : ℝ) ≤
        (1 / 4 : ℝ) *
          (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta))
    (honePower : (1 : ℝ) ≤ (1 / 4 : ℝ) *
      (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta)) :
    (1 / 4 : ℝ) *
        (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta) ≤
      AppendixLocalTime.requiredHLOZTerminalMargin s
        Proposition13Scales.chosenProfileDelta
        (Proposition13Scales.chosenThickDelta delta)
        (terminalHitProbability s) (terminalEscapeProbability s) := by
  let x : ℝ := s
  let L : ℝ := Real.log s
  let beta : ℝ := Proposition13Scales.chosenThickDelta delta
  let alpha : ℝ := 1 + beta
  let c : ℝ := Real.log 16 + 9 * L
  let T : ℝ := ThickPoint.terminalLower s Proposition13Scales.chosenProfileDelta
  let m : ℝ := AppendixLocalTime.requiredTerminalCount s
    Proposition13Scales.chosenProfileDelta
  let G : ℝ := (infiniteGreen (boundaryInterior (s ^ 9))
    (axisPoint (s ^ 6)) 0).toReal
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < s by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ s by omega)
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos (by exact_mod_cast hs)
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact terminalLower_chosenProfile_nonneg s hs
  have hmT : T ≤ m := by
    dsimp [T, m]
    exact requiredTerminalCount_lower s Proposition13Scales.chosenProfileDelta
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hGLower : (6 / Real.pi) * L - terminalOffDiagonalError s ≤ G := by
    have h := (abs_le.mp (abs_terminalGreen_sub_six_div_pi_log_le s hs)).1
    dsimp [G, L]
    linarith
  have hpow12 : x ^ (6 / 5 : ℝ) =
      (s : ℝ) ^ (1 + Proposition13Scales.chosenProfileDelta) := by
    dsimp [x]
    unfold Proposition13Scales.chosenProfileDelta
    congr 1
    norm_num
  have hTformula : T =
      (2 * x ^ 2 - x ^ (6 / 5 : ℝ)) / (3 * L) := by
    dsimp [T, x, L]
    unfold ThickPoint.terminalLower Proposition13Scales.chosenProfileDelta
    norm_num
  have hTle : T ≤ x ^ 2 := by
    rw [hTformula]
    have hnum : 2 * x ^ 2 - x ^ (6 / 5 : ℝ) ≤ 2 * x ^ 2 := by
      linarith [Real.rpow_nonneg hx.le (6 / 5 : ℝ)]
    rw [div_le_iff₀ (by positivity : 0 < 3 * L)]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have hTE : T * terminalOffDiagonalError s ≤ 1 := by
    have hE0 := terminalOffDiagonalError_nonneg s
    have hTEle := mul_le_mul hTle herror hE0 (by positivity : 0 ≤ x ^ 2)
    have hx3 : 0 < x ^ 3 := pow_pos hx _
    have hcalc : x ^ 2 * (1 / x ^ 3) = 1 / x := by field_simp
    rw [hcalc] at hTEle
    exact hTEle.trans (by
      rw [div_le_one hx]
      exact hx1)
  have hmeanLower :
      4 / Real.pi * x ^ 2 - (2 / Real.pi) * x ^ (6 / 5 : ℝ) - 1 ≤
        m * G := by
    have hmG : T * G ≤ m * G := mul_le_mul_of_nonneg_right hmT hG0
    have hTG : T * ((6 / Real.pi) * L - terminalOffDiagonalError s) ≤
        T * G := mul_le_mul_of_nonneg_left hGLower hT0
    have hmain : T * ((6 / Real.pi) * L) =
        4 / Real.pi * x ^ 2 - (2 / Real.pi) * x ^ (6 / 5 : ℝ) := by
      rw [hTformula]
      field_simp [hL.ne']
      ring
    calc
      4 / Real.pi * x ^ 2 - (2 / Real.pi) * x ^ (6 / 5 : ℝ) - 1
          ≤ T * ((6 / Real.pi) * L) - T * terminalOffDiagonalError s := by
            rw [hmain]
            linarith
      _ = T * ((6 / Real.pi) * L - terminalOffDiagonalError s) := by ring
      _ ≤ T * G := hTG
      _ ≤ m * G := hmG
  have hbeta0 : 0 < beta := by
    dsimp [beta]
    unfold Proposition13Scales.chosenThickDelta
    linarith [Proposition13Scales.scaleSlack_pos hdelta]
  have hc0 : 0 ≤ c := by
    dsimp [c, L]
    have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
    have hslog := Real.log_nonneg hx1
    positivity
  have hcs : c ≤ x := by
    have hc := hcorrection
    dsimp [c, L, x, beta] at hc hbetaPow ⊢
    nlinarith [Real.rpow_nonneg hx.le
      (Proposition13Scales.chosenThickDelta delta)]
  have hprod : x * x ^ beta = x ^ alpha := by
    dsimp [alpha]
    rw [Real.rpow_add hx, Real.rpow_one]
  have hquadCorrection :
      4 / Real.pi * ((x + c) ^ 2 - x ^ 2) ≤
        (1 / 4 : ℝ) * x ^ alpha := by
    have hcSq : c ^ 2 ≤ x * c := by nlinarith
    have hdiff : (x + c) ^ 2 - x ^ 2 ≤ 3 * x * c := by nlinarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hcoef : 0 ≤ 4 / Real.pi := by positivity
    have h1 := mul_le_mul_of_nonneg_left hdiff hcoef
    have hc : c ≤ (1 / 100 : ℝ) * x ^ beta := by
      simpa [c, L, x, beta] using hcorrection
    have hxc : x * c ≤ (1 / 100 : ℝ) * x ^ alpha := by
      calc
        x * c ≤ x * ((1 / 100 : ℝ) * x ^ beta) := by gcongr
        _ = (1 / 100 : ℝ) * x ^ alpha := by rw [← hprod]; ring
    calc
      4 / Real.pi * ((x + c) ^ 2 - x ^ 2) ≤
          4 / Real.pi * (3 * x * c) := h1
      _ ≤ 4 / Real.pi * (3 * ((1 / 100 : ℝ) * x ^ alpha)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        nlinarith
      _ ≤ (1 / 4 : ℝ) * x ^ alpha := by
        have hxa : 0 ≤ x ^ alpha := Real.rpow_nonneg hx.le _
        have hpithree := Real.pi_gt_three
        have hcoefSmall : 12 / (100 * Real.pi) ≤ (1 / 4 : ℝ) := by
          rw [div_le_iff₀ (by positivity : 0 < 100 * Real.pi)]
          nlinarith
        calc
          4 / Real.pi * (3 * ((1 / 100 : ℝ) * x ^ alpha)) =
              (12 / (100 * Real.pi)) * x ^ alpha := by ring
          _ ≤ (1 / 4 : ℝ) * x ^ alpha := by
            exact mul_le_mul_of_nonneg_right hcoefSmall hxa
  have halpha0 : 0 ≤ alpha := by dsimp [alpha]; linarith
  have houterPow : x ^ alpha ≤ (x + c) ^ alpha :=
    Real.rpow_le_rpow hx.le (by linarith) halpha0
  have hthresholdUpper :
      ThickPoint.thickThreshold s
          (Proposition13Scales.chosenThickDelta delta) ≤
        4 / Real.pi * x ^ 2 +
          (1 / 4 : ℝ) * x ^ alpha - x ^ alpha := by
    have houter : Real.log (ThickPoint.outerScale s) = x + c := by
      rw [Proposition13Scales.log_outerScale (show 0 < s by omega)]
      dsimp [x, c, L]
      ring
    unfold ThickPoint.thickThreshold
    rw [houter]
    change 4 / Real.pi * (x + c) ^ 2 - (x + c) ^ alpha ≤ _
    calc
      4 / Real.pi * (x + c) ^ 2 - (x + c) ^ alpha =
          (4 / Real.pi * x ^ 2 +
            4 / Real.pi * ((x + c) ^ 2 - x ^ 2)) -
              (x + c) ^ alpha := by ring
      _ ≤ (4 / Real.pi * x ^ 2 + (1 / 4 : ℝ) * x ^ alpha) -
            (x + c) ^ alpha := by
        linarith only [hquadCorrection]
      _ ≤ (4 / Real.pi * x ^ 2 + (1 / 4 : ℝ) * x ^ alpha) -
            x ^ alpha := sub_le_sub_left houterPow _
      _ = _ := by ring
  rw [AppendixLocalTime.requiredHLOZTerminalMargin]
  rw [requiredTerminalVisitMean_eq_count_mul_green s hs]
  change (1 / 4 : ℝ) * x ^ alpha ≤ m * G -
    ThickPoint.thickThreshold s (Proposition13Scales.chosenThickDelta delta)
  have hlower : (2 / Real.pi) * x ^ (6 / 5 : ℝ) ≤
      (1 / 4 : ℝ) * x ^ alpha := by
    simpa [x, alpha] using hlowerPower
  have hone : (1 : ℝ) ≤ (1 / 4 : ℝ) * x ^ alpha := by
    simpa [x, alpha] using honePower
  linarith

private theorem chosenThickDelta_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < Proposition13Scales.chosenThickDelta delta := by
  unfold Proposition13Scales.chosenThickDelta
  linarith [Proposition13Scales.scaleSlack_pos hdelta]

private theorem chosenThickDelta_lt_one (delta : ℝ) :
    Proposition13Scales.chosenThickDelta delta < 1 := by
  unfold Proposition13Scales.chosenThickDelta
  linarith [Proposition13Scales.scaleSlack_le_one_hundred delta]

private theorem six_fifths_lt_terminalExponent
    {delta : ℝ} (hdelta : 0 < delta) :
    (6 / 5 : ℝ) < 1 + Proposition13Scales.chosenThickDelta delta := by
  unfold Proposition13Scales.chosenThickDelta
  linarith [Proposition13Scales.scaleSlack_pos hdelta]

private theorem eventually_terminalError_le_inv_cube :
    ∀ᶠ s : ℕ in atTop,
      terminalOffDiagonalError s ≤ 1 / (s : ℝ) ^ 3 := by
  have hlarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop terminalDecayConstant)
  filter_upwards [hlarge, eventually_ge_atTop 2] with s hsC hs
  have hx : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hx1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hx3 : (0 : ℝ) < (s : ℝ) ^ 3 := pow_pos hx _
  have hx6 : (0 : ℝ) < (s : ℝ) ^ 6 := pow_pos hx _
  have hxle3 : (s : ℝ) ≤ (s : ℝ) ^ 3 := by
    simpa using (pow_le_pow_right₀ hx1 (show 1 ≤ 3 by omega))
  have hC3 : terminalDecayConstant ≤ (s : ℝ) ^ 3 := hsC.trans hxle3
  have hdecay := terminalOffDiagonalError_le_decay s hs
  calc
    terminalOffDiagonalError s ≤ terminalDecayConstant / (s : ℝ) ^ 6 := hdecay
    _ ≤ 1 / (s : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ hx6 hx3]
      have hpow : (s : ℝ) ^ 6 = (s : ℝ) ^ 3 * (s : ℝ) ^ 3 := by ring
      rw [hpow]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC3 hx3.le

private theorem eventually_outerLogCorrection_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop,
      Real.log 16 + 9 * Real.log s ≤ (1 / 100 : ℝ) *
        (s : ℝ) ^ Proposition13Scales.chosenThickDelta delta := by
  let beta := Proposition13Scales.chosenThickDelta delta
  have hbeta : 0 < beta := chosenThickDelta_pos hdelta
  have hlogReal := (isLittleO_log_rpow_atTop hbeta).bound
    (show (0 : ℝ) < 1 / 2000 by norm_num)
  have hlog := tendsto_natCast_atTop_atTop.eventually hlogReal
  have hpowTop : Tendsto (fun s : ℕ ↦ (s : ℝ) ^ beta) atTop atTop :=
    (tendsto_rpow_atTop hbeta).comp tendsto_natCast_atTop_atTop
  have hconstant := hpowTop.eventually
    (eventually_ge_atTop (2000 * Real.log 16))
  filter_upwards [hlog, hconstant, eventually_ge_atTop 1] with s hlog hconstant hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlog0 : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
  have hpow0 : 0 ≤ (s : ℝ) ^ beta := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hpow0] at hlog
  have hconst : Real.log 16 ≤ (1 / 2000 : ℝ) * (s : ℝ) ^ beta := by
    linarith
  change Real.log 16 + 9 * Real.log s ≤
    (1 / 100 : ℝ) * (s : ℝ) ^
      Proposition13Scales.chosenThickDelta delta
  change Real.log 16 + 9 * Real.log s ≤
    (1 / 100 : ℝ) * (s : ℝ) ^ beta
  linarith

private theorem eventually_terminalBetaPow_le
    (delta : ℝ) :
    ∀ᶠ s : ℕ in atTop,
      (s : ℝ) ^ Proposition13Scales.chosenThickDelta delta ≤ s := by
  have hreal := Proposition13Scales.eventually_rpow_le_quarter_mul
    (chosenThickDelta_lt_one delta)
  have h := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [h, eventually_ge_atTop 0] with s hs _
  have hs0 : (0 : ℝ) ≤ s := by positivity
  exact hs.trans (by linarith)

private theorem eventually_lowerTerminalPower_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop,
      (2 / Real.pi) * (s : ℝ) ^ (6 / 5 : ℝ) ≤
        (1 / 4 : ℝ) *
          (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta) := by
  have hC : 0 ≤ (8 / Real.pi : ℝ) := by positivity
  have hreal := Proposition13Scales.eventually_const_mul_rpow_le_half_rpow
    (six_fifths_lt_terminalExponent hdelta) hC
  have h := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [h, eventually_ge_atTop 1] with s hs _
  have hpow0 : 0 ≤ (s : ℝ) ^
      (1 + Proposition13Scales.chosenThickDelta delta) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hs
    (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  calc
    (2 / Real.pi) * (s : ℝ) ^ (6 / 5 : ℝ) =
        (1 / 4 : ℝ) *
          ((8 / Real.pi) * (s : ℝ) ^ (6 / 5 : ℝ)) := by ring
    _ ≤ (1 / 4 : ℝ) * ((1 / 2 : ℝ) *
        (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta)) := hscaled
    _ ≤ (1 / 4 : ℝ) *
        (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta) := by
      nlinarith

private theorem eventually_one_le_quarter_terminalPower
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop,
      (1 : ℝ) ≤ (1 / 4 : ℝ) *
        (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta) := by
  have halpha : 0 < 1 + Proposition13Scales.chosenThickDelta delta := by
    linarith [chosenThickDelta_pos hdelta]
  have htop : Tendsto
      (fun s : ℕ ↦ (s : ℝ) ^
        (1 + Proposition13Scales.chosenThickDelta delta)) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp tendsto_natCast_atTop_atTop
  have h := htop.eventually (eventually_ge_atTop 4)
  filter_upwards [h] with s hs
  linarith

/-- The exact terminal Bernoulli--geometric mean exceeds the HLOZ threshold
by a fixed fraction of the strict tail power, eventually in the terminal
scale. -/
theorem eventually_requiredHLOZTerminalMargin_ge :
    ∀ delta : ℝ, 0 < delta →
      ∀ᶠ s : ℕ in atTop,
        (1 / 4 : ℝ) *
            (s : ℝ) ^
              (1 + Proposition13Scales.chosenThickDelta delta) ≤
          AppendixLocalTime.requiredHLOZTerminalMargin s
            Proposition13Scales.chosenProfileDelta
            (Proposition13Scales.chosenThickDelta delta)
            (terminalHitProbability s) (terminalEscapeProbability s) := by
  intro delta hdelta
  have hlog := Proposition13Scales.tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2, hlog,
    eventually_terminalError_le_inv_cube,
    eventually_outerLogCorrection_le hdelta,
    eventually_terminalBetaPow_le delta,
    eventually_lowerTerminalPower_le hdelta,
    eventually_one_le_quarter_terminalPower hdelta]
      with s hs hlog herror hcorrection hbeta hlower hone
  exact requiredHLOZTerminalMargin_ge_quarter_rpow delta hdelta s hs hlog
    herror hcorrection hbeta hlower hone

theorem eventually_requiredHLOZTerminalMargin_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop,
      0 < AppendixLocalTime.requiredHLOZTerminalMargin s
        Proposition13Scales.chosenProfileDelta
        (Proposition13Scales.chosenThickDelta delta)
        (terminalHitProbability s) (terminalEscapeProbability s) := by
  filter_upwards [eventually_requiredHLOZTerminalMargin_ge delta hdelta,
    eventually_ge_atTop 1] with s hmargin hs
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hpowpos : 0 < (s : ℝ) ^
      (1 + Proposition13Scales.chosenThickDelta delta) :=
    Real.rpow_pos_of_pos hspos _
  linarith

/-! ## Terminal variance -/

def terminalOffDiagonalLogConstant : ℝ := 2 + terminalErrorConstant

def terminalDiagonalLogConstant : ℝ :=
  6 + |PotentialRadialAsymptotic.cPotential| + terminalErrorConstant

def terminalVarianceGrowthConstant : ℝ :=
  4 * terminalOffDiagonalLogConstant * terminalDiagonalLogConstant

private theorem terminalOffDiagonalLogConstant_pos :
    0 < terminalOffDiagonalLogConstant := by
  unfold terminalOffDiagonalLogConstant
  linarith [terminalErrorConstant_pos]

private theorem terminalDiagonalLogConstant_pos :
    0 < terminalDiagonalLogConstant := by
  unfold terminalDiagonalLogConstant
  linarith [abs_nonneg PotentialRadialAsymptotic.cPotential,
    terminalErrorConstant_pos]

theorem terminalVarianceGrowthConstant_pos :
    0 < terminalVarianceGrowthConstant := by
  unfold terminalVarianceGrowthConstant
  exact mul_pos (mul_pos (by norm_num) terminalOffDiagonalLogConstant_pos)
    terminalDiagonalLogConstant_pos

private theorem requiredTerminalCount_le_two_sq
    (s : ℕ) (hs : 2 ≤ s) (hlog : 1 ≤ Real.log s) :
    (AppendixLocalTime.requiredTerminalCount s
        Proposition13Scales.chosenProfileDelta : ℝ) ≤
      2 * (s : ℝ) ^ 2 := by
  have hT0 := terminalLower_chosenProfile_nonneg s hs
  have hceil := requiredTerminalCount_lt_upper s
    Proposition13Scales.chosenProfileDelta hT0
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hpow : (s : ℝ) ^ (1 + Proposition13Scales.chosenProfileDelta) ≤
      (s : ℝ) ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ s by omega))
    unfold Proposition13Scales.chosenProfileDelta
    norm_num
  have hTle : ThickPoint.terminalLower s
      Proposition13Scales.chosenProfileDelta ≤ (s : ℝ) ^ 2 := by
    unfold ThickPoint.terminalLower Proposition13Scales.chosenProfileDelta
    rw [div_le_iff₀ (by positivity : 0 < 3 * Real.log s)]
    rw [Real.rpow_two] at hpow
    have hs2 : 1 ≤ (s : ℝ) ^ 2 := one_le_pow₀
      (by exact_mod_cast (show 1 ≤ s by omega))
    calc
      2 * (s : ℝ) ^ 2 -
          (s : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤ 2 * (s : ℝ) ^ 2 := by
        linarith [Real.rpow_nonneg hsR.le (1 + (1 / 5 : ℝ))]
      _ ≤ (s : ℝ) ^ 2 * (3 * Real.log s) := by nlinarith
  have hs2 : 1 ≤ (s : ℝ) ^ 2 := one_le_pow₀
    (by exact_mod_cast (show 1 ≤ s by omega))
  linarith

private theorem terminalOffDiagonalGreen_le_log
    (s : ℕ) (hs : 2 ≤ s) (hlog : 1 ≤ Real.log s) :
    (infiniteGreen (boundaryInterior (s ^ 9))
        (axisPoint (s ^ 6)) 0).toReal ≤
      terminalOffDiagonalLogConstant * Real.log s := by
  have hupper := (abs_le.mp
    (abs_terminalGreen_sub_six_div_pi_log_le s hs)).2
  have herr := terminalOffDiagonalError_le_constant s hs
  have hcoef : 6 / Real.pi ≤ (2 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hlog0 : 0 ≤ Real.log s := le_trans zero_le_one hlog
  unfold terminalOffDiagonalLogConstant
  nlinarith [terminalErrorConstant_pos]

private theorem terminalDiagonalGreen_le_log
    (s : ℕ) (hs : 2 ≤ s) (hlog : 1 ≤ Real.log s) :
    (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal ≤
      terminalDiagonalLogConstant * Real.log s := by
  have hupper := (abs_le.mp (abs_terminalDiagonalGreen_sub_log_le s hs)).2
  have herr := terminalDiagonalError_le_constant s hs
  have hcoef : 18 / Real.pi ≤ (6 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hc := le_abs_self PotentialRadialAsymptotic.cPotential
  have hlog0 : 0 ≤ Real.log s := le_trans zero_le_one hlog
  unfold terminalDiagonalLogConstant
  nlinarith [terminalErrorConstant_pos,
    abs_nonneg PotentialRadialAsymptotic.cPotential]

/-- Crude but uniform variance growth.  The exact `O(s² log² s)` order is
what is needed against the squared terminal margin. -/
theorem requiredTerminalVisitVariance_le_growth
    (s : ℕ) (hs : 2 ≤ s) (hlog : 1 ≤ Real.log s) :
    AppendixLocalTime.requiredTerminalVisitVariance s
        Proposition13Scales.chosenProfileDelta
        (terminalHitProbability s) (terminalEscapeProbability s) ≤
      terminalVarianceGrowthConstant * (s : ℝ) ^ 2 *
        (Real.log s) ^ 2 := by
  have hvar := requiredTerminalVisitVariance_le_two_count_mul_greens
    s hs Proposition13Scales.chosenProfileDelta
  have hm := requiredTerminalCount_le_two_sq s hs hlog
  have hgo := terminalOffDiagonalGreen_le_log s hs hlog
  have hgd := terminalDiagonalGreen_le_log s hs hlog
  have hm0 : 0 ≤ (AppendixLocalTime.requiredTerminalCount s
      Proposition13Scales.chosenProfileDelta : ℝ) := by positivity
  have hgo0 : 0 ≤ (infiniteGreen (boundaryInterior (s ^ 9))
      (axisPoint (s ^ 6)) 0).toReal := by positivity
  have hgd0 : 0 ≤ (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal := by
    positivity
  have hlog0 : 0 ≤ Real.log s := le_trans zero_le_one hlog
  have hco0 : 0 ≤ terminalOffDiagonalLogConstant * Real.log s :=
    mul_nonneg terminalOffDiagonalLogConstant_pos.le hlog0
  have hcd0 : 0 ≤ terminalDiagonalLogConstant * Real.log s :=
    mul_nonneg terminalDiagonalLogConstant_pos.le hlog0
  calc
    AppendixLocalTime.requiredTerminalVisitVariance s
        Proposition13Scales.chosenProfileDelta
        (terminalHitProbability s) (terminalEscapeProbability s) ≤
      2 * (AppendixLocalTime.requiredTerminalCount s
          Proposition13Scales.chosenProfileDelta : ℝ) *
        (infiniteGreen (boundaryInterior (s ^ 9))
          (axisPoint (s ^ 6)) 0).toReal *
        (infiniteGreen (boundaryInterior (s ^ 9)) 0 0).toReal := hvar
    _ ≤ 2 * (2 * (s : ℝ) ^ 2) *
        (terminalOffDiagonalLogConstant * Real.log s) *
        (terminalDiagonalLogConstant * Real.log s) := by
      gcongr
    _ = terminalVarianceGrowthConstant * (s : ℝ) ^ 2 *
        (Real.log s) ^ 2 := by
      unfold terminalVarianceGrowthConstant
      ring

private theorem terminalVariancePowerGap_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    0 < 2 * (1 + Proposition13Scales.chosenThickDelta delta) - 3 := by
  unfold Proposition13Scales.chosenThickDelta
  linarith [Proposition13Scales.scaleSlack_pos hdelta]

private theorem eventually_varianceGrowth_le_terminalPower
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop,
      terminalVarianceGrowthConstant * (s : ℝ) ^ 2 *
          (Real.log s) ^ 2 ≤
        (1 / 16 : ℝ) *
          (s : ℝ) ^
            (2 * (1 + Proposition13Scales.chosenThickDelta delta) - 1) := by
  let gamma := 2 * (1 + Proposition13Scales.chosenThickDelta delta) - 3
  let C := terminalVarianceGrowthConstant
  have hgamma : 0 < gamma := terminalVariancePowerGap_pos hdelta
  have hC : 0 < C := terminalVarianceGrowthConstant_pos
  have hsmallReal := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hgamma).bound
    (show 0 < (1 / (32 * (C + 1)) : ℝ) by positivity)
  have hsmall := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop 2] with s hsmall hs
  have hx : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hlog0 : 0 ≤ Real.log (s : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ s by omega))
  have hpow0 : 0 ≤ (s : ℝ) ^ gamma := Real.rpow_nonneg hx.le _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 (2 : ℝ)),
    Real.norm_of_nonneg hpow0] at hsmall
  have hlogSq : (Real.log s) ^ 2 = (Real.log (s : ℝ)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
  rw [hlogSq]
  have hClog : C * (Real.log (s : ℝ)) ^ (2 : ℝ) ≤
      (1 / 16 : ℝ) * (s : ℝ) ^ gamma := by
    have hmul := mul_le_mul_of_nonneg_left hsmall hC.le
    calc
      C * (Real.log (s : ℝ)) ^ (2 : ℝ) ≤
          C * ((1 / (32 * (C + 1)) : ℝ) * (s : ℝ) ^ gamma) := hmul
      _ ≤ (1 / 16 : ℝ) * (s : ℝ) ^ gamma := by
        have hratio : C * (1 / (32 * (C + 1))) ≤ (1 / 16 : ℝ) := by
          rw [div_eq_mul_inv]
          field_simp
          linarith
        calc
          C * ((1 / (32 * (C + 1)) : ℝ) * (s : ℝ) ^ gamma) =
              (C * (1 / (32 * (C + 1)))) * (s : ℝ) ^ gamma := by ring
          _ ≤ (1 / 16 : ℝ) * (s : ℝ) ^ gamma :=
            mul_le_mul_of_nonneg_right hratio hpow0
  have hpowerSplit : (s : ℝ) ^
      (2 * (1 + Proposition13Scales.chosenThickDelta delta) - 1) =
      (s : ℝ) ^ 2 * (s : ℝ) ^ gamma := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hx]
    dsimp [gamma]
    congr 1
    ring
  rw [hpowerSplit]
  dsimp [C] at hClog ⊢
  nlinarith [sq_nonneg (s : ℝ)]

private theorem variance_div_margin_sq_le_inv_of_power_bounds
    {delta : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hmargin : (1 / 4 : ℝ) *
        (s : ℝ) ^ (1 + Proposition13Scales.chosenThickDelta delta) ≤
      AppendixLocalTime.requiredHLOZTerminalMargin s
        Proposition13Scales.chosenProfileDelta
        (Proposition13Scales.chosenThickDelta delta)
        (terminalHitProbability s) (terminalEscapeProbability s))
    (hvariance :
      AppendixLocalTime.requiredTerminalVisitVariance s
          Proposition13Scales.chosenProfileDelta
          (terminalHitProbability s) (terminalEscapeProbability s) ≤
        (1 / 16 : ℝ) *
          (s : ℝ) ^
            (2 * (1 + Proposition13Scales.chosenThickDelta delta) - 1)) :
    AppendixLocalTime.requiredTerminalVisitVariance s
          Proposition13Scales.chosenProfileDelta
          (terminalHitProbability s) (terminalEscapeProbability s) /
        (AppendixLocalTime.requiredHLOZTerminalMargin s
          Proposition13Scales.chosenProfileDelta
          (Proposition13Scales.chosenThickDelta delta)
          (terminalHitProbability s) (terminalEscapeProbability s)) ^ 2 ≤
      (s : ℝ)⁻¹ := by
  let x : ℝ := s
  let alpha : ℝ := 1 + Proposition13Scales.chosenThickDelta delta
  let Q : ℝ := (1 / 4 : ℝ) * x ^ alpha
  let M : ℝ := AppendixLocalTime.requiredHLOZTerminalMargin s
    Proposition13Scales.chosenProfileDelta
    (Proposition13Scales.chosenThickDelta delta)
    (terminalHitProbability s) (terminalEscapeProbability s)
  let V : ℝ := AppendixLocalTime.requiredTerminalVisitVariance s
    Proposition13Scales.chosenProfileDelta
    (terminalHitProbability s) (terminalEscapeProbability s)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < s by omega)
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hx _)
  have hQM : Q ≤ M := by simpa [Q, M, x, alpha] using hmargin
  have hMpos : 0 < M := hQpos.trans_le hQM
  have hsq : Q ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ hQpos.le hQM 2
  have hpowSq : (x ^ alpha) ^ 2 = x ^ (2 * alpha) := by
    calc
      (x ^ alpha) ^ 2 = (x ^ alpha) ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = x ^ (alpha * 2) := (Real.rpow_mul hx.le alpha 2).symm
      _ = x ^ (2 * alpha) := by ring_nf
  have hpowSplit : x ^ (2 * alpha) = x ^ (2 * alpha - 1) * x := by
    calc
      x ^ (2 * alpha) = x ^ ((2 * alpha - 1) + 1) := by ring_nf
      _ = x ^ (2 * alpha - 1) * x ^ (1 : ℝ) := Real.rpow_add hx _ _
      _ = x ^ (2 * alpha - 1) * x := by rw [Real.rpow_one]
  have hnormalize : x⁻¹ * Q ^ 2 =
      (1 / 16 : ℝ) * x ^ (2 * alpha - 1) := by
    dsimp [Q]
    rw [mul_pow, hpowSq, hpowSplit]
    have hxinv : x⁻¹ * x = 1 := inv_mul_cancel₀ hx.ne'
    rw [show ((1 / 4 : ℝ) ^ 2) = 1 / 16 by norm_num]
    calc
      x⁻¹ * (1 / 16 * (x ^ (2 * alpha - 1) * x)) =
          (1 / 16 * x ^ (2 * alpha - 1)) * (x⁻¹ * x) := by ring
      _ = (1 / 16 : ℝ) * x ^ (2 * alpha - 1) := by rw [hxinv, mul_one]
  have hV : V ≤ (1 / 16 : ℝ) * x ^ (2 * alpha - 1) := by
    simpa [V, x, alpha] using hvariance
  change V / M ^ 2 ≤ x⁻¹
  rw [div_le_iff₀ (sq_pos_of_pos hMpos)]
  calc
    V ≤ (1 / 16 : ℝ) * x ^ (2 * alpha - 1) := hV
    _ = x⁻¹ * Q ^ 2 := hnormalize.symm
    _ ≤ x⁻¹ * M ^ 2 := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hx.le)

/-- Exact concentration ratio required by the terminal thick-point adapter,
eventually in the terminal scale. -/
theorem eventually_requiredTerminalVariance_div_margin_sq_le_inv
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop,
      AppendixLocalTime.requiredTerminalVisitVariance s
          Proposition13Scales.chosenProfileDelta
          (terminalHitProbability s) (terminalEscapeProbability s) /
        (AppendixLocalTime.requiredHLOZTerminalMargin s
          Proposition13Scales.chosenProfileDelta
          (Proposition13Scales.chosenThickDelta delta)
          (terminalHitProbability s) (terminalEscapeProbability s)) ^ 2 ≤
      (s : ℝ)⁻¹ := by
  have hlog := Proposition13Scales.tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 2, hlog,
    eventually_requiredHLOZTerminalMargin_ge delta hdelta,
    eventually_varianceGrowth_le_terminalPower hdelta]
      with s hs hlog hmargin hgrowth
  have hvariance := (requiredTerminalVisitVariance_le_growth s hs hlog).trans hgrowth
  exact variance_div_margin_sq_le_inv_of_power_bounds (show 1 ≤ s by omega)
    hmargin hvariance

/-! ## Packaged certificate and substitution of the HLOZ scale index -/

/-- All exact numerical hypotheses on the canonical terminal hit/escape
parameters used by `AppendixTerminalThick`. -/
structure TerminalParameterCertificate (delta : ℝ) (s : ℕ) : Prop where
  scale_ge_four : 4 ≤ s
  hit_nonneg : 0 ≤ terminalHitProbability s
  hit_le_half : terminalHitProbability s ≤ 1 / 2
  escape_pos : 0 < terminalEscapeProbability s
  escape_le_one : terminalEscapeProbability s ≤ 1
  margin_pos :
    0 < AppendixLocalTime.requiredHLOZTerminalMargin s
      Proposition13Scales.chosenProfileDelta
      (Proposition13Scales.chosenThickDelta delta)
      (terminalHitProbability s) (terminalEscapeProbability s)
  variance_ratio :
    AppendixLocalTime.requiredTerminalVisitVariance s
        Proposition13Scales.chosenProfileDelta
        (terminalHitProbability s) (terminalEscapeProbability s) /
      (AppendixLocalTime.requiredHLOZTerminalMargin s
        Proposition13Scales.chosenProfileDelta
        (Proposition13Scales.chosenThickDelta delta)
        (terminalHitProbability s) (terminalEscapeProbability s)) ^ 2 ≤
      (s : ℝ)⁻¹

theorem TerminalParameterCertificate.hit_le_one
    {delta : ℝ} {s : ℕ} (h : TerminalParameterCertificate delta s) :
    terminalHitProbability s ≤ 1 := by
  linarith [h.hit_le_half]

/-- Canonical terminal numerical parameters are valid at all sufficiently
large terminal scales. -/
theorem eventually_terminalParameterCertificate
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ s : ℕ in atTop, TerminalParameterCertificate delta s := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_terminalHitProbability_le_half,
    eventually_requiredHLOZTerminalMargin_pos hdelta,
    eventually_requiredTerminalVariance_div_margin_sq_le_inv hdelta]
      with s hs hhalf hmargin hratio
  exact
    { scale_ge_four := hs
      hit_nonneg := terminalHitProbability_nonneg s
      hit_le_half := hhalf
      escape_pos := terminalEscapeProbability_pos s (by omega)
      escape_le_one := terminalEscapeProbability_le_one s
      margin_pos := hmargin
      variance_ratio := hratio }

/-- The packaged certificate at the actual rounded HLOZ terminal scale
`scaleIndex delta n`. -/
theorem eventually_terminalParameterCertificate_scaleIndex
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      TerminalParameterCertificate delta
        (Proposition13Scales.scaleIndex delta n) := by
  have hscaleTop : Tendsto (Proposition13Scales.scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp
      (Proposition13Scales.tendsto_scaleIndex_atTop delta)
  exact hscaleTop.eventually (eventually_terminalParameterCertificate hdelta)







end

end Erdos1165.TerminalParameterBounds

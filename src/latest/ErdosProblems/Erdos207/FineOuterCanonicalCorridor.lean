/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterPowerSandwich
import ErdosProblems.Erdos207.FineOuterCanonicalScalars

/-!
# The canonical coupled outer corridor

This module assembles the clock, power-window, and scalar estimates proved in
the preceding files.  It is the first theorem in the outer-stage chain whose
hypotheses are entirely integral power inequalities and the two already-known
time-zero offset bounds.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- The canonical reserve `outside² / t` and inverse-clock window trap both
recursive pair-degree schedules until the reserve is reached. -/
theorem outerSharpRecursiveSchedules_between_fineCanonicalBarriers
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t K : ℕ)
    (houtside : 0 < outside) (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hsmallPower : 12800 ≤ t ^ 31)
    (hoffsetPower : t ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower : 50 * t ^ 101 ≤ outside ^ 2)
    (haggregatePower : t ^ 102 * K ≤ 8 * outside ^ 2)
    (hinitialOrder : lower₀ ≤ outside)
    (hinitial :
      (outside : ℝ) ≤
          quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
              fineOuterInitialOffset outside t ∧
        quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
              fineOuterInitialOffset outside t ≤ (lower₀ : ℝ))
    (hfour : 4 ≤ fineOuterReserve outside t) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    let A := fineOuterInitialOffset outside t *
      (outerSharpEligiblePairs H X 0 : ℝ) ^ coupledOuterExponent
    ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ≤
        nonnegativeNatCeil
          (outerCoupledUpperBarrier H X outside A coupledOuterExponent i +
            fineOuterBuffer outside t) ∧
      nonnegativeNatFloor
          (outerCoupledLowerBarrier H X outside A coupledOuterExponent i -
            fineOuterBuffer outside t) ≤
        outerSharpLowerSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
      outerSharpLowerSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ≤
        outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i := by
  dsimp only
  let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
  let A := fineOuterInitialOffset outside t *
    (outerSharpEligiblePairs H X 0 : ℝ) ^ coupledOuterExponent
  have hE0 : 0 < outerSharpEligiblePairs H X 0 :=
    hreservePos.trans_le hreserveInitial
  have hcoupledInitial := fineOffset_initial_bounds_to_coupled
    H X outside lower₀ t coupledOuterExponent hE0
    (show fineOuterCorridorError t ≤ 4 by
      have hsmall : fineOuterCorridorError t ≤ 1 := by
        unfold fineOuterCorridorError
        exact pow_le_one₀ (show (0 : ℝ≥0) ≤ (t : ℝ≥0)⁻¹ by positivity)
          (inv_le_one_of_one_le₀ (by exact_mod_cast ht))
      exact hsmall.trans (by norm_num))
    hinitial
  have hA : 0 ≤ A := by
    dsimp only [A, fineOuterInitialOffset]
    positivity
  have hbuffer : 0 ≤ fineOuterBuffer outside t := by
    unfold fineOuterBuffer fineOuterInitialOffset
    positivity
  have hclock : 3 * (fuel + 1) < outerSharpEligiblePairs H X 0 := by
    dsimp only [fuel]
    exact canonicalStopFuel_clock H X hreserveInitial hfour
  let z : ℕ → ℝ := fun i ↦
    outerCoupledWindow H X A coupledOuterExponent i /
      outerCoupledCenter H X outside i
  apply outerSharpRecursiveSchedules_between_coupledBarriers H X
    outside lower₀ outside K fuel coupledOuterExponent
    (fineOuterBuffer outside t) A z houtside hA
    coupledOuterExponent_growth hbuffer hinitialOrder
  · simpa only [A] using hcoupledInitial.1
  · simpa only [A] using hcoupledInitial.2
  · exact hclock
  · intro i hi
    have hclockFacts := fineOuterCanonicalClockFacts H X outside t i ht
      hreservePos hreserveInitial (by
        dsimp only [fuel] at hi
        exact Nat.le_of_lt hi) hpairUpper
    have hscalars := fineOuterCanonicalScalars H X outside t K i
      houtside ht hclockFacts.lower_clock hsmallPower hoffsetPower
      hclockPower haggregatePower
    dsimp only [z]
    apply coupledOuterScaleFacts_of_power H X outside t K
      coupledOuterExponent i (fineOuterBuffer outside t) (t : ℝ)
      houtside (by exact_mod_cast ht) hclockFacts.current_pos
      hclockFacts.current_le_initial hclockFacts.compare
      hclockFacts.lower_clock hclockFacts.upper_clock
    · exact hscalars.small
    · exact hscalars.round_buffer
    · exact hscalars.round_two
    · exact hscalars.lower_one
    · exact hscalars.clock
    · exact hscalars.aggregate

end

end Erdos207

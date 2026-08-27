/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpRecursiveSchedules

/-!
# Barrier comparison for recursive sharp schedules

The exact recursive envelopes may be compared with any explicit pair of
real barriers.  This is the discrete differential-equation interface used
for the long initial phase: later arithmetic can work with closed quadratic
barriers without unfolding the recursion.
-/

namespace Erdos207

noncomputable section

/-- Sub- and super-solutions for the two scalar recurrences trap the exact
recursive upper and lower envelopes. -/
theorem sharpPairEnvelope_between_barriers
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (upperBarrier lowerBarrier : ℕ → ℝ)
    (hupper₀ : upper₀ ≤ upperBarrier 0)
    (hlower₀ : lowerBarrier 0 ≤ lower₀)
    (hupperStep : ∀ i,
      upperBarrier i - upperBarrier (i + 1) ≤
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i))
    (hlowerStep : ∀ i,
      sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc ≤
        lowerBarrier i - lowerBarrier (i + 1)) :
    ∀ i,
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 ≤
          upperBarrier i ∧
        lowerBarrier i ≤
          (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 := by
  intro i
  induction i with
  | zero =>
      simpa only [sharpPairEnvelope_zero] using And.intro hupper₀ hlower₀
  | succ i ih =>
      rw [sharpPairEnvelope_upper_succ, sharpPairEnvelope_lower_succ]
      constructor
      · have hs := hupperStep i
        linarith [ih.1]
      · have hs := hlowerStep i
        linarith [ih.2]

/-- The trapped real envelopes give the corresponding natural ceiling and
floor bounds used by the stopped process. -/
theorem sharpRecursiveSchedules_between_barriers
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (upperBarrier lowerBarrier : ℕ → ℝ)
    (hupper₀ : upper₀ ≤ upperBarrier 0)
    (hlower₀ : lowerBarrier 0 ≤ lower₀)
    (hupperStep : ∀ i,
      upperBarrier i - upperBarrier (i + 1) ≤
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i))
    (hlowerStep : ∀ i,
      sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc ≤
        lowerBarrier i - lowerBarrier (i + 1)) :
    ∀ i,
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) ∧
        nonnegativeNatFloor (lowerBarrier i - buffer) ≤
      sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i := by
  intro i
  have henv := sharpPairEnvelope_between_barriers upper₀ lower₀ buffer Kinc
    Dof Mof upperBarrier lowerBarrier hupper₀ hlower₀ hupperStep hlowerStep i
  constructor
  · unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
    apply Nat.ceil_mono
    apply max_le_max_left
    simpa only [add_comm] using add_le_add_right henv.1 buffer
  · unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
    apply Nat.floor_mono
    exact max_le_max_left _ (sub_le_sub_right henv.2 buffer)

/-- Finite-horizon form of `sharpPairEnvelope_between_barriers`.  This is
the form needed for explicit barriers which are only positive until the
prescribed stopping time. -/
theorem sharpPairEnvelope_between_barriers_until
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (upperBarrier lowerBarrier : ℕ → ℝ)
    (hupper₀ : upper₀ ≤ upperBarrier 0)
    (hlower₀ : lowerBarrier 0 ≤ lower₀)
    (hupperStep : ∀ i, i < fuel →
      upperBarrier i - upperBarrier (i + 1) ≤
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i))
    (hlowerStep : ∀ i, i < fuel →
      sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc ≤
        lowerBarrier i - lowerBarrier (i + 1)) :
    ∀ i, i ≤ fuel →
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 ≤
          upperBarrier i ∧
        lowerBarrier i ≤
          (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 := by
  intro i hi
  induction i with
  | zero =>
      simpa only [sharpPairEnvelope_zero] using And.intro hupper₀ hlower₀
  | succ i ih =>
      have hi' : i < fuel := by omega
      have ih' := ih (Nat.le_of_lt hi')
      rw [sharpPairEnvelope_upper_succ, sharpPairEnvelope_lower_succ]
      constructor
      · linarith [ih'.1, hupperStep i hi']
      · linarith [ih'.2, hlowerStep i hi']

/-- Finite-horizon natural schedule bounds obtained from explicit real
barriers. -/
theorem sharpRecursiveSchedules_between_barriers_until
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (upperBarrier lowerBarrier : ℕ → ℝ)
    (hupper₀ : upper₀ ≤ upperBarrier 0)
    (hlower₀ : lowerBarrier 0 ≤ lower₀)
    (hupperStep : ∀ i, i < fuel →
      upperBarrier i - upperBarrier (i + 1) ≤
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i))
    (hlowerStep : ∀ i, i < fuel →
      sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc ≤
        lowerBarrier i - lowerBarrier (i + 1)) :
    ∀ i, i ≤ fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) ∧
        nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i := by
  intro i hi
  have henv := sharpPairEnvelope_between_barriers_until upper₀ lower₀ buffer
    Kinc fuel Dof Mof upperBarrier lowerBarrier hupper₀ hlower₀
    hupperStep hlowerStep i hi
  constructor
  · unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
    apply Nat.ceil_mono
    apply max_le_max_left
    simpa only [add_comm] using add_le_add_right henv.1 buffer
  · unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
    apply Nat.floor_mono
    exact max_le_max_left _ (sub_le_sub_right henv.2 buffer)

/-- A self-certifying finite barrier comparison.  At clock `i`, the step
estimates may use the natural floor/ceiling bounds already supplied by the
barriers at that clock.  This is the non-circular induction principle used
for rounded explicit schedules. -/
theorem sharpRecursiveSchedules_between_barriers_until_of_box
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (upperBarrier lowerBarrier : ℕ → ℝ)
    (hupper₀ : upper₀ ≤ upperBarrier 0)
    (hlower₀ : lowerBarrier 0 ≤ lower₀)
    (hupperStep : ∀ i, i < fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      upperBarrier i - upperBarrier (i + 1) ≤
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i))
    (hlowerStep : ∀ i, i < fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc ≤
        lowerBarrier i - lowerBarrier (i + 1)) :
    ∀ i, i ≤ fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) ∧
        nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i := by
  have henv : ∀ i, i ≤ fuel →
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 ≤
          upperBarrier i ∧
        lowerBarrier i ≤
          (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 := by
    intro i hi
    induction i with
    | zero =>
        simpa only [sharpPairEnvelope_zero] using And.intro hupper₀ hlower₀
    | succ i ih =>
        have hi' : i < fuel := by omega
        have ih' := ih (Nat.le_of_lt hi')
        have hu : sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc
            Dof Mof i ≤ nonnegativeNatCeil (upperBarrier i + buffer) := by
          unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
          apply Nat.ceil_mono
          apply max_le_max_left
          simpa only [add_comm] using add_le_add_right ih'.1 buffer
        have hd : nonnegativeNatFloor (lowerBarrier i - buffer) ≤
            sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc
              Dof Mof i := by
          unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
          apply Nat.floor_mono
          exact max_le_max_left _ (sub_le_sub_right ih'.2 buffer)
        rw [sharpPairEnvelope_upper_succ, sharpPairEnvelope_lower_succ]
        constructor
        · linarith [hupperStep i hi' hu hd]
        · linarith [hlowerStep i hi' hu hd]
  intro i hi
  have hiEnv := henv i hi
  constructor
  · unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
    apply Nat.ceil_mono
    apply max_le_max_left
    simpa only [add_comm] using add_le_add_right hiEnv.1 buffer
  · unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
    apply Nat.floor_mono
    exact max_le_max_left _ (sub_le_sub_right hiEnv.2 buffer)

/-- Ordered self-certifying barriers.  Besides trapping both schedules, this
version propagates the fact that the lower natural schedule does not exceed
the upper one.  The propagation uses exactly the expected ordering of the
two conservative deletion rates. -/
theorem sharpRecursiveSchedules_between_barriers_until_of_box_ordered
    (upper₀ lower₀ buffer : ℝ) (Kinc fuel : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (upperBarrier lowerBarrier : ℕ → ℝ)
    (hbuffer : 0 ≤ buffer)
    (horder₀ : lower₀ ≤ upper₀)
    (hupper₀ : upper₀ ≤ upperBarrier 0)
    (hlower₀ : lowerBarrier 0 ≤ lower₀)
    (hupperStep : ∀ i, i < fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      upperBarrier i - upperBarrier (i + 1) ≤
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i))
    (hlowerStep : ∀ i, i < fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc ≤
        lowerBarrier i - lowerBarrier (i + 1))
    (hrateOrder : ∀ i, i < fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i →
      sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i) ≤
        sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc
            Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc) :
    ∀ i, i ≤ fuel →
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          nonnegativeNatCeil (upperBarrier i + buffer) ∧
        nonnegativeNatFloor (lowerBarrier i - buffer) ≤
          sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i ∧
        sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
          sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i := by
  have henv : ∀ i, i ≤ fuel →
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 ≤
          upperBarrier i ∧
        lowerBarrier i ≤
          (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 ∧
        (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 ≤
          (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 := by
    intro i hi
    induction i with
    | zero =>
        simpa only [sharpPairEnvelope_zero] using
          And.intro hupper₀ (And.intro hlower₀ horder₀)
    | succ i ih =>
        have hi' : i < fuel := by omega
        have ih' := ih (Nat.le_of_lt hi')
        have hu : sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc
            Dof Mof i ≤ nonnegativeNatCeil (upperBarrier i + buffer) := by
          unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
          apply Nat.ceil_mono
          apply max_le_max_left
          simpa only [add_comm] using add_le_add_right ih'.1 buffer
        have hd : nonnegativeNatFloor (lowerBarrier i - buffer) ≤
            sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc
              Dof Mof i := by
          unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
          apply Nat.floor_mono
          exact max_le_max_left _ (sub_le_sub_right ih'.2.1 buffer)
        have hdu : sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc
            Dof Mof i ≤ sharpRecursiveUpperSchedule upper₀ lower₀ buffer
              Kinc Dof Mof i := by
          unfold sharpRecursiveLowerSchedule sharpRecursiveUpperSchedule
            nonnegativeNatFloor nonnegativeNatCeil
          have hxy : max 0
                ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 -
                  buffer) ≤
              max 0
                ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 +
                  buffer) := by
            apply max_le_max_left
            linarith [ih'.2.2, hbuffer]
          exact (Nat.floor_mono hxy).trans (Nat.floor_le_ceil _)
        rw [sharpPairEnvelope_upper_succ, sharpPairEnvelope_lower_succ]
        refine ⟨?_, ?_, ?_⟩
        · linarith [hupperStep i hi' hu hd hdu]
        · linarith [hlowerStep i hi' hu hd hdu]
        · linarith [ih'.2.2, hrateOrder i hi' hu hd hdu]
  intro i hi
  have hiEnv := henv i hi
  have hu : sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
      nonnegativeNatCeil (upperBarrier i + buffer) := by
    unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
    apply Nat.ceil_mono
    apply max_le_max_left
    simpa only [add_comm] using add_le_add_right hiEnv.1 buffer
  have hd : nonnegativeNatFloor (lowerBarrier i - buffer) ≤
      sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i := by
    unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
    apply Nat.floor_mono
    exact max_le_max_left _ (sub_le_sub_right hiEnv.2.1 buffer)
  have hdu : sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
      sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i := by
    unfold sharpRecursiveLowerSchedule sharpRecursiveUpperSchedule
      nonnegativeNatFloor nonnegativeNatCeil
    have hxy : max 0
          ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 -
            buffer) ≤
        max 0
          ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 +
            buffer) := by
      apply max_le_max_left
      linarith [hiEnv.2.2, hbuffer]
    exact (Nat.floor_mono hxy).trans (Nat.floor_le_ceil _)
  exact ⟨hu, hd, hdu⟩

end

end Erdos207

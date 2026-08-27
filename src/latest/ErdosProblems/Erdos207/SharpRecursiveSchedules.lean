/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RealFloorSchedules
import ErdosProblems.Erdos207.SharpScheduledPairTrajectories

/-!
# Self-consistent sharp pair schedules

The upper and lower real envelopes are updated by exactly the rates used by
the martingales.  Natural schedules are obtained by taking a ceiling above
the buffered upper envelope and a floor below the buffered lower envelope.
This removes all trajectory bookkeeping from the later scalar estimates.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Natural ceiling of the nonnegative part of a real number. -/
def nonnegativeNatCeil (x : ℝ) : ℕ :=
  ⌈max 0 x⌉₊

lemma le_nonnegativeNatCeil {x : ℝ} :
    x ≤ (nonnegativeNatCeil x : ℝ) := by
  calc
    x ≤ max 0 x := le_max_right _ _
    _ ≤ (nonnegativeNatCeil x : ℝ) := Nat.le_ceil _

/-- One pair of real upper/lower envelopes. -/
abbrev SharpPairEnvelope := ℝ × ℝ

/-- Recursively integrate the exact scheduled rates.  The functions `Dof`
and `Mof` may use the clock and the current natural lower/upper schedules;
this covers the pair-sum availability bounds without a mutual recursion. -/
def sharpPairEnvelope
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) : ℕ → SharpPairEnvelope
  | 0 => (upper₀, lower₀)
  | i + 1 =>
      let state := sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i
      let d := nonnegativeNatFloor (state.2 - buffer)
      let u := nonnegativeNatCeil (state.1 + buffer)
      (state.1 - sharpScheduledPairUpperRate (Mof i d u) d u,
        state.2 - sharpScheduledPairLowerRate (Dof i d u) u Kinc)

def sharpRecursiveLowerSchedule
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  nonnegativeNatFloor
    ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 - buffer)

def sharpRecursiveUpperSchedule
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  nonnegativeNatCeil
    ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 + buffer)

def sharpRecursiveLowerAvailability
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  Dof i
    (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
    (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)

def sharpRecursiveUpperAvailability
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  Mof i
    (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
    (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)

/-- A positive natural lower schedule certifies that the underlying real
lower envelope is still above its buffer. -/
lemma sharpPairEnvelope_lower_sub_buffer_nonneg_of_lowerSchedule_pos
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ)
    (hpos : 0 < sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc
      Dof Mof i) :
    0 ≤ (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 -
      buffer := by
  unfold sharpRecursiveLowerSchedule nonnegativeNatFloor at hpos
  have hmax : 1 ≤ max 0
      ((sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 -
        buffer) := Nat.floor_pos.mp hpos
  by_contra hneg
  have hlt : (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 -
      buffer < 0 := lt_of_not_ge hneg
  rw [max_eq_left (le_of_lt hlt)] at hmax
  norm_num at hmax

@[simp] lemma sharpPairEnvelope_zero
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) :
    sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof 0 =
      (upper₀, lower₀) := rfl

lemma sharpPairEnvelope_upper_succ
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof (i + 1)).1 =
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 -
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i) := by
  rfl

lemma sharpPairEnvelope_lower_succ
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof (i + 1)).2 =
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 -
        sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof i)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i)
          Kinc := by
  rfl

theorem sharpPairEnvelope_upper_eq_sub_sum
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 =
      upper₀ - ∑ j ∈ range i,
        sharpScheduledPairUpperRate
          (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
          (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [sharpPairEnvelope_upper_succ, ih, sum_range_succ]
      ring

theorem sharpPairEnvelope_lower_eq_sub_sum
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 =
      lower₀ - ∑ j ∈ range i,
        sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
          Kinc := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [sharpPairEnvelope_lower_succ, ih, sum_range_succ]
      ring

lemma sharpPairEnvelope_upper_le_initial
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 ≤ upper₀ := by
  rw [sharpPairEnvelope_upper_eq_sub_sum]
  exact sub_le_self _ (sum_nonneg fun j _ ↦
    sharpScheduledPairUpperRate_nonneg _ _ _)

lemma sharpPairEnvelope_lower_le_initial
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 ≤ lower₀ := by
  rw [sharpPairEnvelope_lower_eq_sub_sum]
  exact sub_le_self _ (sum_nonneg fun j _ ↦
    sharpScheduledPairLowerRate_nonneg _ _ _)

/-- A uniform upper bound on all lower rates gives the expected linear
lower bound on the recursively integrated lower envelope. -/
theorem sharpPairEnvelope_lower_ge_sub_mul
    (upper₀ lower₀ buffer R : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ)
    (hrate : ∀ j, j < i →
      sharpScheduledPairLowerRate
        (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
        (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
        Kinc ≤ R) :
    lower₀ - (i : ℝ) * R ≤
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 := by
  rw [sharpPairEnvelope_lower_eq_sub_sum]
  apply sub_le_sub_left
  calc
    ∑ j ∈ range i,
        sharpScheduledPairLowerRate
          (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
          (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
          Kinc ≤ ∑ _j ∈ range i, R := by
      apply sum_le_sum
      intro j hj
      exact hrate j (mem_range.mp hj)
    _ = (i : ℝ) * R := by simp

/-- A linear real lower bound turns directly into a natural lower schedule
bound. -/
theorem le_sharpRecursiveLowerSchedule_of_sub_mul
    (upper₀ lower₀ buffer R : ℝ) (Kinc dmin i : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ)
    (hrate : ∀ j, j < i →
      sharpScheduledPairLowerRate
        (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
        (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
        Kinc ≤ R)
    (hbuffer : (dmin : ℝ) + buffer + (i : ℝ) * R ≤ lower₀) :
    dmin ≤ sharpRecursiveLowerSchedule
      upper₀ lower₀ buffer Kinc Dof Mof i := by
  have henv := sharpPairEnvelope_lower_ge_sub_mul
    upper₀ lower₀ buffer R Kinc Dof Mof i hrate
  have hreal : (dmin : ℝ) ≤
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 - buffer := by
    linarith
  unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
  apply Nat.le_floor
  exact hreal.trans (le_max_right _ _)

/-- The upper schedule never exceeds the ceiling of its initial buffered
value. -/
lemma sharpRecursiveUpperSchedule_le_initial
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i ≤
      nonnegativeNatCeil (upper₀ + buffer) := by
  unfold sharpRecursiveUpperSchedule nonnegativeNatCeil
  apply Nat.ceil_mono
  apply max_le_max_left
  simpa only [add_comm] using add_le_add_right
    (sharpPairEnvelope_upper_le_initial upper₀ lower₀ buffer Kinc Dof Mof i)
      buffer

/-- The recursive upper schedule dominates every upper martingale target
whose initial pair count is at most `upper₀`. -/
theorem sharpScheduledPairUpperTarget_add_buffer_le_recursiveUpper
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (P : PairOn V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ)
    (hinitial : fixedPairAvailableCountReal S₀ P.1 S₀ ≤ upper₀) :
    sharpScheduledPairUpperTarget S₀
        (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc Dof Mof)
        (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof)
        (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof)
        P i + buffer ≤
      (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i : ℝ) := by
  rw [sharpScheduledPairUpperTarget]
  let rates := ∑ j ∈ range i,
    sharpScheduledPairUpperRate
      (sharpRecursiveUpperAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
      (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
      (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j)
  calc
    fixedPairAvailableCountReal S₀ P.1 S₀ - rates + buffer ≤
        upper₀ - rates + buffer :=
      by simpa only [add_comm] using
        add_le_add_right (sub_le_sub_right hinitial rates) buffer
    _ = (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).1 +
        buffer := by
      rw [sharpPairEnvelope_upper_eq_sub_sum]
    _ ≤ (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof i : ℝ) := by
      unfold sharpRecursiveUpperSchedule
      exact le_nonnegativeNatCeil

/-- The recursive lower schedule lies below every lower martingale target
whose initial live-pair count is at least `lower₀`. -/
theorem recursiveLower_le_sharpScheduledPairLowerTarget_sub_buffer
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (P : PairOn V)
    (upper₀ lower₀ buffer : ℝ) (Kinc : ℕ)
    (Dof Mof : ℕ → ℕ → ℕ → ℕ) (i : ℕ)
    (hinitial : lower₀ ≤ fixedPairAvailableCountReal S₀ P.1 S₀)
    (hnonneg : 0 ≤
      (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 - buffer) :
    (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i : ℝ) ≤
      sharpScheduledPairLowerTarget S₀
        (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof)
        (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof)
        Kinc P i - buffer := by
  have hfloor :
      (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i : ℝ) ≤
        (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 - buffer := by
    unfold sharpRecursiveLowerSchedule nonnegativeNatFloor
    rw [max_eq_right hnonneg]
    exact Nat.floor_le hnonneg
  rw [sharpScheduledPairLowerTarget]
  let rates := ∑ j ∈ range i,
    sharpScheduledPairLowerRate
      (sharpRecursiveLowerAvailability upper₀ lower₀ buffer Kinc Dof Mof j)
      (sharpRecursiveUpperSchedule upper₀ lower₀ buffer Kinc Dof Mof j) Kinc
  calc
    (sharpRecursiveLowerSchedule upper₀ lower₀ buffer Kinc Dof Mof i : ℝ) ≤
        (sharpPairEnvelope upper₀ lower₀ buffer Kinc Dof Mof i).2 - buffer := hfloor
    _ = lower₀ - rates - buffer := by
      rw [sharpPairEnvelope_lower_eq_sub_sum]
    _ ≤ fixedPairAvailableCountReal S₀ P.1 S₀ - rates - buffer :=
      sub_le_sub_right (sub_le_sub_right hinitial rates) buffer

end

end Erdos207

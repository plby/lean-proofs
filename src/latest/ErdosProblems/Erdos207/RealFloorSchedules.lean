/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ScheduledAggregateAverageAbsorberPhase
import ErdosProblems.Erdos207.LinearAggregateAverageAbsorberPhase

/-!
# Natural-valued floors for real linear trajectories

The martingales are centered on real-valued trajectories.  Survival needs
natural lower bounds, so we take the floor of the nonnegative part of the
corresponding real lower trajectory.
-/

namespace Erdos207

open Finset

noncomputable section

def nonnegativeNatFloor (x : ℝ) : ℕ :=
  ⌊max 0 x⌋₊

lemma nonnegativeNatFloor_le_nat_of_le
    {x : ℝ} {m : ℕ} (h : x ≤ (m : ℝ)) :
    nonnegativeNatFloor x ≤ m := by
  have hmax : max 0 x ≤ (m : ℝ) :=
    max_le (by positivity) h
  have hfloor : ((nonnegativeNatFloor x : ℕ) : ℝ) ≤ max 0 x := by
    exact Nat.floor_le (by positivity)
  exact_mod_cast hfloor.trans hmax

def realLinearFloorSchedule (x₀ rate buffer : ℝ) (i : ℕ) : ℕ :=
  nonnegativeNatFloor (x₀ - (i : ℝ) * rate - buffer)

@[simp]
lemma realLinearFloorSchedule_zero (x₀ rate buffer : ℝ) :
    realLinearFloorSchedule x₀ rate buffer 0 =
      nonnegativeNatFloor (x₀ - buffer) := by
  simp [realLinearFloorSchedule]

theorem realLinearFloorSchedule_le_nat
    {x₀ rate buffer : ℝ} {i m : ℕ}
    (h : x₀ - (i : ℝ) * rate - buffer ≤ (m : ℝ)) :
    realLinearFloorSchedule x₀ rate buffer i ≤ m :=
  nonnegativeNatFloor_le_nat_of_le h

theorem availabilityDeficit_implies_realLinearFloorSchedule
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} {rate buffer : ℝ} {i : ℕ}
    (hdeficit : averageAvailabilityDeficit rate i S -
        averageAvailabilityDeficit rate 0 S₀ < buffer) :
    realLinearFloorSchedule (S₀.available.card : ℝ) rate buffer i ≤
      S.available.card := by
  apply realLinearFloorSchedule_le_nat
  simp only [averageAvailabilityDeficit] at hdeficit
  push_cast at hdeficit
  linarith

theorem linearPairDeviation_implies_realLinearFloorSchedule
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} {P : PairOn V}
    {d₀ i : ℕ} {rate buffer : ℝ}
    (hsub : S.available ⊆ S₀.available)
    (halive : PairAlive P.1 S)
    (hfloor₀ : HasAvailablePairFloor d₀ S₀)
    (hdev : fixedPairLowerDeviation (linearPairTarget S₀ rate P) S₀
          P.1 i S -
        fixedPairLowerDeviation (linearPairTarget S₀ rate P) S₀
          P.1 0 S₀ < buffer) :
    realLinearFloorSchedule (d₀ : ℝ) rate buffer i ≤
      (availableTrianglesContainingPair S P.1).card := by
  have halive₀ : PairAlive P.1 S₀ := halive.of_available_subset hsub
  have hfloorNat : d₀ ≤
      (availableTrianglesContainingPair S₀ P.1).card :=
    hfloor₀ P.1 P.2 halive₀
  have hfloorReal : (d₀ : ℝ) ≤
      (availableTrianglesContainingPair S₀ P.1).card := by
    exact_mod_cast hfloorNat
  have hcurrent := fixedPairAvailableCountReal_eq_current
    (S₀ := S₀) (S := S) (P := P.1) hsub
  have hinitial := fixedPairAvailableCountReal_eq_current
    (S₀ := S₀) (S := S₀) (P := P.1) Subset.rfl
  apply realLinearFloorSchedule_le_nat
  simp only [fixedPairLowerDeviation, linearPairTarget,
    Nat.cast_zero, zero_mul, sub_zero] at hdev
  rw [hcurrent, hinitial] at hdev
  push_cast at hdev
  linarith

end

end Erdos207

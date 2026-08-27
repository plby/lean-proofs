/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PerturbedOuterQuadraticBarrier

/-!
# Explicit stopping clock for the outer-only phase

The process removes three eligible outside pairs at each step.  Division by
three therefore gives a canonical clock which leaves a prescribed pair
reserve, with an error of at most two pairs.
-/

namespace Erdos207

noncomputable section

def outerSharpStopFuel
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (reserve : ℕ) : ℕ :=
  (outerSharpEligiblePairs H X 0 - reserve) / 3

lemma outerSharpEligiblePairs_eq_zero_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) {i : ℕ}
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    outerSharpEligiblePairs H X i =
      outerSharpEligiblePairs H X 0 - 3 * i := by
  unfold outerSharpEligiblePairs
  omega

lemma three_mul_outerSharpStopFuel_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (reserve : ℕ) :
    3 * outerSharpStopFuel H X reserve ≤
      outerSharpEligiblePairs H X 0 - reserve := by
  unfold outerSharpStopFuel
  simpa only [Nat.mul_comm] using Nat.div_mul_le_self
    (outerSharpEligiblePairs H X 0 - reserve) 3

lemma reserve_le_outerSharpEligiblePairs_stopFuel
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) {reserve : ℕ}
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0) :
    reserve ≤ outerSharpEligiblePairs H X
      (outerSharpStopFuel H X reserve) := by
  have hstep := three_mul_outerSharpStopFuel_le H X reserve
  have hclock : 3 * outerSharpStopFuel H X reserve ≤
      outerSharpEligiblePairs H X 0 := hstep.trans (Nat.sub_le _ _)
  rw [outerSharpEligiblePairs_eq_zero_sub H X hclock]
  omega

lemma outerSharpEligiblePairs_stopFuel_lt_add_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) {reserve : ℕ}
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0) :
    outerSharpEligiblePairs H X (outerSharpStopFuel H X reserve) <
      reserve + 3 := by
  let E := outerSharpEligiblePairs H X 0
  let A := E - reserve
  have hmod : A % 3 < 3 := Nat.mod_lt A (by norm_num)
  have hdecomp : A % 3 + 3 * (A / 3) = A := Nat.mod_add_div A 3
  have hformula : outerSharpEligiblePairs H X (outerSharpStopFuel H X reserve) =
      E - 3 * (A / 3) := by
    have hstep := three_mul_outerSharpStopFuel_le H X reserve
    have hclock : 3 * outerSharpStopFuel H X reserve ≤
        outerSharpEligiblePairs H X 0 := hstep.trans (Nat.sub_le _ _)
    rw [outerSharpEligiblePairs_eq_zero_sub H X hclock]
    simp only [outerSharpStopFuel]
    rfl
  rw [hformula]
  have hEA : E = reserve + A := by
    dsimp only [A, E]
    omega
  omega

lemma outerSharpEligiblePairs_stopFuel_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) {reserve i : ℕ}
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (hi : i ≤ outerSharpStopFuel H X reserve) :
    reserve ≤ outerSharpEligiblePairs H X i := by
  have hmono : outerSharpEligiblePairs H X
      (outerSharpStopFuel H X reserve) ≤ outerSharpEligiblePairs H X i := by
    unfold outerSharpEligiblePairs
    omega
  exact (reserve_le_outerSharpEligiblePairs_stopFuel H X hreserve).trans hmono

lemma outerSharpStopFuel_le_card_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (reserve : ℕ) :
    outerSharpStopFuel H X reserve ≤ Fintype.card V ^ 2 := by
  calc
    outerSharpStopFuel H X reserve ≤ outerSharpEligiblePairs H X 0 := by
      unfold outerSharpStopFuel
      exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    _ ≤ Nat.choose (Fintype.card V) 2 := by
      unfold outerSharpEligiblePairs
      omega
    _ ≤ Fintype.card V ^ 2 := by
      exact Nat.choose_le_pow _ _

end

end Erdos207

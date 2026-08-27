/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterCorridor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Harmonic gain along the outer sharp clock

The outer process removes exactly three eligible pairs at every live step.
The reciprocal eligible-pair clock therefore accumulates logarithmically.
This file records the estimate with a deliberately generous factor six,
which cleanly absorbs the final three-pair discretization error.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- A reserve of at least 21 sharpens the discrete logarithmic loss to
seven halves of the reciprocal clock. -/
lemma log_nat_sub_three_le_seven_halves_mul_inv
    {E E' : ℕ} (hE : 21 ≤ E) (hstep : E' = E - 3) :
    Real.log E - Real.log E' ≤ (7 / 2 : ℝ) * ((E : ℝ)⁻¹) := by
  have hEreal : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by omega)
  have hE'real : (0 : ℝ) < E' := by exact_mod_cast (show 0 < E' by omega)
  have hsumReal : (E : ℝ) = E' + 3 := by
    exact_mod_cast (show E = E' + 3 by omega)
  have hlargeReal : (21 : ℝ) ≤ E := by exact_mod_cast hE
  calc
    Real.log E - Real.log E' = Real.log ((E : ℝ) / E') := by
      rw [Real.log_div hEreal.ne' hE'real.ne']
    _ ≤ (E : ℝ) / E' - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hEreal hE'real)
    _ = 3 / (E' : ℝ) := by
      field_simp
      linarith
    _ ≤ (7 / 2 : ℝ) / (E : ℝ) := by
      rw [div_le_div_iff₀ hE'real hEreal]
      linarith
    _ = (7 / 2 : ℝ) * ((E : ℝ)⁻¹) := by rw [div_eq_mul_inv]

/-- The sharper logarithmic estimate telescopes along every natural clock
which decreases by three and remains at least 21 before its terminal step. -/
theorem log_clock_ratio_le_seven_halves_mul_sum_inv
    (E : ℕ → ℕ) (fuel : ℕ)
    (hlarge : ∀ i, i < fuel → 21 ≤ E i)
    (hstep : ∀ i, i < fuel → E (i + 1) = E i - 3) :
    Real.log (E 0) - Real.log (E fuel) ≤
      (7 / 2 : ℝ) * ∑ i ∈ range fuel, ((E i : ℝ)⁻¹) := by
  calc
    Real.log (E 0) - Real.log (E fuel) =
        ∑ i ∈ range fuel, (Real.log (E i) - Real.log (E (i + 1))) := by
      rw [sum_range_sub']
    _ ≤ ∑ i ∈ range fuel, (7 / 2 : ℝ) * ((E i : ℝ)⁻¹) := by
      apply sum_le_sum
      intro i hi
      exact log_nat_sub_three_le_seven_halves_mul_inv
        (hlarge i (mem_range.mp hi)) (hstep i (mem_range.mp hi))
    _ = (7 / 2 : ℝ) * ∑ i ∈ range fuel, ((E i : ℝ)⁻¹) := by
      rw [mul_sum]

/-- One decrement by three costs at most six reciprocal-clock units in the
logarithmic potential. -/
lemma log_nat_sub_three_le_six_mul_inv
    {E E' : ℕ} (hE : 6 ≤ E) (hstep : E' = E - 3) :
    Real.log E - Real.log E' ≤ 6 * ((E : ℝ)⁻¹) := by
  have hEpos : 0 < E := by omega
  have hE'pos : 0 < E' := by omega
  have hEreal : (0 : ℝ) < E := by exact_mod_cast hEpos
  have hE'real : (0 : ℝ) < E' := by exact_mod_cast hE'pos
  have hsum : E = E' + 3 := by omega
  have hsumReal : (E : ℝ) = E' + 3 := by exact_mod_cast hsum
  have hhalf : E ≤ 2 * E' := by omega
  have hhalfReal : (E : ℝ) ≤ 2 * E' := by exact_mod_cast hhalf
  calc
    Real.log E - Real.log E' = Real.log ((E : ℝ) / E') := by
      rw [Real.log_div hEreal.ne' hE'real.ne']
    _ ≤ (E : ℝ) / E' - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hEreal hE'real)
    _ = 3 / (E' : ℝ) := by
      field_simp
      linarith
    _ ≤ 6 / (E : ℝ) := by
      rw [div_le_div_iff₀ hE'real hEreal]
      nlinarith
    _ = 6 * ((E : ℝ)⁻¹) := by rw [div_eq_mul_inv]

/-- Telescoping the logarithmic potential along the exact outer clock gives
a lower bound for its reciprocal sum. -/
theorem outerSharpClock_log_ratio_le_six_mul_sum_inv
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (reserve : ℕ)
    (hreserve : reserve ≤ outerSharpEligiblePairs H X 0)
    (hreserveSix : 6 ≤ reserve) :
    let fuel := outerSharpStopFuel H X reserve
    Real.log (outerSharpEligiblePairs H X 0) -
        Real.log (outerSharpEligiblePairs H X fuel) ≤
      6 * ∑ i ∈ range fuel,
        ((outerSharpEligiblePairs H X i : ℕ) : ℝ)⁻¹ := by
  dsimp only
  let fuel := outerSharpStopFuel H X reserve
  have hterm : ∀ i ∈ range fuel,
      Real.log (outerSharpEligiblePairs H X i) -
          Real.log (outerSharpEligiblePairs H X (i + 1)) ≤
        6 * (((outerSharpEligiblePairs H X i : ℕ) : ℝ)⁻¹) := by
    intro i hi
    have hiFuel : i < fuel := mem_range.mp hi
    have hiLe : i ≤ fuel := Nat.le_of_lt hiFuel
    have hEi : reserve ≤ outerSharpEligiblePairs H X i :=
      outerSharpEligiblePairs_stopFuel_floor H X hreserve hiLe
    have hclockFuel := three_mul_outerSharpStopFuel_le H X reserve
    have hclock : 3 * (i + 1) ≤ outerSharpEligiblePairs H X 0 := by
      have hisucc : i + 1 ≤ fuel := by omega
      calc
        3 * (i + 1) ≤ 3 * fuel := Nat.mul_le_mul_left 3 hisucc
        _ ≤ outerSharpEligiblePairs H X 0 - reserve := hclockFuel
        _ ≤ outerSharpEligiblePairs H X 0 := Nat.sub_le _ _
    apply log_nat_sub_three_le_six_mul_inv
      (hreserveSix.trans hEi)
    exact outerSharpEligiblePairs_succ_eq_sub_three H X hclock
  calc
    Real.log (outerSharpEligiblePairs H X 0) -
          Real.log (outerSharpEligiblePairs H X fuel) =
        ∑ i ∈ range fuel,
          (Real.log (outerSharpEligiblePairs H X i) -
            Real.log (outerSharpEligiblePairs H X (i + 1))) := by
      rw [sum_range_sub']
    _ ≤ ∑ i ∈ range fuel,
          6 * (((outerSharpEligiblePairs H X i : ℕ) : ℝ)⁻¹) := by
      exact sum_le_sum hterm
    _ = 6 * ∑ i ∈ range fuel,
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ)⁻¹ := by
      rw [mul_sum]

end

end Erdos207

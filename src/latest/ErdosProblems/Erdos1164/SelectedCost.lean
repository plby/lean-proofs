import ErdosProblems.Erdos1164.PointCostRestart
import ErdosProblems.Erdos1164.TargetRace

/-! # A uniform logarithmic local-time cost between selected targets -/

open MeasureTheory

namespace Erdos1164

open Erdos1165 Erdos1165.PointBeforeReturn

/-- A positive integer visit cost proportional to the logarithmic spatial scale. -/
noncomputable def targetVisitCost (m : ℕ) : ℕ := ⌊spatialLogScale m / 2⌋₊ + 1

theorem targetVisitCost_pos (m : ℕ) : 0 < targetVisitCost m := Nat.succ_pos _

theorem targetVisitCost_lower (m : ℕ) : spatialLogScale m / 2 ≤ (targetVisitCost m : ℝ) := by
  simpa only [targetVisitCost, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one (spatialLogScale m / 2)).le

private theorem target_floor_cost_small {m : ℕ} (hm : LargeTargetScale m) (i : Fin m) :
    (⌊spatialLogScale m / 2⌋₊ : ℝ) *
      pointBeforeReturnProbability (separatedTarget m i) ≤ 1 / 4 := by
  have hs := hm.2
  have he := potentialError_pos
  have ht : 0 < spatialLogScale m := by linarith
  have hf : (⌊spatialLogScale m / 2⌋₊ : ℝ) ≤ spatialLogScale m / 2 := Nat.floor_le (by positivity)
  calc
    _ ≤ (⌊spatialLogScale m / 2⌋₊ : ℝ) * (1 / (2 * spatialLogScale m)) :=
      mul_le_mul_of_nonneg_left (target_excursion_probability_upper hm i) (by positivity)
    _ ≤ (spatialLogScale m / 2) * (1 / (2 * spatialLogScale m)) := by gcongr
    _ = 1 / 4 := by field_simp; norm_num

/-- Starting at the origin, the logarithmic cost is paid with probability at least one half. -/
theorem selected_cost_from_origin {m : ℕ} (hm : LargeTargetScale m) (i : Fin m) :
    (1 / 2 : ℝ) ≤ fairSteps.real
      (beforePointVisits 0 (separatedTarget m i) (targetVisitCost m)) := by
  have h := beforePointVisits_origin_lower (separatedTarget m i)
    (separatedTarget_ne_zero (by have := hm.1; omega) i) ⌊spatialLogScale m / 2⌋₊
  have hp := target_floor_cost_small hm i
  change 1 - _ ≤ fairSteps.real (beforePointVisits 0 (separatedTarget m i) (targetVisitCost m)) at h
  linarith

/-- The same cost is paid with uniformly positive probability from any other selected target. -/
theorem selected_cost_from_target {m : ℕ} (hm : LargeTargetScale m)
    {i j : Fin m} (hij : i ≠ j) :
    (1 / 256 : ℝ) ≤ fairSteps.real
      (beforePointVisits (separatedTarget m i) (separatedTarget m j) (targetVisitCost m)) := by
  have hprod := mul_le_mul (target_race_origin_lower hm hij) (selected_cost_from_origin hm j)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) measureReal_nonneg
  have h := beforePointVisits_race_product_real (separatedTarget m i) (separatedTarget m j)
    (targetVisitCost m)
  norm_num at hprod
  exact hprod.trans h

/-- Uniform form covering the initial point and every possible prior target. -/
theorem selected_cost_uniform {m : ℕ} (hm : LargeTargetScale m) (j : Fin m)
    {x : Point} (hx : x = 0 ∨ ∃ i : Fin m, i ≠ j ∧ x = separatedTarget m i) :
    (1 / 256 : ℝ) ≤ fairSteps.real
      (beforePointVisits x (separatedTarget m j) (targetVisitCost m)) := by
  rcases hx with rfl | ⟨i, hij, rfl⟩
  · exact (by norm_num : (1 / 256 : ℝ) ≤ 1 / 2).trans (selected_cost_from_origin hm j)
  · exact selected_cost_from_target hm hij

/-- The corresponding fixed contraction of exponential hitting costs. -/
noncomputable def targetCostDiscount : ℝ := 1 - (1 - Real.exp (-1)) / 256

theorem targetCostDiscount_pos : 0 < targetCostDiscount := by
  unfold targetCostDiscount
  have h := Real.exp_pos (-1)
  linarith

theorem targetCostDiscount_lt_one : targetCostDiscount < 1 := by
  unfold targetCostDiscount
  have h : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

end Erdos1164

import ErdosProblems.Erdos1164.OrderedCoverCost

/-! # The upper tail of the covered radius -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential

/-- Covering the radius-`2m²` disc covers the selected targets by the next deadline. -/
theorem radius_cover_implies_selected {m n : ℕ} (hm : 1 ≤ m) {w : StepPath}
    (h : 2 * m ^ 2 ≤ coveredRadius (trajectory w) n) : w ∈ selectedCovered m (n + 1) := by
  have hc := (le_coveredRadius_iff (trajectory_zero w) n (2 * m ^ 2)).mp h
  intro i
  obtain ⟨j, hj, hp⟩ := hc (separatedTarget m i) (separatedTarget_mem_disc m i)
  have ht : pointHitClock 0 (separatedTarget m i) (n + 1) w ≤ n := by
    apply (pointHitClock_le_iff (Ne.symm (separatedTarget_ne_zero hm i)) (Nat.lt_succ_self n) w).mpr
    exact ⟨j, hj, by simpa only [trajectoryFrom, zero_add] using hp⟩
  exact ht.trans_lt (Nat.lt_succ_self n)

/-- Finite-time upper-radius estimate. The integer split level `K` is free,
so it can later be chosen proportional to `log n` or to the covering cost. -/
theorem radius_upper_tail {m n K : ℕ} (hm : LargeTargetScale m) (hK : 2 ≤ K) :
    walkLaw {s | 2 * m ^ 2 ≤ coveredRadius s n} ≤
      ENNReal.ofReal (Real.exp ((K : ℝ) / (targetVisitCost m : ℝ) -
        (1 - targetCostDiscount) * (harmonic m : ℝ))) +
      ENNReal.ofReal (Real.exp (-((K - 1 : ℕ) : ℝ) /
        (100 * Real.log ((n + 2 : ℕ) : ℝ)))) := by
  have hmeas : MeasurableSet {s : WalkPath | 2 * m ^ 2 ≤ coveredRadius s n} :=
    measurableSet_le measurable_const (measurable_coveredRadius n)
  have hcount : MeasurableSet {s : WalkPath | K ≤ originVisits s (n + 1)} :=
    measurableSet_le measurable_const (measurable_originVisits (n + 1))
  have hsub : trajectory ⁻¹' {s : WalkPath | 2 * m ^ 2 ≤ coveredRadius s n} ⊆
      (selectedCovered m (n + 1) ∩ {w | normalizedOriginCost m (n + 1) w ≤
        (K : ℝ) / (targetVisitCost m : ℝ)}) ∪
      trajectory ⁻¹' {s : WalkPath | K ≤ originVisits s (n + 1)} := by
    intro w hw
    by_cases hk : K ≤ originVisits (trajectory w) (n + 1)
    · exact Or.inr hk
    · refine Or.inl ⟨radius_cover_implies_selected (by have := hm.1; omega) hw, ?_⟩
      change (originVisits (trajectory w) (n + 1) : ℝ) / (targetVisitCost m : ℝ) ≤
        (K : ℝ) / (targetVisitCost m : ℝ)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (by omega : originVisits (trajectory w) (n + 1) ≤ K)
  have hcost := selected_cover_cost_tail hm (Nat.succ_pos n)
    ((K : ℝ) / (targetVisitCost m : ℝ))
  have hclock := originVisits_tail (by omega : 1 ≤ n + 1) hK
  change simpleRandomWalk _ ≤ _ at hclock ⊢
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hmeas]
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hcount] at hclock
  calc
    _ ≤ fairSteps ((selectedCovered m (n + 1) ∩
        {w | normalizedOriginCost m (n + 1) w ≤ (K : ℝ) / (targetVisitCost m : ℝ)}) ∪
          trajectory ⁻¹' {s : WalkPath | K ≤ originVisits s (n + 1)}) := measure_mono hsub
    _ ≤ fairSteps (selectedCovered m (n + 1) ∩
        {w | normalizedOriginCost m (n + 1) w ≤ (K : ℝ) / (targetVisitCost m : ℝ)}) +
          fairSteps (trajectory ⁻¹' {s : WalkPath | K ≤ originVisits s (n + 1)}) :=
      measure_union_le _ _
    _ ≤ _ := add_le_add hcost (by simpa only [Nat.add_assoc] using hclock)

end Erdos1164

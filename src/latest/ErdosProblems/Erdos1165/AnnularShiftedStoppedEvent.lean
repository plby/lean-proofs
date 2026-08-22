/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.Proposition13Assembly

/-!
# Deterministic shift invariance of stopped successful-point events
-/

open MeasureTheory Set

namespace Erdos1165.AnnularShiftedStoppedEvent

open Proposition13Assembly

noncomputable section

theorem stoppedSuccessfulPointEvent_eq_shiftSteps_preimage
    (start scale : ℕ) (delta : ℝ) (x : Point) :
    stoppedSuccessfulPointEvent start scale delta x =
      shiftSteps start ⁻¹'
        stoppedSuccessfulPointEvent 0 scale delta x := by
  ext omega
  simp only [stoppedSuccessfulPointEvent, Set.mem_setOf_eq,
    Set.mem_preimage]
  change (∃ horizon,
      ThickPoint.IsOuterExitTime (trajectory (shiftSteps start omega))
          scale horizon ∧
        ThickPoint.SuccessfulPoint (trajectory (shiftSteps start omega))
          scale horizon delta x) ↔
    ∃ horizon,
      ThickPoint.IsOuterExitTime
          (trajectory (shiftSteps 0 (shiftSteps start omega))) scale horizon ∧
        ThickPoint.SuccessfulPoint
          (trajectory (shiftSteps 0 (shiftSteps start omega)))
            scale horizon delta x
  have hshift : shiftSteps 0 (shiftSteps start omega) =
      shiftSteps start omega := by
    funext q
    simp only [shiftSteps, Nat.zero_add]
  rw [hshift]

theorem fairSteps_stoppedSuccessfulPointEvent_eq_zero
    (start scale : ℕ) (delta : ℝ) (x : Point) :
    fairSteps (stoppedSuccessfulPointEvent start scale delta x) =
      fairSteps (stoppedSuccessfulPointEvent 0 scale delta x) := by
  rw [stoppedSuccessfulPointEvent_eq_shiftSteps_preimage]
  rw [← Measure.map_apply (measurable_shiftSteps start)
    (measurableSet_stoppedSuccessfulPointEvent 0 scale delta x),
    fairSteps_map_shiftSteps]

theorem fairStepsReal_stoppedSuccessfulPointEvent_eq_zero
    (start scale : ℕ) (delta : ℝ) (x : Point) :
    fairSteps.real (stoppedSuccessfulPointEvent start scale delta x) =
      fairSteps.real (stoppedSuccessfulPointEvent 0 scale delta x) := by
  rw [Measure.real, Measure.real,
    fairSteps_stoppedSuccessfulPointEvent_eq_zero]

end

end Erdos1165.AnnularShiftedStoppedEvent

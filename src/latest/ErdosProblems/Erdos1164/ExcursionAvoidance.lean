import ErdosProblems.Erdos1164.LocalTime
import ErdosProblems.Erdos1165.HLOZGapPointReturn

/-! # Repeated return excursions cannot keep missing a fixed site -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165
open Erdos1165.HLOZGapEstimate Erdos1165.HLOZGapReturn
open Erdos1165.HLOZGapStoppedCandidate Erdos1165.HLOZGapPointReturn
open Erdos1165.PointBeforeReturn

/-- A point is still unvisited despite at least `k` visits to the origin. -/
def missedPointWithVisits (x : Point) (n k : ℕ) : Set WalkPath :=
  {s | k ≤ localTime s n 0 ∧ ∀ j ≤ n, s j ≠ x}

theorem measurableSet_missedPointWithVisits (x : Point) (n k : ℕ) :
    MeasurableSet (missedPointWithVisits x n k) := by
  have hcount : MeasurableSet {s : WalkPath | k ≤ localTime s n 0} :=
    measurableSet_le measurable_const
      (HLOZGapCandidateMeasurability.measurable_localTime_fixed n 0)
  have hmiss : MeasurableSet {s : WalkPath | ∀ j ≤ n, s j ≠ x} := by
    measurability
  exact hcount.inter hmiss

private theorem constant_observable {tau : StepPath → ℕ}
    (htau : IsFiniteStoppingTime tau) (x y : Point) :
    IsMeasurableAtStopping tau {_w | x = y} := by
  intro t
  by_cases h : x = y
  · simpa only [h, Set.ofPred_true, Set.univ_inter] using htau.measurableSet_eq t
  · simp only [h, Set.ofPred_false, Set.empty_inter, MeasurableSet.empty]

private theorem origin_return_stage {n k : ℕ} (hk : 2 ≤ k) {w : StepPath}
    (hcount : k ≤ localTime (trajectory w) n 0) :
    w ∈ returnLadderStage (fun _ ↦ 0) (fun _ ↦ 0) (n + 1) (k - 1) := by
  apply HLOZFixedPointLocalTimeTail.returnLadderStage_of_strictVisitSchedule_from_base
    (by omega)
  apply hasStrictVisitSchedule_of_localTime_gain (by omega)
  change localTime (trajectory w) 0 0 + (k - 1) ≤ localTime (trajectory w) n 0
  have hz : localTime (trajectory w) 0 0 = 1 := by
    simp [localTime, localTimePrefix, pathPrefix, trajectory_zero]
  rw [hz]
  omega

private theorem origin_return_clock_lt {n k : ℕ} (hk : 2 ≤ k) {w : StepPath}
    (hstage : w ∈ returnLadderStage (fun _ ↦ 0) (fun _ ↦ 0) (n + 1) (k - 1)) :
    returnLadder (fun _ ↦ 0) (fun _ ↦ 0) (n + 1) (k - 1) w < n + 1 := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - 1 ≠ 0)
  simpa only [hj, returnLadderStage, Set.mem_ofPred_eq] using hstage

private noncomputable def missedPointCertificate (x : Point) (n k : ℕ)
    (hx : x ≠ 0) (hk : 2 ≤ k) :
    PointBeforeReturnCertificate (missedPointWithVisits x n k) (k - 1) where
  stage := screenedReturnLadderStage (fun _ ↦ 0) (fun _ ↦ 0)
    (fun _ ↦ 0) (n + 1) (fun _ ↦ x)
  stop := returnLadder (fun _ ↦ 0) (fun _ ↦ 0) (n + 1)
  relativePoint := fun _ _ ↦ x
  event_subset := by
    intro w hw
    have hstage := origin_return_stage hk hw.1
    refine ⟨⟨hstage, hx⟩, ?_⟩
    intro q _hqpos hq
    exact hw.2 q (by have := origin_return_clock_lt hk hstage; omega)
  stop_isStopping := fun r _ ↦ returnLadder_isFiniteStoppingTime
    (isFiniteStoppingTime_const 0) (fun _ ↦ Nat.zero_le _)
    (fun y ↦ constant_observable (isFiniteStoppingTime_const 0) 0 y) r
  spatial_observable := by
    intro r _ y
    apply isMeasurableAtStopping_inter
    · exact screenedReturnLadderStage_observable
        (isFiniteStoppingTime_const 0) (fun _ ↦ Nat.zero_le _)
        (fun z ↦ constant_observable (isFiniteStoppingTime_const 0) 0 z)
        (fun _ ↦ le_rfl)
        (fun z ↦ constant_observable (isFiniteStoppingTime_const 0) x z) r
    · exact constant_observable
        (returnLadder_isFiniteStoppingTime (isFiniteStoppingTime_const 0)
          (fun _ ↦ Nat.zero_le _)
          (fun z ↦ constant_observable (isFiniteStoppingTime_const 0) 0 z) r) x y
  next_subset := by
    intro r _
    simpa only [sub_zero] using
      (screenedReturnLadderStage_succ_subset_pointBeforeReturn_compl
        (past := fun _ ↦ 0) (start := fun _ ↦ 0) (target := fun _ ↦ 0)
        (old := fun _ ↦ x) (deadline := n + 1) (r := r)
        (fun _ ↦ Nat.zero_le _) (fun _ ↦ le_rfl) (fun w ↦ trajectory_zero w))

/-- The exact point-before-return probability gives the geometric cost of
missing that point during `k-1` completed excursions from the origin. -/
theorem missedPointWithVisits_geometric (x : Point) (n k : ℕ)
    (hx : x ≠ 0) (hk : 2 ≤ k) :
    walkLaw (missedPointWithVisits x n k) ≤
      Gap.geometricReturnCost (pointBeforeReturnProbability x) (k - 1) := by
  exact measure_le_geometricReturnCost_of_pointBeforeReturnCertificate
    (measurableSet_missedPointWithVisits x n k)
    (pointBeforeReturnProbability_nonneg x) (pointBeforeReturnProbability_le_one x)
    (missedPointCertificate x n k hx hk) (fun _ _ _ _ ↦ le_rfl)

/-- Exponential form of the preceding unconditional estimate. -/
theorem missedPointWithVisits_exponential (x : Point) (n k : ℕ)
    (hx : x ≠ 0) (hk : 2 ≤ k) :
    walkLaw (missedPointWithVisits x n k) ≤
      ENNReal.ofReal (Real.exp (-(pointBeforeReturnProbability x * (k - 1 : ℕ)))) :=
  (missedPointWithVisits_geometric x n k hx hk).trans
    (Gap.geometricReturnCost_le_exponentialReturnCost
      (pointBeforeReturnProbability_nonneg x) (pointBeforeReturnProbability_le_one x) _)

end Erdos1164

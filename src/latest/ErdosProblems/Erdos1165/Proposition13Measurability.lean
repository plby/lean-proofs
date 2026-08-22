/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.BlockAmplification
import ErdosProblems.Erdos1165.LevelTail
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.ThickPoint

/-!
# Measurability of the literal Proposition 1.3 events

This file records the measurable-event layer used by the Appendix-A and
independent-block assembly of HLOZ Proposition 1.3.  It deliberately uses the
literal predicates from `ThickPoint`: an outer exit occurs at a specified
finite time, a point has the successful excursion profile through that time,
and the same point is thick-successful through that time.

The fixed-horizon predicates depend only on a finite path prefix.  Their
stopped versions are countable unions over the first outer-exit time, and
their deterministic-block versions are pullbacks by the measurable shift of
the increment sequence.  The final section closes the exact threshold and
global-failure event schemas passed to `BlockAmplification`.
-/

open MeasureTheory Set

namespace Erdos1165.Proposition13Measurability

noncomputable section

/-! ## Finite-prefix infrastructure -/

/-- Extend a finite walk prefix by the origin.  Only the values through the
given horizon will ever be observed. -/
def extendWalkPrefix {horizon : ℕ} (u : Fin (horizon + 1) → Point) : WalkPath :=
  fun k ↦ if hk : k ≤ horizon then u ⟨k, Nat.lt_succ_of_le hk⟩ else (0, 0)

lemma extendWalkPrefix_eq {horizon : ℕ} (u : Fin (horizon + 1) → Point)
    {k : ℕ} (hk : k ≤ horizon) :
    extendWalkPrefix u k = u ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [extendWalkPrefix, hk]

/-- Any predicate determined by a finite path prefix is measurable. -/
lemma measurableSet_of_pathPrefix_dependent (horizon : ℕ) (P : WalkPath → Prop)
    (hP : ∀ s t : WalkPath, (∀ k ≤ horizon, s k = t k) → (P s ↔ P t)) :
    MeasurableSet {s | P s} := by
  let A : Set (Fin (horizon + 1) → Point) := {u | P (extendWalkPrefix u)}
  have hset : {s : WalkPath | P s} =
      (fun s : WalkPath ↦ pathPrefix s horizon) ⁻¹' A := by
    ext s
    change P s ↔ P (extendWalkPrefix (pathPrefix s horizon))
    apply hP
    intro k hk
    simp [extendWalkPrefix, hk, pathPrefix]
  rw [hset]
  exact (measurable_pathPrefix horizon) (Set.to_countable A).measurableSet

lemma hitTimesThrough_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (A : Set Point) [DecidablePred (· ∈ A)] (start : ℕ) :
    ThickPoint.hitTimesThrough s A start horizon =
      ThickPoint.hitTimesThrough t A start horizon := by
  apply Finset.filter_congr
  intro k hk
  rw [hst k (Finset.mem_Icc.mp hk).2]

lemma firstHitThrough_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (A : Set Point) [DecidablePred (· ∈ A)] (start : ℕ) :
    ThickPoint.firstHitThrough s A start horizon =
      ThickPoint.firstHitThrough t A start horizon := by
  unfold ThickPoint.firstHitThrough
  rw [hitTimesThrough_congr_prefix hst A start]

lemma completedExcursionCount_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)] :
    ThickPoint.completedExcursionCount s outer inner horizon =
      ThickPoint.completedExcursionCount t outer inner horizon := by
  have hstep :
      ThickPoint.excursionStep s outer inner horizon =
        ThickPoint.excursionStep t outer inner horizon := by
    funext start
    unfold ThickPoint.excursionStep
    rw [firstHitThrough_congr_prefix hst outer start,
      firstHitThrough_congr_prefix hst inner]
  have hstart (j : ℕ) :
      ThickPoint.excursionStart s outer inner horizon j =
        ThickPoint.excursionStart t outer inner horizon j := by
    unfold ThickPoint.excursionStart
    rw [hstep, firstHitThrough_congr_prefix hst outer]
  have hfinish (j : ℕ) :
      ThickPoint.excursionFinish s outer inner horizon j =
        ThickPoint.excursionFinish t outer inner horizon j := by
    unfold ThickPoint.excursionFinish
    rw [hstart j, firstHitThrough_congr_prefix hst inner]
  unfold ThickPoint.completedExcursionCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _hj
  rw [hfinish j]

lemma excursionProfile_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (x : Point) :
    ThickPoint.excursionProfile s n horizon x =
      ThickPoint.excursionProfile t n horizon x := by
  classical
  funext k
  unfold ThickPoint.excursionProfile
  split_ifs
  · rfl
  · exact completedExcursionCount_congr_prefix hst _ _

lemma localTimeThrough_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (x : Point) :
    ThickPoint.localTimeThrough s horizon x =
      ThickPoint.localTimeThrough t horizon x := by
  unfold ThickPoint.localTimeThrough
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k hk
  rw [hst k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

lemma successfulPoint_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (delta : ℝ) (x : Point) :
    ThickPoint.SuccessfulPoint s n horizon delta x ↔
      ThickPoint.SuccessfulPoint t n horizon delta x := by
  unfold ThickPoint.SuccessfulPoint
  rw [excursionProfile_congr_prefix hst x]

lemma thickSuccessfulPoint_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) (delta delta' : ℝ) (x : Point) :
    ThickPoint.ThickSuccessfulPoint s n horizon delta delta' x ↔
      ThickPoint.ThickSuccessfulPoint t n horizon delta delta' x := by
  unfold ThickPoint.ThickSuccessfulPoint
  rw [successfulPoint_congr_prefix hst delta x,
    localTimeThrough_congr_prefix hst x]

lemma isOuterExitTime_congr_prefix
    {s t : WalkPath} {n horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k) :
    ThickPoint.IsOuterExitTime s n horizon ↔
      ThickPoint.IsOuterExitTime t n horizon := by
  unfold ThickPoint.IsOuterExitTime
  constructor
  · rintro ⟨hexit, hbefore⟩
    refine ⟨?_, ?_⟩
    · simpa [hst horizon le_rfl] using hexit
    · intro k hk
      simpa [hst k hk.le] using hbefore k hk
  · rintro ⟨hexit, hbefore⟩
    refine ⟨?_, ?_⟩
    · simpa [hst horizon le_rfl] using hexit
    · intro k hk
      simpa [hst k hk.le] using hbefore k hk

/-- The walk segment formed by increments beginning at deterministic time
`start`, translated back to the origin. -/
def shiftedWalk (start : ℕ) (omega : StepPath) : WalkPath :=
  trajectory (shiftSteps start omega)

lemma measurable_shiftedWalk (start : ℕ) : Measurable (shiftedWalk start) := by
  exact measurable_trajectory.comp (measurable_shiftSteps start)

/-! ## Literal fixed-horizon events on walk paths -/

/-- The outer boundary is hit for the first time at exactly `horizon`. -/
def outerExitAtEvent (scale horizon : ℕ) : Set WalkPath :=
  {s | ThickPoint.IsOuterExitTime s scale horizon}

/-- A fixed candidate has the successful excursion profile through a fixed
horizon. -/
def successfulPointAtEvent (scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) : Set WalkPath :=
  {s | ThickPoint.SuccessfulPoint s scale horizon profileDelta x}

/-- A fixed candidate is thick-successful through a fixed horizon. -/
def thickSuccessfulPointAtEvent (scale horizon : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) : Set WalkPath :=
  {s | ThickPoint.ThickSuccessfulPoint s scale horizon profileDelta thickDelta x}

/-- The literal fixed-horizon stopped successful-point event. -/
def stoppedSuccessfulPointAtEvent (scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) : Set WalkPath :=
  outerExitAtEvent scale horizon ∩
    successfulPointAtEvent scale horizon profileDelta x

/-- The literal fixed-horizon stopped thick-successful-point event. -/
def stoppedThickPointAtEvent (scale horizon : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) : Set WalkPath :=
  outerExitAtEvent scale horizon ∩
    thickSuccessfulPointAtEvent scale horizon profileDelta thickDelta x

lemma measurableSet_outerExitAtEvent (scale horizon : ℕ) :
    MeasurableSet (outerExitAtEvent scale horizon) := by
  exact measurableSet_of_pathPrefix_dependent horizon _ fun _s _t hst ↦
    isOuterExitTime_congr_prefix hst

lemma measurableSet_successfulPointAtEvent (scale horizon : ℕ)
    (profileDelta : ℝ) (x : Point) :
    MeasurableSet (successfulPointAtEvent scale horizon profileDelta x) := by
  exact measurableSet_of_pathPrefix_dependent horizon _ fun _s _t hst ↦
    successfulPoint_congr_prefix hst profileDelta x

lemma measurableSet_thickSuccessfulPointAtEvent (scale horizon : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) :
    MeasurableSet
      (thickSuccessfulPointAtEvent scale horizon profileDelta thickDelta x) := by
  exact measurableSet_of_pathPrefix_dependent horizon _ fun _s _t hst ↦
    thickSuccessfulPoint_congr_prefix hst profileDelta thickDelta x

lemma measurableSet_stoppedSuccessfulPointAtEvent (scale horizon : ℕ)
    (profileDelta : ℝ) (x : Point) :
    MeasurableSet (stoppedSuccessfulPointAtEvent scale horizon profileDelta x) := by
  exact (measurableSet_outerExitAtEvent scale horizon).inter
    (measurableSet_successfulPointAtEvent scale horizon profileDelta x)

lemma measurableSet_stoppedThickPointAtEvent (scale horizon : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) :
    MeasurableSet
      (stoppedThickPointAtEvent scale horizon profileDelta thickDelta x) := by
  exact (measurableSet_outerExitAtEvent scale horizon).inter
    (measurableSet_thickSuccessfulPointAtEvent scale horizon
      profileDelta thickDelta x)

/-! ## Deterministic increment-block shifts -/

/-- Pull an arbitrary walk-path event back to the deterministic increment
block beginning at `start`. -/
def shiftedWalkEvent (start : ℕ) (A : Set WalkPath) : Set StepPath :=
  shiftedWalk start ⁻¹' A

lemma measurableSet_shiftedWalkEvent (start : ℕ) {A : Set WalkPath}
    (hA : MeasurableSet A) : MeasurableSet (shiftedWalkEvent start A) := by
  exact (measurable_shiftedWalk start) hA

/-- The fixed-horizon literal stopped-success event in a deterministic
increment block. -/
def shiftedStoppedSuccessfulPointAtEvent (start scale horizon : ℕ)
    (profileDelta : ℝ) (x : Point) : Set StepPath :=
  shiftedWalkEvent start
    (stoppedSuccessfulPointAtEvent scale horizon profileDelta x)

/-- The fixed-horizon literal stopped thick-success event in a deterministic
increment block. -/
def shiftedStoppedThickPointAtEvent (start scale horizon : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) : Set StepPath :=
  shiftedWalkEvent start
    (stoppedThickPointAtEvent scale horizon profileDelta thickDelta x)

lemma measurableSet_shiftedStoppedSuccessfulPointAtEvent
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point) :
    MeasurableSet
      (shiftedStoppedSuccessfulPointAtEvent start scale horizon profileDelta x) := by
  exact measurableSet_shiftedWalkEvent start
    (measurableSet_stoppedSuccessfulPointAtEvent scale horizon profileDelta x)

lemma measurableSet_shiftedStoppedThickPointAtEvent
    (start scale horizon : ℕ) (profileDelta thickDelta : ℝ) (x : Point) :
    MeasurableSet
      (shiftedStoppedThickPointAtEvent start scale horizon
        profileDelta thickDelta x) := by
  exact measurableSet_shiftedWalkEvent start
    (measurableSet_stoppedThickPointAtEvent scale horizon
      profileDelta thickDelta x)

/-- The stopped profile event, obtained by taking the countable union over
the literal first outer-exit time. -/
def stoppedSuccessfulPointEvent (start scale : ℕ) (profileDelta : ℝ)
    (x : Point) : Set StepPath :=
  {omega | ∃ horizon : ℕ,
    ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
      ThickPoint.SuccessfulPoint (shiftedWalk start omega) scale horizon
        profileDelta x}

/-- The stopped thick-profile event, obtained by taking the countable union
over the literal first outer-exit time. -/
def stoppedThickPointEvent (start scale : ℕ)
    (profileDelta thickDelta : ℝ) (x : Point) : Set StepPath :=
  {omega | ∃ horizon : ℕ,
    ThickPoint.IsOuterExitTime (shiftedWalk start omega) scale horizon ∧
      ThickPoint.ThickSuccessfulPoint (shiftedWalk start omega) scale horizon
        profileDelta thickDelta x}

lemma stoppedSuccessfulPointEvent_eq_iUnion_shiftedAt
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ horizon : ℕ,
        shiftedStoppedSuccessfulPointAtEvent start scale horizon profileDelta x := by
  ext omega
  simp [stoppedSuccessfulPointEvent, shiftedStoppedSuccessfulPointAtEvent,
    shiftedWalkEvent, stoppedSuccessfulPointAtEvent, outerExitAtEvent,
    successfulPointAtEvent]

lemma stoppedThickPointEvent_eq_iUnion_shiftedAt
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point) :
    stoppedThickPointEvent start scale profileDelta thickDelta x =
      ⋃ horizon : ℕ,
        shiftedStoppedThickPointAtEvent start scale horizon
          profileDelta thickDelta x := by
  ext omega
  simp [stoppedThickPointEvent, shiftedStoppedThickPointAtEvent,
    shiftedWalkEvent, stoppedThickPointAtEvent, outerExitAtEvent,
    thickSuccessfulPointAtEvent]

lemma measurableSet_stoppedSuccessfulPointEvent
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    MeasurableSet (stoppedSuccessfulPointEvent start scale profileDelta x) := by
  rw [stoppedSuccessfulPointEvent_eq_iUnion_shiftedAt]
  exact MeasurableSet.iUnion fun horizon ↦
    measurableSet_shiftedStoppedSuccessfulPointAtEvent
      start scale horizon profileDelta x

lemma measurableSet_stoppedThickPointEvent
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x : Point) :
    MeasurableSet
      (stoppedThickPointEvent start scale profileDelta thickDelta x) := by
  rw [stoppedThickPointEvent_eq_iUnion_shiftedAt]
  exact MeasurableSet.iUnion fun horizon ↦
    measurableSet_shiftedStoppedThickPointAtEvent
      start scale horizon profileDelta thickDelta x

/-! ## Candidate unions and the exact lower-deviation failure event -/

/-- A finite union of point events over HLOZ's candidate square. -/
def oneBlockSuccess (scale : ℕ) (thick : Point → Set StepPath) : Set StepPath :=
  ⋃ x ∈ ThickPoint.candidateBox scale, thick x

lemma measurableSet_oneBlockSuccess {scale : ℕ} {thick : Point → Set StepPath}
    (hmeas : ∀ x ∈ ThickPoint.candidateBox scale, MeasurableSet (thick x)) :
    MeasurableSet (oneBlockSuccess scale thick) := by
  exact (ThickPoint.candidateBox scale).measurableSet_biUnion hmeas

/-- At least one literal stopped thick-successful candidate occurs in the
deterministic block.  This is `oneBlockSuccess` specialized to the actual
HLOZ stopped event. -/
def stoppedBlockSuccessEvent (start scale : ℕ)
    (profileDelta thickDelta : ℝ) : Set StepPath :=
  oneBlockSuccess scale
    (stoppedThickPointEvent start scale profileDelta thickDelta)

lemma measurableSet_stoppedBlockSuccessEvent (start scale : ℕ)
    (profileDelta thickDelta : ℝ) :
    MeasurableSet
      (stoppedBlockSuccessEvent start scale profileDelta thickDelta) := by
  exact measurableSet_oneBlockSuccess fun x _hx ↦
    measurableSet_stoppedThickPointEvent start scale profileDelta thickDelta x

/-- The lower-deviation threshold event on increment paths, exactly as it
appears on the left side of `ScaleCertificate.measureReal_lowerDeviation_le`.
-/
def lowerDeviationStepEvent (delta : ℝ) (n : ℕ) : Set StepPath :=
  trajectory ⁻¹' lowerDeviationSet delta n

/-- Its complementary global success event: the maximum local time reaches
the Proposition 1.3 threshold at time `n`. -/
def reachesLowerDeviationThresholdStepEvent (delta : ℝ) (n : ℕ) :
    Set StepPath :=
  (lowerDeviationStepEvent delta n)ᶜ

lemma measurableSet_lowerDeviationSet (delta : ℝ) (n : ℕ) :
    MeasurableSet (lowerDeviationSet delta n) := by
  exact measurableSet_lt
    ((measurable_of_countable (fun u : Fin (n + 1) → Point ↦
      (maxLocalTimePrefix u : ℝ))).comp (measurable_pathPrefix n))
    measurable_const

lemma measurableSet_lowerDeviationStepEvent (delta : ℝ) (n : ℕ) :
    MeasurableSet (lowerDeviationStepEvent delta n) := by
  exact measurable_trajectory
    (measurableSet_lowerDeviationSet delta n)

lemma measurableSet_reachesLowerDeviationThresholdStepEvent
    (delta : ℝ) (n : ℕ) :
    MeasurableSet (reachesLowerDeviationThresholdStepEvent delta n) := by
  exact (measurableSet_lowerDeviationStepEvent delta n).compl

lemma mem_reachesLowerDeviationThresholdStepEvent_iff
    {omega : StepPath} {delta : ℝ} {n : ℕ} :
    omega ∈ reachesLowerDeviationThresholdStepEvent delta n ↔
      lowerDeviationThreshold delta n ≤
        (maxLocalTime (trajectory omega) n : ℝ) := by
  simp [reachesLowerDeviationThresholdStepEvent, lowerDeviationStepEvent,
    lowerDeviationSet]

/-! ## Finite all-block failure events used by amplification -/

/-- Every block in `blocks` fails.  This is the exact finite intersection
occurring in the independent-block amplification lemmas. -/
def allBlockFailures {I : Type*} (success : I → Set StepPath)
    (blocks : Finset I) : Set StepPath :=
  ⋂ i ∈ blocks, (success i)ᶜ

/-- At least one selected block succeeds. -/
def anyBlockSuccess {I : Type*} (success : I → Set StepPath)
    (blocks : Finset I) : Set StepPath :=
  ⋃ i ∈ blocks, success i

lemma measurableSet_allBlockFailures {I : Type*}
    (success : I → Set StepPath) (blocks : Finset I)
    (hmeas : ∀ i ∈ blocks, MeasurableSet (success i)) :
    MeasurableSet (allBlockFailures success blocks) := by
  exact blocks.measurableSet_biInter fun i hi ↦ (hmeas i hi).compl

lemma measurableSet_anyBlockSuccess {I : Type*}
    (success : I → Set StepPath) (blocks : Finset I)
    (hmeas : ∀ i ∈ blocks, MeasurableSet (success i)) :
    MeasurableSet (anyBlockSuccess success blocks) := by
  exact blocks.measurableSet_biUnion hmeas

lemma allBlockFailures_eq_compl_anyBlockSuccess {I : Type*}
    (success : I → Set StepPath) (blocks : Finset I) :
    allBlockFailures success blocks = (anyBlockSuccess success blocks)ᶜ := by
  ext omega
  simp [allBlockFailures, anyBlockSuccess]

/-- The exact global-failure event used for Proposition 1.3, exposed under a
name suitable for the generic `BlockAmplification` interface. -/
def proposition13GlobalFailureEvent (delta : ℝ) (n : ℕ) : Set StepPath :=
  (reachesLowerDeviationThresholdStepEvent delta n)ᶜ

lemma proposition13GlobalFailureEvent_eq (delta : ℝ) (n : ℕ) :
    proposition13GlobalFailureEvent delta n = lowerDeviationStepEvent delta n := by
  simp [proposition13GlobalFailureEvent,
    reachesLowerDeviationThresholdStepEvent]

lemma measurableSet_proposition13GlobalFailureEvent (delta : ℝ) (n : ℕ) :
    MeasurableSet (proposition13GlobalFailureEvent delta n) := by
  rw [proposition13GlobalFailureEvent_eq]
  exact measurableSet_lowerDeviationStepEvent delta n

end

end Erdos1165.Proposition13Measurability

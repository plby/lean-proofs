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

import ErdosProblems.Erdos1165.TerminalSequentialVisitLaw
import ErdosProblems.Erdos1165.MarkedTerminalDisintegration
import ErdosProblems.Erdos1165.GreenHarnack

/-!
# Boundary-visit kernels retaining the exit mark

`BoundaryVisitLaw` records only the number of visits made before a literal
vertex-boundary hit.  The stopped skeleton used in Appendix A must also retain
the endpoint of that hit (and, more generally, any measurable condition on
the remaining fresh path).  This file supplies that marked version.

The construction is deliberately prior to any Harnack estimate.  Its only
probabilistic input is strong Markov, first at the target hit and then at each
positive return to the target.  Consequently the final escaping piece may
carry an arbitrary measurable mark.  Singleton boundary marks give the
joint visit-count/exit-point kernel used by marked stopped disintegration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.MarkedBoundaryVisitKernel

open BoundaryVisitRegeneration BoundaryVisitLaw SequentialAnnularKernel
open TerminalExcursionBridge
open TerminalSequentialVisitLaw
open BoundaryStoppedHarnack GreenHarnack
open Annulus AnnulusHarnack

noncomputable section

/-! ## Literal boundary-exit marks -/

/-- First visit to `boundary` by the walk whose absolute starting point is
`start`.  The clock is expressed in the fresh increment coordinates. -/
noncomputable def boundaryExitTime
    (boundary : Set Point) (start : Point) : StepPath → WithTop ℕ :=
  firstHitSetAfter zeroClock (relativeBoundary boundary start)

theorem isStoppingTime_boundaryExitTime
    (boundary : Set Point) (start : Point) :
    IsStoppingTime incrementFiltration (boundaryExitTime boundary start) :=
  isStoppingTime_firstHitSetAfter isStoppingTime_zeroClock _

/-- The first literal boundary hit is finite and its absolute endpoint lies
in `mark`.  Taking `mark = {z}` retains an exact exit point. -/
def boundaryExitMarkedSteps
    (boundary mark : Set Point) (start : Point) : Set StepPath :=
  {omega | boundaryExitTime boundary start omega < ⊤ ∧
    start + stoppedPosition (boundaryExitTime boundary start) omega ∈ mark}

theorem measurableSet_boundaryExitMarkedSteps
    (boundary mark : Set Point) (start : Point) :
    MeasurableSet (boundaryExitMarkedSteps boundary mark start) := by
  have heq : boundaryExitMarkedSteps boundary mark start =
      ⋃ n : ℕ,
        {omega | boundaryExitTime boundary start omega = (n : WithTop ℕ)} ∩
          {omega | start + trajectory omega n ∈ mark} := by
    ext omega
    simp only [boundaryExitMarkedSteps, mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨hfinite, hmark⟩
      have hne : boundaryExitTime boundary start omega ≠ ⊤ :=
        WithTop.lt_top_iff_ne_top.mp hfinite
      cases htime : boundaryExitTime boundary start omega with
      | top => exact (hne htime).elim
      | coe n =>
          refine ⟨n, rfl, ?_⟩
          simpa only [stoppedPosition, htime, WithTop.untopD_coe] using hmark
    · rintro ⟨n, htime, hmark⟩
      refine ⟨htime ▸ WithTop.coe_lt_top n, ?_⟩
      rw [stoppedPosition_eq_of_eq htime]
      exact hmark
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (incrementFiltration.le n _
      ((isStoppingTime_boundaryExitTime boundary start).measurableSet_eq n)).inter
    (incrementFiltration.le n _
      (measurableSet_trajectory_mem_incrementFiltration n
        {z | start + z ∈ mark}))

lemma boundaryExitTime_eq_of_absoluteBoundaryFirstAt
    {boundary : Set Point} {start : Point} {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N) :
    boundaryExitTime boundary start omega = N := by
  apply (firstHitSetAfter_eq_coe_iff zeroClock
    (relativeBoundary boundary start) omega N).2
  refine ⟨by simp [zeroClock], ?_, ?_⟩
  · change start + trajectory omega N ∈ boundary
    simpa only [PlanarPotential.trajectoryFrom] using hfirst.1
  · intro q hq hcandidate
    have hmem := hcandidate.2
    change start + trajectory omega q ∈ boundary at hmem
    exact hfirst.2 q hq hmem

lemma mem_boundaryExitMarkedSteps_iff_of_absoluteBoundaryFirstAt
    {boundary mark : Set Point} {start : Point} {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt boundary start omega N) :
    omega ∈ boundaryExitMarkedSteps boundary mark start ↔
      PlanarPotential.trajectoryFrom start omega N ∈ mark := by
  have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
  change (boundaryExitTime boundary start omega < ⊤ ∧
      start + stoppedPosition (boundaryExitTime boundary start) omega ∈ mark) ↔ _
  rw [htime, stoppedPosition_eq_of_eq htime]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨WithTop.coe_lt_top N, h⟩

lemma mem_boundaryExitMarkedSteps_iff_exists_first
    (boundary mark : Set Point) (start : Point) (omega : StepPath) :
    omega ∈ boundaryExitMarkedSteps boundary mark start ↔
      ∃ N : ℕ, AbsoluteBoundaryFirstAt boundary start omega N ∧
        PlanarPotential.trajectoryFrom start omega N ∈ mark := by
  constructor
  · rintro ⟨hfinite, hmark⟩
    have hne : boundaryExitTime boundary start omega ≠ ⊤ :=
      WithTop.lt_top_iff_ne_top.mp hfinite
    lift boundaryExitTime boundary start omega to ℕ using hne with N hN
    have htime : boundaryExitTime boundary start omega = N := hN.symm
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (relativeBoundary boundary start) omega N).mp htime
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · change start + trajectory omega N ∈ boundary
      exact hspec.2.1
    · intro q hq hqboundary
      exact hspec.2.2 q hq ⟨by simp [zeroClock], hqboundary⟩
    · rw [stoppedPosition_eq_of_eq htime] at hmark
      simpa only [PlanarPotential.trajectoryFrom] using hmark
  · rintro ⟨N, hfirst, hmark⟩
    exact (mem_boundaryExitMarkedSteps_iff_of_absoluteBoundaryFirstAt hfirst).2 hmark

/-- The unmarked skeleton kernel, refined by an arbitrary set of permitted
exit endpoints. -/
def skeletonExitMarkKernel
    (boundary mark : Set Point) (start : Point) : ℝ≥0∞ :=
  fairSteps (boundaryExitMarkedSteps boundary mark start)

/-- Singleton form of `skeletonExitMarkKernel`. -/
def skeletonExitKernel
    (boundary : Set Point) (start exit : Point) : ℝ≥0∞ :=
  skeletonExitMarkKernel boundary {exit} start

/-! ## A marked positive-geometric regeneration atom -/

/-- Positive target-visit atoms with an arbitrary measurable condition on
the final escaping fresh path.  The condition is imposed only after the last
return, so it may encode an exit endpoint or any future boundary weight. -/
def positiveMarkedVisitAtom
    (boundary : Set Point) (terminal : Set StepPath) : ℕ → Set StepPath
  | 0 => ∅
  | 1 => (positiveReturnBeforeBoundary boundary)ᶜ ∩ terminal
  | k + 2 => positiveReturnBeforeBoundary boundary ∩
      postWithTopStoppingSteps firstPositiveReturnTime ⁻¹'
        positiveMarkedVisitAtom boundary terminal (k + 1)

@[simp] theorem positiveMarkedVisitAtom_zero
    (boundary : Set Point) (terminal : Set StepPath) :
    positiveMarkedVisitAtom boundary terminal 0 = ∅ := rfl

@[simp] theorem positiveMarkedVisitAtom_one
    (boundary : Set Point) (terminal : Set StepPath) :
    positiveMarkedVisitAtom boundary terminal 1 =
      (positiveReturnBeforeBoundary boundary)ᶜ ∩ terminal := rfl

theorem positiveMarkedVisitAtom_succ_succ
    (boundary : Set Point) (terminal : Set StepPath) (k : ℕ) :
    positiveMarkedVisitAtom boundary terminal (k + 2) =
      positiveReturnBeforeBoundary boundary ∩
        postWithTopStoppingSteps firstPositiveReturnTime ⁻¹'
          positiveMarkedVisitAtom boundary terminal (k + 1) := rfl

theorem measurableSet_positiveMarkedVisitAtom
    (boundary : Set Point) {terminal : Set StepPath}
    (hterminal : MeasurableSet terminal) :
    ∀ k, MeasurableSet (positiveMarkedVisitAtom boundary terminal k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
      exact (measurableSet_positiveReturnBeforeBoundary boundary).compl.inter
        hterminal
  | more k _ ih =>
      rw [positiveMarkedVisitAtom_succ_succ]
      exact (measurableSet_positiveReturnBeforeBoundary boundary).inter
        (ih.preimage
          (measurable_postWithTopStoppingSteps
            isStoppingTime_firstPositiveReturnTime))

/-- One marked regeneration step factors exactly. -/
theorem measure_positiveMarkedVisitAtom_succ_succ
    (boundary : Set Point) {terminal : Set StepPath}
    (hterminal : MeasurableSet terminal) (k : ℕ) :
    fairSteps (positiveMarkedVisitAtom boundary terminal (k + 2)) =
      fairSteps (positiveReturnBeforeBoundary boundary) *
        fairSteps (positiveMarkedVisitAtom boundary terminal (k + 1)) := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    isStoppingTime_firstPositiveReturnTime
    (isMeasurableAtWithTopStopping_positiveReturnBeforeBoundary boundary)
    (measurableSet_positiveMarkedVisitAtom boundary hterminal (k + 1))
  have hfinite : positiveReturnBeforeBoundary boundary ∩
      {omega | firstPositiveReturnTime omega < ⊤} =
        positiveReturnBeforeBoundary boundary := by
    apply Set.Subset.antisymm inter_subset_left
    intro omega homega
    exact ⟨homega,
      positiveReturnBeforeBoundary_subset_finite boundary homega⟩
  rw [hfinite] at hmarkov
  simpa only [positiveMarkedVisitAtom_succ_succ] using hmarkov

/-- Closed marked positive-geometric formula.  The last factor is the exact
killed, marked escaping-piece mass. -/
theorem measure_positiveMarkedVisitAtom_succ
    (boundary : Set Point) {terminal : Set StepPath}
    (hterminal : MeasurableSet terminal) (k : ℕ) :
    fairSteps (positiveMarkedVisitAtom boundary terminal (k + 1)) =
      fairSteps (positiveReturnBeforeBoundary boundary) ^ k *
        fairSteps ((positiveReturnBeforeBoundary boundary)ᶜ ∩ terminal) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by omega,
        measure_positiveMarkedVisitAtom_succ_succ boundary hterminal k, ih,
        pow_succ]
      ac_rfl

/-! ## Adding the first-target Bernoulli step -/

/-- Visit atom marked by `initialTerminal` when the target is missed and by
`targetTerminal` (in target-relative coordinates) after a target hit.  The
two arguments make the zero-visit and positive-visit cases usable with the
same absolute exit mark. -/
def markedBoundaryVisitAtom
    (boundary : Set Point) (target start : Point)
    (initialTerminal targetTerminal : Set StepPath) : ℕ → Set StepPath
  | 0 => (boundaryHitSteps boundary target start)ᶜ ∩ initialTerminal
  | k + 1 => boundaryHitSteps boundary target start ∩
      postWithTopStoppingSteps (targetHitTime start target) ⁻¹'
        positiveMarkedVisitAtom (relativeBoundary boundary target)
          targetTerminal (k + 1)

theorem measurableSet_markedBoundaryVisitAtom
    (boundary : Set Point) (target start : Point)
    {initialTerminal targetTerminal : Set StepPath}
    (hinitial : MeasurableSet initialTerminal)
    (htarget : MeasurableSet targetTerminal) :
    ∀ k, MeasurableSet (markedBoundaryVisitAtom boundary target start
      initialTerminal targetTerminal k) := by
  intro k
  cases k with
  | zero =>
      exact (measurableSet_boundaryHitSteps boundary target start).compl.inter
        hinitial
  | succ k =>
      exact (measurableSet_boundaryHitSteps boundary target start).inter
        ((measurableSet_positiveMarkedVisitAtom
          (relativeBoundary boundary target) htarget (k + 1)).preimage
            (measurable_postWithTopStoppingSteps
              (isStoppingTime_targetHitTime start target)))

/-- Strong Markov at the first target hit preserves the complete marked
escaping-piece event. -/
theorem measure_markedBoundaryVisitAtom_succ
    (boundary : Set Point) (target start : Point)
    {initialTerminal targetTerminal : Set StepPath}
    (htarget : MeasurableSet targetTerminal) (k : ℕ) :
    fairSteps (markedBoundaryVisitAtom boundary target start
      initialTerminal targetTerminal (k + 1)) =
      fairSteps (boundaryHitSteps boundary target start) *
        fairSteps (positiveMarkedVisitAtom
          (relativeBoundary boundary target) targetTerminal (k + 1)) := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    (isStoppingTime_targetHitTime start target)
    (isMeasurableAtWithTopStopping_boundaryHitSteps boundary target start)
    (measurableSet_positiveMarkedVisitAtom
      (relativeBoundary boundary target) htarget (k + 1))
  have hfinite : boundaryHitSteps boundary target start ∩
      {omega | targetHitTime start target omega < ⊤} =
        boundaryHitSteps boundary target start := by
    apply Set.Subset.antisymm inter_subset_left
    intro omega homega
    exact ⟨homega,
      boundaryHitSteps_subset_targetHitTime_finite boundary target start homega⟩
  rw [hfinite] at hmarkov
  simpa only [markedBoundaryVisitAtom] using hmarkov

/-- Closed first-hit/marked-geometric factorization. -/
theorem measure_markedBoundaryVisitAtom_succ_closed
    (boundary : Set Point) (target start : Point)
    {initialTerminal targetTerminal : Set StepPath}
    (htarget : MeasurableSet targetTerminal) (k : ℕ) :
    fairSteps (markedBoundaryVisitAtom boundary target start
      initialTerminal targetTerminal (k + 1)) =
      fairSteps (boundaryHitSteps boundary target start) *
        fairSteps (positiveReturnBeforeBoundary
          (relativeBoundary boundary target)) ^ k *
        fairSteps ((positiveReturnBeforeBoundary
          (relativeBoundary boundary target))ᶜ ∩ targetTerminal) := by
  rw [measure_markedBoundaryVisitAtom_succ boundary target start htarget k,
    measure_positiveMarkedVisitAtom_succ
      (relativeBoundary boundary target) htarget k]
  ac_rfl

/-! ## Exit-mark and singleton kernels -/

/-- The final boundary-exit mark viewed in the coordinates after the first
target hit. -/
def targetRelativeExitMarkSteps
    (boundary mark : Set Point) (target : Point) : Set StepPath :=
  boundaryExitMarkedSteps (relativeBoundary boundary target)
    (relativeBoundary mark target) 0

theorem measurableSet_targetRelativeExitMarkSteps
    (boundary mark : Set Point) (target : Point) :
    MeasurableSet (targetRelativeExitMarkSteps boundary mark target) :=
  measurableSet_boundaryExitMarkedSteps _ _ _

/-- Exact joint atom: `k` target visits followed by the first literal
boundary hit at an endpoint in `mark`. -/
def boundaryVisitExitMarkAtom
    (boundary : Set Point) (target start : Point) (mark : Set Point) (k : ℕ) :
    Set StepPath :=
  markedBoundaryVisitAtom boundary target start
    (boundaryExitMarkedSteps boundary mark start)
    (targetRelativeExitMarkSteps boundary mark target) k

theorem measurableSet_boundaryVisitExitMarkAtom
    (boundary : Set Point) (target start : Point) (mark : Set Point) (k : ℕ) :
    MeasurableSet (boundaryVisitExitMarkAtom boundary target start mark k) :=
  measurableSet_markedBoundaryVisitAtom boundary target start
    (measurableSet_boundaryExitMarkedSteps boundary mark start)
    (measurableSet_targetRelativeExitMarkSteps boundary mark target) k

/-- Exact joint visit-count/exit-mark kernel. -/
def boundaryVisitExitMarkKernel
    (boundary : Set Point) (target start : Point) (k : ℕ) (mark : Set Point) :
    ℝ≥0∞ :=
  fairSteps (boundaryVisitExitMarkAtom boundary target start mark k)

/-- The marked kernel at a singleton exit point. -/
def boundaryVisitExitKernel
    (boundary : Set Point) (target start : Point) (k : ℕ) (exit : Point) :
    ℝ≥0∞ :=
  boundaryVisitExitMarkKernel boundary target start k {exit}

/-! ## Regenerative identities for the exit skeleton -/

/-- Final escaping-piece kernel from the target-relative origin. -/
def killedPositiveReturnExitMarkKernel
    (boundary mark : Set Point) : ℝ≥0∞ :=
  fairSteps ((positiveReturnBeforeBoundary boundary)ᶜ ∩
    boundaryExitMarkedSteps boundary mark 0)

private lemma positiveReturn_data
    {boundary : Set Point} {omega : StepPath} {r : ℕ}
    (hreturn : omega ∈ positiveReturnBeforeBoundary boundary)
    (hr : firstPositiveReturnTime omega = r) :
    omega ∈ avoidsBoundaryBefore boundary r := by
  obtain ⟨m, hm, havoid⟩ := Set.mem_iUnion.mp hreturn
  have hmr : m = r := WithTop.coe_eq_coe.mp (hm.symm.trans hr)
  simpa only [hmr] using havoid

private lemma boundaryExitMarkedSteps_shift_firstPositiveReturn_iff
    (boundary mark : Set Point) (hzero : (0 : Point) ∉ boundary)
    {omega : StepPath} {r : ℕ}
    (hreturn : omega ∈ positiveReturnBeforeBoundary boundary)
    (hr : firstPositiveReturnTime omega = r) :
    omega ∈ boundaryExitMarkedSteps boundary mark 0 ↔
      shiftSteps r omega ∈ boundaryExitMarkedSteps boundary mark 0 := by
  have hrspec := firstPositiveReturnTime_spec hr
  have havoid := positiveReturn_data hreturn hr
  constructor
  · intro hexit
    obtain ⟨N, hfirstAbs, hmark⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary mark 0 omega).1 hexit
    have hfirst : BoundaryFirstAt boundary omega N := by
      simpa [BoundaryFirstAt, AbsoluteBoundaryFirstAt,
        PlanarPotential.trajectoryFrom] using hfirstAbs
    obtain ⟨r', hr'N, hr'⟩ :=
      (positiveReturnBeforeBoundary_iff_exists_return_lt hzero hfirst).1 hreturn
    have hrr : r' = r := WithTop.coe_eq_coe.mp (hr'.symm.trans hr)
    subst r'
    have hshiftFirst := boundaryFirstAt_shift_firstPositiveReturn hfirst hr'N hr
    have hshiftAbs : AbsoluteBoundaryFirstAt boundary 0
        (shiftSteps r omega) (N - r) := by
      simpa [BoundaryFirstAt, AbsoluteBoundaryFirstAt,
        PlanarPotential.trajectoryFrom] using hshiftFirst
    refine (mem_boundaryExitMarkedSteps_iff_exists_first
      boundary mark 0 (shiftSteps r omega)).2 ⟨N - r, hshiftAbs, ?_⟩
    have hshift := trajectory_add_sub_trajectory omega r (N - r)
    rw [Nat.add_sub_of_le hr'N.le, hrspec.2.1, sub_zero] at hshift
    simpa only [PlanarPotential.trajectoryFrom, zero_add, ← hshift] using hmark
  · intro hexit
    obtain ⟨M, hshiftFirstAbs, hshiftMark⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary mark 0 (shiftSteps r omega)).1 hexit
    have hshiftFirst : BoundaryFirstAt boundary (shiftSteps r omega) M := by
      simpa [BoundaryFirstAt, AbsoluteBoundaryFirstAt,
        PlanarPotential.trajectoryFrom] using hshiftFirstAbs
    have hfirst : BoundaryFirstAt boundary omega (r + M) := by
      constructor
      · have hshift := trajectory_add_sub_trajectory omega r M
        rw [hrspec.2.1, sub_zero] at hshift
        rw [hshift]
        exact hshiftFirst.1
      · intro q hq
        by_cases hqr : q < r
        · exact havoid q hqr
        · have hrq : r ≤ q := Nat.le_of_not_gt hqr
          have hqeq : r + (q - r) = q := Nat.add_sub_of_le hrq
          have hdiff : q - r < M := by omega
          have hshift := trajectory_add_sub_trajectory omega r (q - r)
          rw [hqeq, hrspec.2.1, sub_zero] at hshift
          rw [hshift]
          exact hshiftFirst.2 (q - r) hdiff
    have hfirstAbs : AbsoluteBoundaryFirstAt boundary 0 omega (r + M) := by
      simpa [BoundaryFirstAt, AbsoluteBoundaryFirstAt,
        PlanarPotential.trajectoryFrom] using hfirst
    refine (mem_boundaryExitMarkedSteps_iff_exists_first
      boundary mark 0 omega).2 ⟨r + M, hfirstAbs, ?_⟩
    have hshift := trajectory_add_sub_trajectory omega r M
    rw [hrspec.2.1, sub_zero] at hshift
    simpa only [PlanarPotential.trajectoryFrom, zero_add, hshift] using hshiftMark

lemma positiveReturn_inter_boundaryExitMarkedSteps_eq_post
    (boundary mark : Set Point) (hzero : (0 : Point) ∉ boundary) :
    positiveReturnBeforeBoundary boundary ∩
        boundaryExitMarkedSteps boundary mark 0 =
      positiveReturnBeforeBoundary boundary ∩
        postWithTopStoppingSteps firstPositiveReturnTime ⁻¹'
          boundaryExitMarkedSteps boundary mark 0 := by
  ext omega
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hreturn, hexit⟩
    obtain ⟨r, hr, _havoid⟩ := Set.mem_iUnion.mp hreturn
    have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq hr
    refine ⟨hreturn, ?_⟩
    rw [hpost]
    exact (boundaryExitMarkedSteps_shift_firstPositiveReturn_iff
      boundary mark hzero hreturn hr).1 hexit
  · rintro ⟨hreturn, hexit⟩
    obtain ⟨r, hr, _havoid⟩ := Set.mem_iUnion.mp hreturn
    have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq hr
    refine ⟨hreturn, ?_⟩
    rw [hpost] at hexit
    exact (boundaryExitMarkedSteps_shift_firstPositiveReturn_iff
      boundary mark hzero hreturn hr).2 hexit

/-- The marked exit skeleton splits into a killed last piece and a returned
copy of the entire skeleton. -/
theorem skeletonExitMarkKernel_eq_killed_add_return_mul
    (boundary mark : Set Point) (hzero : (0 : Point) ∉ boundary) :
    skeletonExitMarkKernel boundary mark 0 =
      killedPositiveReturnExitMarkKernel boundary mark +
        fairSteps (positiveReturnBeforeBoundary boundary) *
          skeletonExitMarkKernel boundary mark 0 := by
  let R := positiveReturnBeforeBoundary boundary
  let C := boundaryExitMarkedSteps boundary mark 0
  have hrestart : fairSteps (R ∩ C) = fairSteps R * fairSteps C := by
    have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
      isStoppingTime_firstPositiveReturnTime
      (isMeasurableAtWithTopStopping_positiveReturnBeforeBoundary boundary)
      (measurableSet_boundaryExitMarkedSteps boundary mark 0)
    have hfinite : R ∩ {omega | firstPositiveReturnTime omega < ⊤} = R := by
      apply Set.Subset.antisymm inter_subset_left
      intro omega homega
      exact ⟨homega, positiveReturnBeforeBoundary_subset_finite boundary homega⟩
    rw [hfinite] at hmarkov
    rw [positiveReturn_inter_boundaryExitMarkedSteps_eq_post
      boundary mark hzero]
    exact hmarkov
  have hpartition : C = (Rᶜ ∩ C) ∪ (R ∩ C) := by
    ext omega
    by_cases hR : omega ∈ R <;> simp [hR]
  have hdisjoint : Disjoint (Rᶜ ∩ C) (R ∩ C) := by
    exact Set.disjoint_left.2 fun _ hx hy ↦ hx.1 hy.1
  change fairSteps C = fairSteps (Rᶜ ∩ C) + fairSteps R * fairSteps C
  calc
    fairSteps C = fairSteps ((Rᶜ ∩ C) ∪ (R ∩ C)) :=
      congrArg fairSteps hpartition
    _ = fairSteps (Rᶜ ∩ C) + fairSteps (R ∩ C) :=
      measure_union hdisjoint
        ((measurableSet_positiveReturnBeforeBoundary boundary).inter
          (measurableSet_boundaryExitMarkedSteps boundary mark 0))
    _ = fairSteps (Rᶜ ∩ C) + fairSteps R * fairSteps C := by rw [hrestart]

/-- ENNReal form of the escape parameter used by the geometric visit law. -/
lemma ofReal_escapeBeforePositiveReturnProbability
    (boundary : Set Point) :
    ENNReal.ofReal (escapeBeforePositiveReturnProbability boundary) =
      1 - fairSteps (positiveReturnBeforeBoundary boundary) := by
  have hle : fairSteps (positiveReturnBeforeBoundary boundary) ≤ 1 := prob_le_one
  have hsub :
      (1 - fairSteps (positiveReturnBeforeBoundary boundary)).toReal =
        1 - (fairSteps (positiveReturnBeforeBoundary boundary)).toReal := by
    simpa using ENNReal.toReal_sub_of_le hle (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
  rw [escapeBeforePositiveReturnProbability, measureReal_def, ← hsub]
  exact ENNReal.ofReal_toReal (by finiteness)

lemma returnMass_eq_ofReal_one_sub_escape
    (boundary : Set Point) :
    fairSteps (positiveReturnBeforeBoundary boundary) =
      ENNReal.ofReal (1 - escapeBeforePositiveReturnProbability boundary) := by
  have hp1 : escapeBeforePositiveReturnProbability boundary ≤ 1 := by
    unfold escapeBeforePositiveReturnProbability
    have hnonneg :
        0 ≤ fairSteps.real (positiveReturnBeforeBoundary boundary) :=
      measureReal_nonneg
    linarith
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top fairSteps _) (by simp)).mp
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]
  unfold escapeBeforePositiveReturnProbability
  simp only [measureReal_def]
  ring

/-- Exact killed-piece identity: the last marked escape has escape mass
times the full marked exit skeleton. -/
theorem killedPositiveReturnExitMarkKernel_eq_escape_mul_skeleton
    (boundary mark : Set Point) (hzero : (0 : Point) ∉ boundary) :
    killedPositiveReturnExitMarkKernel boundary mark =
      ENNReal.ofReal (escapeBeforePositiveReturnProbability boundary) *
        skeletonExitMarkKernel boundary mark 0 := by
  have hadd := skeletonExitMarkKernel_eq_killed_add_return_mul
    boundary mark hzero
  have hkfinite : killedPositiveReturnExitMarkKernel boundary mark ≠ ⊤ :=
    measure_ne_top fairSteps _
  have hsfinite : skeletonExitMarkKernel boundary mark 0 ≠ ⊤ :=
    measure_ne_top fairSteps _
  have hefinite : ENNReal.ofReal
      (escapeBeforePositiveReturnProbability boundary) ≠ ⊤ := by simp
  apply (ENNReal.toReal_eq_toReal_iff' hkfinite
    (ENNReal.mul_ne_top hefinite hsfinite)).mp
  have haddReal := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hkfinite
      (ENNReal.mul_ne_top (measure_ne_top fairSteps _) hsfinite),
    ENNReal.toReal_mul] at haddReal
  rw [ofReal_escapeBeforePositiveReturnProbability,
    ENNReal.toReal_mul, ENNReal.toReal_sub_of_le prob_le_one (by norm_num)]
  norm_num only [ENNReal.toReal_one]
  nlinarith

lemma targetRelativeExitMarkSteps_eq_at_target
    (boundary mark : Set Point) (target : Point) :
    targetRelativeExitMarkSteps boundary mark target =
      boundaryExitMarkedSteps boundary mark target := by
  have hboundary : relativeBoundary (relativeBoundary boundary target) 0 =
      relativeBoundary boundary target := by
    ext z
    simp only [relativeBoundary, mem_setOf_eq, zero_add]
  have htime : boundaryExitTime (relativeBoundary boundary target) 0 =
      boundaryExitTime boundary target := by
    unfold boundaryExitTime
    rw [hboundary]
  unfold targetRelativeExitMarkSteps boundaryExitMarkedSteps
  rw [htime]
  ext omega
  simp only [relativeBoundary, mem_setOf_eq, zero_add]

private lemma boundaryHitSteps_avoids_before_targetHit
    {boundary : Set Point} {target start : Point}
    {omega : StepPath} {t : ℕ}
    (hhit : omega ∈ boundaryHitSteps boundary target start)
    (ht : targetHitTime start target omega = t) :
    omega ∈ avoidsBoundaryFromBefore boundary start t := by
  have hboth : omega ∈ boundaryHitSteps boundary target start ∩
      {omega | targetHitTime start target omega = (t : WithTop ℕ)} :=
    ⟨hhit, ht⟩
  rw [boundaryHitSteps_inter_targetHitTime_eq] at hboth
  exact hboth.2

private lemma boundaryExitMarkedSteps_shift_targetHit_iff
    (boundary mark : Set Point) (target start : Point)
    (htarget : target ∉ boundary)
    {omega : StepPath} {t : ℕ}
    (hhit : omega ∈ boundaryHitSteps boundary target start)
    (ht : targetHitTime start target omega = t) :
    omega ∈ boundaryExitMarkedSteps boundary mark start ↔
      shiftSteps t omega ∈ targetRelativeExitMarkSteps boundary mark target := by
  have htTarget := targetHitTime_eq_implies_trajectoryFrom ht
  have htDisplacement : trajectory omega t = target - start := by
    unfold PlanarPotential.trajectoryFrom at htTarget
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using htTarget)
  have havoid := boundaryHitSteps_avoids_before_targetHit hhit ht
  constructor
  · intro hexit
    obtain ⟨N, hfirst, hmark⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        boundary mark start omega).1 hexit
    have htNTop := targetHitTime_lt_boundary_of_hit htarget hfirst hhit
    rw [ht] at htNTop
    have htN : t < N := WithTop.coe_lt_coe.mp htNTop
    have hrelative := relativeBoundaryFirstAt_after_targetHit hfirst ht htN
    have hrelativeAbs : AbsoluteBoundaryFirstAt
        (relativeBoundary boundary target) 0 (shiftSteps t omega) (N - t) := by
      simpa [BoundaryFirstAt, AbsoluteBoundaryFirstAt,
        PlanarPotential.trajectoryFrom] using hrelative
    apply (mem_boundaryExitMarkedSteps_iff_exists_first
      (relativeBoundary boundary target) (relativeBoundary mark target) 0
      (shiftSteps t omega)).2
    refine ⟨N - t, hrelativeAbs, ?_⟩
    simp only [PlanarPotential.trajectoryFrom, zero_add, relativeBoundary,
      mem_setOf_eq]
    rw [← trajectory_add_sub_trajectory, Nat.add_sub_of_le htN.le,
      htDisplacement]
    have heq : target + (trajectory omega N - (target - start)) =
        start + trajectory omega N := by abel
    rw [heq]
    simpa only [PlanarPotential.trajectoryFrom] using hmark
  · intro hexit
    obtain ⟨M, hrelativeAbs, hrelativeMark⟩ :=
      (mem_boundaryExitMarkedSteps_iff_exists_first
        (relativeBoundary boundary target) (relativeBoundary mark target) 0
        (shiftSteps t omega)).1 hexit
    have hrelative : BoundaryFirstAt (relativeBoundary boundary target)
        (shiftSteps t omega) M := by
      simpa [BoundaryFirstAt, AbsoluteBoundaryFirstAt,
        PlanarPotential.trajectoryFrom] using hrelativeAbs
    have hfirst : AbsoluteBoundaryFirstAt boundary start omega (t + M) := by
      constructor
      · change start + trajectory omega (t + M) ∈ boundary
        have hshift := trajectory_add_sub_trajectory omega t M
        have heq : start + trajectory omega (t + M) =
            target + trajectory (shiftSteps t omega) M := by
          rw [← hshift, htDisplacement]
          abel
        rw [heq]
        exact hrelative.1
      · intro q hq
        by_cases hqt : q < t
        · exact havoid q hqt
        · have htq : t ≤ q := Nat.le_of_not_gt hqt
          have hqeq : t + (q - t) = q := Nat.add_sub_of_le htq
          have hdiff : q - t < M := by omega
          change start + trajectory omega q ∉ boundary
          have hshift := trajectory_add_sub_trajectory omega t (q - t)
          rw [hqeq] at hshift
          have heq : start + trajectory omega q =
              target + trajectory (shiftSteps t omega) (q - t) := by
            rw [← hshift, htDisplacement]
            abel
          rw [heq]
          exact hrelative.2 (q - t) hdiff
    apply (mem_boundaryExitMarkedSteps_iff_exists_first
      boundary mark start omega).2
    refine ⟨t + M, hfirst, ?_⟩
    change start + trajectory omega (t + M) ∈ mark
    simp only [PlanarPotential.trajectoryFrom, zero_add, relativeBoundary,
      mem_setOf_eq] at hrelativeMark
    have hshift := trajectory_add_sub_trajectory omega t M
    rw [← hshift, htDisplacement] at hrelativeMark
    have heq : target + (trajectory omega (t + M) - (target - start)) =
        start + trajectory omega (t + M) := by abel
    rw [heq] at hrelativeMark
    exact hrelativeMark

lemma boundaryHit_inter_boundaryExitMarkedSteps_eq_post
    (boundary mark : Set Point) (target start : Point)
    (htarget : target ∉ boundary) :
    boundaryHitSteps boundary target start ∩
        boundaryExitMarkedSteps boundary mark start =
      boundaryHitSteps boundary target start ∩
        postWithTopStoppingSteps (targetHitTime start target) ⁻¹'
          targetRelativeExitMarkSteps boundary mark target := by
  ext omega
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hhit, hexit⟩
    have hfinite := boundaryHitSteps_subset_targetHitTime_finite
      boundary target start hhit
    have hne := WithTop.lt_top_iff_ne_top.mp hfinite
    lift targetHitTime start target omega to ℕ using hne with t ht
    have ht' : targetHitTime start target omega = t := ht.symm
    refine ⟨hhit, ?_⟩
    rw [postWithTopStoppingSteps_eq_shiftSteps_of_eq ht']
    exact (boundaryExitMarkedSteps_shift_targetHit_iff
      boundary mark target start htarget hhit ht').1 hexit
  · rintro ⟨hhit, hexit⟩
    have hfinite := boundaryHitSteps_subset_targetHitTime_finite
      boundary target start hhit
    have hne := WithTop.lt_top_iff_ne_top.mp hfinite
    lift targetHitTime start target omega to ℕ using hne with t ht
    have ht' : targetHitTime start target omega = t := ht.symm
    refine ⟨hhit, ?_⟩
    rw [postWithTopStoppingSteps_eq_shiftSteps_of_eq ht'] at hexit
    exact (boundaryExitMarkedSteps_shift_targetHit_iff
      boundary mark target start htarget hhit ht').2 hexit

/-- Killed punctured-domain exit kernel: reach the marked part of the
boundary without first reaching `target`. -/
def killedPuncturedExitMarkKernel
    (boundary : Set Point) (target start : Point) (mark : Set Point) : ℝ≥0∞ :=
  fairSteps ((boundaryHitSteps boundary target start)ᶜ ∩
    boundaryExitMarkedSteps boundary mark start)

/-- Zero-visit additive identity.  A marked skeleton path either misses the
target before its boundary exit or hits the target and restarts from there. -/
theorem skeletonExitMarkKernel_eq_killedPunctured_add_hit_mul
    (boundary mark : Set Point) (target start : Point)
    (htarget : target ∉ boundary) :
    skeletonExitMarkKernel boundary mark start =
      killedPuncturedExitMarkKernel boundary target start mark +
        fairSteps (boundaryHitSteps boundary target start) *
          skeletonExitMarkKernel boundary mark target := by
  let H := boundaryHitSteps boundary target start
  let C := boundaryExitMarkedSteps boundary mark start
  let Ct := targetRelativeExitMarkSteps boundary mark target
  have hrestart : fairSteps (H ∩ C) = fairSteps H * fairSteps Ct := by
    have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
      (isStoppingTime_targetHitTime start target)
      (isMeasurableAtWithTopStopping_boundaryHitSteps boundary target start)
      (measurableSet_targetRelativeExitMarkSteps boundary mark target)
    have hfinite : H ∩ {omega | targetHitTime start target omega < ⊤} = H := by
      apply Set.Subset.antisymm inter_subset_left
      intro omega homega
      exact ⟨homega,
        boundaryHitSteps_subset_targetHitTime_finite boundary target start homega⟩
    rw [hfinite] at hmarkov
    rw [boundaryHit_inter_boundaryExitMarkedSteps_eq_post
      boundary mark target start htarget]
    exact hmarkov
  have hpartition : C = (Hᶜ ∩ C) ∪ (H ∩ C) := by
    ext omega
    by_cases hH : omega ∈ H <;> simp [hH]
  have hdisjoint : Disjoint (Hᶜ ∩ C) (H ∩ C) :=
    Set.disjoint_left.2 fun _ hx hy ↦ hx.1 hy.1
  have hCt : fairSteps Ct = skeletonExitMarkKernel boundary mark target := by
    dsimp only [Ct, skeletonExitMarkKernel]
    rw [targetRelativeExitMarkSteps_eq_at_target]
  change fairSteps C = fairSteps (Hᶜ ∩ C) +
    fairSteps H * skeletonExitMarkKernel boundary mark target
  calc
    fairSteps C = fairSteps ((Hᶜ ∩ C) ∪ (H ∩ C)) :=
      congrArg fairSteps hpartition
    _ = fairSteps (Hᶜ ∩ C) + fairSteps (H ∩ C) :=
      measure_union hdisjoint
        ((measurableSet_boundaryHitSteps boundary target start).inter
          (measurableSet_boundaryExitMarkedSteps boundary mark start))
    _ = fairSteps (Hᶜ ∩ C) + fairSteps H * fairSteps Ct := by rw [hrestart]
    _ = fairSteps (Hᶜ ∩ C) +
        fairSteps H * skeletonExitMarkKernel boundary mark target := by rw [hCt]

/-! ## Identification with the canonical literal marked atoms -/

theorem positiveMarkedVisitAtom_eq_inter_exitMark
    (boundary mark : Set Point) (hzero : (0 : Point) ∉ boundary) :
    ∀ k, positiveMarkedVisitAtom boundary
        (boundaryExitMarkedSteps boundary mark 0) k =
      positiveVisitAtom boundary k ∩
        boundaryExitMarkedSteps boundary mark 0 := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => rfl
  | more k _ ih =>
      rw [positiveMarkedVisitAtom_succ_succ,
        positiveVisitAtom_succ_succ, ih]
      have hrestart := positiveReturn_inter_boundaryExitMarkedSteps_eq_post
        boundary mark hzero
      ext omega
      have hpoint := Set.ext_iff.mp hrestart omega
      simp only [mem_inter_iff, mem_preimage] at hpoint ⊢
      constructor
      · rintro ⟨hreturn, hvisit, hpostMark⟩
        have hmark := (hpoint.mpr ⟨hreturn, hpostMark⟩).2
        exact ⟨⟨hreturn, hvisit⟩, hmark⟩
      · rintro ⟨⟨hreturn, hvisit⟩, hmark⟩
        have hpostMark := (hpoint.mp ⟨hreturn, hmark⟩).2
        exact ⟨hreturn, hvisit, hpostMark⟩

theorem boundaryVisitExitMarkAtom_eq_inter
    (boundary : Set Point) (target start : Point) (mark : Set Point)
    (htarget : target ∉ boundary) (k : ℕ) :
    boundaryVisitExitMarkAtom boundary target start mark k =
      boundaryVisitAtom boundary target start k ∩
        boundaryExitMarkedSteps boundary mark start := by
  cases k with
  | zero => rfl
  | succ k =>
      have hzeroRelative : (0 : Point) ∉ relativeBoundary boundary target := by
        simpa [relativeBoundary] using htarget
      rw [boundaryVisitExitMarkAtom, markedBoundaryVisitAtom,
        boundaryVisitAtom]
      unfold targetRelativeExitMarkSteps
      rw [
        positiveMarkedVisitAtom_eq_inter_exitMark
          (relativeBoundary boundary target) (relativeBoundary mark target)
          hzeroRelative (k + 1)]
      have hrestart := boundaryHit_inter_boundaryExitMarkedSteps_eq_post
        boundary mark target start htarget
      ext omega
      have hpoint := Set.ext_iff.mp hrestart omega
      simp only [mem_inter_iff, mem_preimage, targetRelativeExitMarkSteps]
        at hpoint ⊢
      constructor
      · rintro ⟨hhit, hvisit, hpostMark⟩
        have hmark := (hpoint.mpr ⟨hhit, hpostMark⟩).2
        exact ⟨⟨hhit, hvisit⟩, hmark⟩
      · rintro ⟨⟨hhit, hvisit⟩, hmark⟩
        have hpostMark := (hpoint.mp ⟨hhit, hmark⟩).2
        exact ⟨hhit, hvisit, hpostMark⟩

theorem boundaryExitMarkedSteps_singleton_eq_canonical
    (boundary : Set Point) (start exit : Point) :
    boundaryExitMarkedSteps boundary {exit} start =
      boundaryExitEndpointSteps boundary start exit := by
  ext omega
  rw [mem_boundaryExitMarkedSteps_iff_exists_first]
  constructor
  · rintro ⟨N, hfirst, hexit⟩
    exact Set.mem_iUnion.mpr ⟨N, hfirst, by simpa using hexit⟩
  · intro h
    obtain ⟨N, hfirst, hexit⟩ := Set.mem_iUnion.mp h
    exact ⟨N, hfirst, by simpa using hexit⟩

theorem boundaryVisitExitMarkAtom_singleton_eq_canonical
    (boundary : Set Point) (target start exit : Point)
    (htarget : target ∉ boundary) (k : ℕ) :
    boundaryVisitExitMarkAtom boundary target start {exit} k =
      boundaryVisitExitAtom boundary target start k exit := by
  rw [boundaryVisitExitMarkAtom_eq_inter boundary target start {exit} htarget k,
    boundaryExitMarkedSteps_singleton_eq_canonical]
  rfl

theorem skeletonExitKernel_eq_canonical
    (boundary : Set Point) (start exit : Point) :
    skeletonExitKernel boundary start exit =
      fairSteps (boundaryExitEndpointSteps boundary start exit) := by
  rw [skeletonExitKernel, skeletonExitMarkKernel,
    boundaryExitMarkedSteps_singleton_eq_canonical]

theorem boundaryVisitExitKernel_eq_canonical
    (boundary : Set Point) (target start exit : Point)
    (htarget : target ∉ boundary) (k : ℕ) :
    boundaryVisitExitKernel boundary target start k exit =
      fairSteps (boundaryVisitExitAtom boundary target start k exit) := by
  rw [boundaryVisitExitKernel, boundaryVisitExitMarkKernel,
    boundaryVisitExitMarkAtom_singleton_eq_canonical
      boundary target start exit htarget k]

/-- The zero-visit marked kernel is exactly the killed punctured-domain exit
kernel, without a recurrence or Harnack assumption. -/
theorem boundaryVisitExitMarkKernel_zero
    (boundary : Set Point) (target start : Point) (mark : Set Point) :
    boundaryVisitExitMarkKernel boundary target start 0 mark =
      killedPuncturedExitMarkKernel boundary target start mark := rfl

/-- For every positive visit count, the joint marked kernel factors into
the first-target mass, the intervening return masses, and the final killed
marked exit mass. -/
theorem boundaryVisitExitMarkKernel_succ
    (boundary : Set Point) (target start : Point) (mark : Set Point) (k : ℕ) :
    boundaryVisitExitMarkKernel boundary target start (k + 1) mark =
      fairSteps (boundaryHitSteps boundary target start) *
        fairSteps (positiveReturnBeforeBoundary
          (relativeBoundary boundary target)) ^ k *
        killedPositiveReturnExitMarkKernel
          (relativeBoundary boundary target) (relativeBoundary mark target) := by
  exact measure_markedBoundaryVisitAtom_succ_closed boundary target start
    (measurableSet_targetRelativeExitMarkSteps boundary mark target) k

/-- Positive-count factorization entirely in terms of the exact escape
parameter and the ordinary marked skeleton from the target. -/
theorem boundaryVisitExitMarkKernel_succ_eq_hit_mul_return_pow_mul_escape_mul_skeleton
    (boundary : Set Point) (target start : Point) (mark : Set Point)
    (htarget : target ∉ boundary) (k : ℕ) :
    boundaryVisitExitMarkKernel boundary target start (k + 1) mark =
      fairSteps (boundaryHitSteps boundary target start) *
        ENNReal.ofReal (1 - escapeBeforePositiveReturnProbability
          (relativeBoundary boundary target)) ^ k *
        ENNReal.ofReal (escapeBeforePositiveReturnProbability
          (relativeBoundary boundary target)) *
        skeletonExitMarkKernel boundary mark target := by
  have hzeroRelative : (0 : Point) ∉ relativeBoundary boundary target := by
    simpa [relativeBoundary] using htarget
  have hskeleton : skeletonExitMarkKernel
      (relativeBoundary boundary target) (relativeBoundary mark target) 0 =
      skeletonExitMarkKernel boundary mark target := by
    unfold skeletonExitMarkKernel
    change fairSteps (targetRelativeExitMarkSteps boundary mark target) = _
    rw [targetRelativeExitMarkSteps_eq_at_target]
  rw [boundaryVisitExitMarkKernel_succ,
    killedPositiveReturnExitMarkKernel_eq_escape_mul_skeleton
      (relativeBoundary boundary target) (relativeBoundary mark target)
      hzeroRelative,
    returnMass_eq_ofReal_one_sub_escape, hskeleton]
  ac_rfl

theorem boundaryVisitExitKernel_zero
    (boundary : Set Point) (target start exit : Point) :
    boundaryVisitExitKernel boundary target start 0 exit =
      killedPuncturedExitMarkKernel boundary target start {exit} :=
  boundaryVisitExitMarkKernel_zero boundary target start {exit}

theorem boundaryVisitExitKernel_succ
    (boundary : Set Point) (target start exit : Point) (k : ℕ) :
    boundaryVisitExitKernel boundary target start (k + 1) exit =
      fairSteps (boundaryHitSteps boundary target start) *
        fairSteps (positiveReturnBeforeBoundary
          (relativeBoundary boundary target)) ^ k *
        killedPositiveReturnExitMarkKernel
          (relativeBoundary boundary target) (relativeBoundary {exit} target) :=
  boundaryVisitExitMarkKernel_succ boundary target start {exit} k

/-! ## A Harnack-free algebraic wrapper -/

/-- Any pointwise local comparison with the explicit factorized kernel
immediately yields the marked-kernel lower bound required by stopped-data
disintegration.  Analytic Harnack estimates are intentionally kept outside
this module. -/
theorem markedKernel_lower_of_factorized_lower
    (boundary : Set Point) (target start : Point) (mark : Set Point) (k : ℕ)
    (loss reference skeleton : ℝ≥0∞)
    (hlocal : loss * reference * skeleton ≤
      fairSteps (boundaryHitSteps boundary target start) *
        fairSteps (positiveReturnBeforeBoundary
          (relativeBoundary boundary target)) ^ k *
        killedPositiveReturnExitMarkKernel
          (relativeBoundary boundary target) (relativeBoundary mark target)) :
    loss * reference * skeleton ≤
      boundaryVisitExitMarkKernel boundary target start (k + 1) mark := by
  rw [boundaryVisitExitMarkKernel_succ]
  exact hlocal

/-- Concrete all-count wrapper for the marked stopped-data API.  The two
premises are precisely the zero-visit killed-kernel comparison and the
positive factorized comparison; all probabilistic identities have already
been discharged above. -/
theorem markedKernelLower_of_zero_and_positive_factor_bounds
    (m : ℕ) (boundary : Set Point) (target : Point)
    (eta q p : ℝ) (htarget : target ∉ boundary)
    (hzero : ∀ start exit,
      ENNReal.ofReal (1 - eta) *
          ENNReal.ofReal (AppendixLocalTime.visitMass q p 0) *
          skeletonExitKernel boundary start exit ≤
        killedPuncturedExitMarkKernel boundary target start {exit})
    (hpositive : ∀ start exit k,
      ENNReal.ofReal (1 - eta) *
          ENNReal.ofReal (AppendixLocalTime.visitMass q p (k + 1)) *
          skeletonExitKernel boundary start exit ≤
        fairSteps (boundaryHitSteps boundary target start) *
          fairSteps (positiveReturnBeforeBoundary
            (relativeBoundary boundary target)) ^ k *
          killedPositiveReturnExitMarkKernel
            (relativeBoundary boundary target) (relativeBoundary {exit} target)) :
    MarkedTerminalDisintegration.MarkedKernelLower
      (fun _ : Fin m ↦ ENNReal.ofReal (1 - eta))
      (fun _ k ↦ ENNReal.ofReal (AppendixLocalTime.visitMass q p k))
      (fun _ start exit ↦ skeletonExitKernel boundary start exit)
      (fun _ start k exit ↦
        boundaryVisitExitKernel boundary target start k exit) := by
  intro _j start k exit
  cases k with
  | zero =>
      change ENNReal.ofReal (1 - eta) *
          ENNReal.ofReal (AppendixLocalTime.visitMass q p 0) *
          skeletonExitKernel boundary start exit ≤
        boundaryVisitExitKernel boundary target start 0 exit
      rw [boundaryVisitExitKernel_zero]
      exact hzero start exit
  | succ k =>
      change ENNReal.ofReal (1 - eta) *
          ENNReal.ofReal (AppendixLocalTime.visitMass q p (k + 1)) *
          skeletonExitKernel boundary start exit ≤
        boundaryVisitExitKernel boundary target start (k + 1) exit
      rw [boundaryVisitExitKernel_succ]
      exact hpositive start exit k

/-! ## Transparent canonical aliases and the literal-disc exit-mass bridge -/

/-- Canonical unmarked terminal skeleton kernel. -/
def terminalSkeletonKernel
    (boundary : Set Point) (start exit : Point) : ℝ≥0∞ :=
  fairSteps (boundaryExitEndpointSteps boundary start exit)

/-- Canonical terminal kernel jointly retaining visit count and exit point. -/
def terminalMarkedKernel
    (boundary : Set Point) (target start : Point) (k : ℕ) (exit : Point) :
    ℝ≥0∞ :=
  fairSteps (boundaryVisitExitAtom boundary target start k exit)

theorem terminalSkeletonKernel_eq_skeletonExitKernel
    (boundary : Set Point) (start exit : Point) :
    terminalSkeletonKernel boundary start exit =
      skeletonExitKernel boundary start exit := by
  rw [terminalSkeletonKernel, skeletonExitKernel_eq_canonical]

theorem terminalMarkedKernel_eq_boundaryVisitExitKernel
    (boundary : Set Point) (target start exit : Point)
    (htarget : target ∉ boundary) (k : ℕ) :
    terminalMarkedKernel boundary target start k exit =
      boundaryVisitExitKernel boundary target start k exit := by
  rw [terminalMarkedKernel,
    boundaryVisitExitKernel_eq_canonical boundary target start exit htarget k]

private lemma absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
    (D : Finset Point) (start : Point) (omega : StepPath) :
    ∀ n, (∀ k < n, absorbedPosition D start omega k ∈ D) →
      absorbedPosition D start omega n =
        PlanarPotential.trajectoryFrom start omega n := by
  intro n hstay
  induction n with
  | zero => simp [PlanarPotential.trajectoryFrom]
  | succ n ih =>
      rw [absorbedPosition_succ,
        absorbedStep_of_mem D (hstay n (Nat.lt_succ_self n)),
        ih (fun k hk ↦ hstay k (hk.trans (Nat.lt_succ_self n))),
        PlanarPotential.trajectoryFrom_succ]
      rfl

private lemma absorbedPosition_eq_trajectoryFrom_of_trajectory_stays
    (D : Finset Point) (start : Point) (omega : StepPath) :
    ∀ n, (∀ k < n, PlanarPotential.trajectoryFrom start omega k ∈ D) →
      absorbedPosition D start omega n =
        PlanarPotential.trajectoryFrom start omega n := by
  intro n hstay
  induction n with
  | zero => simp [PlanarPotential.trajectoryFrom]
  | succ n ih =>
      rw [absorbedPosition_succ,
        ih (fun k hk ↦ hstay k (hk.trans (Nat.lt_succ_self n))),
        absorbedStep_of_mem D (hstay n (Nat.lt_succ_self n)),
        PlanarPotential.trajectoryFrom_succ]
      rfl

private lemma trajectoryFrom_mem_boundaryInterior_before_firstBoundary
    (R : ℕ) {start : Point} (hstart : start ∈ boundaryInterior R)
    {omega : StepPath} {N : ℕ}
    (hfirst : AbsoluteBoundaryFirstAt
      (ThickPoint.discBoundary 0 (R : ℝ)) start omega N) :
    ∀ k < N, PlanarPotential.trajectoryFrom start omega k ∈ boundaryInterior R := by
  intro k hk
  induction k with
  | zero => simpa only [PlanarPotential.trajectoryFrom_zero] using hstart
  | succ k ih =>
      have hkN : k < N := (Nat.lt_succ_self k).trans hk
      have hprev := ih hkN
      have hcases := neighbor_mem_boundaryInterior_or_discBoundary
        hprev (omega k)
      have hstep : PlanarPotential.trajectoryFrom start omega (k + 1) =
          neighbor (PlanarPotential.trajectoryFrom start omega k) (omega k) := by
        rw [PlanarPotential.trajectoryFrom_succ]
        rfl
      rw [hstep]
      exact hcases.resolve_right (by
        rw [← hstep]
        exact hfirst.2 (k + 1) hk)

theorem boundaryExitEndpointSteps_discBoundary_eq_absorbedExit
    (R : ℕ) {start exit : Point}
    (hstart : start ∈ boundaryInterior R)
    (hexit : exit ∈ ThickPoint.discBoundary 0 (R : ℝ)) :
    boundaryExitEndpointSteps
        (ThickPoint.discBoundary 0 (R : ℝ)) start exit =
      ⋃ n : ℕ, absorbedExitAt (boundaryInterior R) {exit} n start := by
  let D := boundaryInterior R
  ext omega
  simp only [boundaryExitEndpointSteps, mem_iUnion, mem_setOf_eq,
    absorbedExitAt]
  constructor
  · rintro ⟨N, hfirst, hendpoint⟩
    have hstay : ∀ k < N,
        PlanarPotential.trajectoryFrom start omega k ∈ D :=
      trajectoryFrom_mem_boundaryInterior_before_firstBoundary R hstart hfirst
    have heq := absorbedPosition_eq_trajectoryFrom_of_trajectory_stays
      D start omega N hstay
    refine ⟨N, ?_⟩
    rw [heq, hendpoint]
    simp
  · rintro ⟨n, hn⟩
    have hnEndpoint : absorbedPosition D start omega n = exit := by
      simpa only [Finset.mem_singleton] using hn
    have hexitNotD : exit ∉ D := by
      exact fun hmem ↦ (mem_boundaryInterior.mp hmem).2 hexit
    let P : ℕ → Prop := fun q ↦ absorbedPosition D start omega q ∉ D
    have hP : ∃ q, P q := ⟨n, by simpa [P, hnEndpoint] using hexitNotD⟩
    let q := Nat.find hP
    have hqNot : absorbedPosition D start omega q ∉ D := Nat.find_spec hP
    have hqle : q ≤ n := Nat.find_min' hP (by simpa [P, hnEndpoint] using hexitNotD)
    have hbefore : ∀ k < q, absorbedPosition D start omega k ∈ D := by
      intro k hk
      by_contra hkNot
      exact (Nat.find_min hP hk) hkNot
    have hqne : q ≠ 0 := by
      intro hq0
      apply hqNot
      rw [hq0]
      simpa [D] using hstart
    obtain ⟨r, hqr⟩ := Nat.exists_eq_succ_of_ne_zero hqne
    rw [hqr] at hqNot hqle hbefore
    have hqNot' : absorbedPosition D start omega (r + 1) ∉ D := by
      simpa [Nat.succ_eq_add_one] using hqNot
    have hqle' : r + 1 ≤ n := by
      simpa [Nat.succ_eq_add_one] using hqle
    have hbefore' : ∀ k < r + 1, absorbedPosition D start omega k ∈ D := by
      intro k hk
      exact hbefore k (by simpa [Nat.succ_eq_add_one] using hk)
    have hrMem : absorbedPosition D start omega r ∈ D :=
      hbefore' r (Nat.lt_succ_self r)
    have houter : absorbedPosition D start omega (r + 1) ∈ outerBoundary D :=
      absorbedPosition_exit_mem_outerBoundary D start omega hrMem hqNot'
    have hboundary : absorbedPosition D start omega (r + 1) ∈
        ThickPoint.discBoundary 0 (R : ℝ) :=
      outerBoundary_boundaryInterior_subset_discBoundary R houter
    have hstable := absorbedPosition_stable_after_exit D start omega hqNot'
      (n - (r + 1))
    rw [Nat.add_sub_of_le hqle'] at hstable
    have hqEndpoint : absorbedPosition D start omega (r + 1) = exit :=
      hstable.symm.trans hnEndpoint
    have hqTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
      D start omega (r + 1) hbefore'
    refine ⟨r + 1, ⟨?_, ?_⟩, ?_⟩
    · rw [← hqTrajectory]
      exact hboundary
    · intro k hk
      have hkD := hbefore' k hk
      have hkTrajectory := absorbedPosition_eq_trajectoryFrom_of_absorbed_stays
        D start omega k (fun j hj ↦ hbefore' j (hj.trans hk))
      rw [← hkTrajectory]
      exact (mem_boundaryInterior.mp hkD).2
    · rw [← hqTrajectory]
      exact hqEndpoint

/-- For the literal disc boundary, the canonical terminal skeleton kernel
is exactly the standard finite-domain exit mass. -/
theorem terminalSkeletonKernel_discBoundary_eq_exitMass
    (R : ℕ) {start exit : Point}
    (hstart : start ∈ boundaryInterior R)
    (hexit : exit ∈ ThickPoint.discBoundary 0 (R : ℝ)) :
    terminalSkeletonKernel
        (ThickPoint.discBoundary 0 (R : ℝ)) start exit =
      exitMass (boundaryInterior R) {exit} start := by
  rw [terminalSkeletonKernel,
    boundaryExitEndpointSteps_discBoundary_eq_absorbedExit R hstart hexit]
  apply fairSteps_iUnion_absorbedExitAt_eq_exitMass
  rw [Finset.disjoint_left]
  intro z hzD hzExit
  have hzEq : z = exit := by simpa using hzExit
  subst z
  exact (mem_boundaryInterior.mp hzD).2 hexit

theorem skeletonExitKernel_discBoundary_eq_exitMass
    (R : ℕ) {start exit : Point}
    (hstart : start ∈ boundaryInterior R)
    (hexit : exit ∈ ThickPoint.discBoundary 0 (R : ℝ)) :
    skeletonExitKernel
        (ThickPoint.discBoundary 0 (R : ℝ)) start exit =
      exitMass (boundaryInterior R) {exit} start := by
  rw [← terminalSkeletonKernel_eq_skeletonExitKernel]
  exact terminalSkeletonKernel_discBoundary_eq_exitMass R hstart hexit

end

end Erdos1165.MarkedBoundaryVisitKernel

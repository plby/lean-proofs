/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AnnularProfileLevelSkeleton
import ErdosProblems.Erdos1165.TerminalBoundaryScan
import ErdosProblems.Erdos1165.TerminalSpliceProfileGeometry

/-!
# Scan identities for nested annular offspring counts

The two-state boundary scan makes additivity of offspring counts over the
chronological parent gaps explicit.  This file records the two algebraic
facts needed by that argument: a complete first-hit schedule ends in the
canonical `seeking inner` state, and changing the accumulated counter merely
translates the final counter.
-/

namespace Erdos1165.AnnularOffspringScan

noncomputable section

open Set ThickPoint TerminalClockSplice TerminalBoundaryScan
open PlanarPotential TerminalExcursionPathwise TerminalSequentialVisitLaw
open TerminalSpliceProfileGeometry AnnularProfileClocks
open AnnularProfileGapAtoms AnnularProfileLevelSkeleton

/-- Translate only the completed-excursion counter of a scan state. -/
def addCompleted (c : ℕ) (state : BoundaryScanState) : BoundaryScanState :=
  ⟨state.seekingOuter, c + state.completed⟩

@[simp] theorem addCompleted_zero (state : BoundaryScanState) :
    addCompleted 0 state = state := by
  cases state
  simp [addCompleted]

theorem visit_addCompleted
    (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (c : ℕ) (state : BoundaryScanState) (x : Point) :
    visit outer inner (addCompleted c state) x =
      addCompleted c (visit outer inner state x) := by
  cases state with
  | mk seeking completed =>
      cases seeking <;> simp only [visit, addCompleted] <;>
        split_ifs <;> simp [Nat.add_assoc]

/-- A finite scan is equivariant under translation of its accumulated
counter. -/
theorem scanSegment_addCompleted
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length c : ℕ) (state : BoundaryScanState) :
    scanSegment s outer inner start length (addCompleted c state) =
      addCompleted c (scanSegment s outer inner start length state) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [scanSegment_succ, scanSegment_succ, ih, visit_addCompleted]

/-- A complete first-hit excursion schedule ends after its final outer
return, seeking the next inner boundary, with exactly `count` completions. -/
theorem scanThrough_eq_false_count_of_schedule
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {horizon count : ℕ} (hdisjoint : Disjoint outer inner)
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    scanThrough s outer inner horizon = ⟨false, count⟩ := by
  have houter := scan_to_outerTime hdisjoint schedule count le_rfl
  have houterLe : schedule.outerTime count ≤ horizon := by
    by_cases hzero : count = 0
    · simpa [hzero] using schedule.firstOuterZero.2.1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      exact (schedule.firstOuterSucc j (by omega)).2.1
  have htail :
      scanSegment s outer inner (schedule.outerTime count + 1)
          (horizon - schedule.outerTime count) ⟨false, count⟩ =
        ⟨false, count⟩ := by
    apply scanSegment_seekingInner_of_avoids
    intro q hq
    apply schedule.noFinalInner (schedule.outerTime count + 1 + q)
    · omega
    · omega
  rw [scanThrough, show horizon + 1 =
      (schedule.outerTime count + 1) +
        (horizon - schedule.outerTime count) by omega,
    scanSegment_add, houter]
  simp only [Nat.zero_add]
  exact htail

/-! ## Actual adjacent HLOZ scales -/

/-- Successive regular HLOZ radii are separated by at least one lattice
step. -/
lemma scaleRadius_succ_add_one_le
    {n k : ℕ} (hn : 1 ≤ n) (hk : k + 1 ≤ n) :
    scaleRadius n (k + 1) + 1 ≤ scaleRadius n k := by
  rw [scaleRadius_of_le hk, scaleRadius_of_le (by omega : k ≤ n)]
  rw [regularRadius_succ]
  have hr : 2 ≤ regularRadius n k := by
    unfold regularRadius
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 9 :=
      one_le_pow₀ (by exact_mod_cast hn)
    have hkreal : (k : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hk
    have hdiff : (1 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
      linarith
    have hexp : Real.exp 1 ≤ Real.exp ((n : ℝ) - (k : ℝ)) :=
      Real.exp_le_exp.mpr hdiff
    have he : 2 ≤ Real.exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    nlinarith [mul_le_mul hexp hpow (by positivity) (by positivity)]
  have he : 2 ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hhalf : regularRadius n k / Real.exp 1 ≤ regularRadius n k / 2 := by
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) he
  nlinarith

/-- A point on a sufficiently separated larger inner boundary lies outside
the smaller disc. -/
lemma not_mem_smaller_disc_of_mem_larger_boundary
    {center z : Point} {r R : ℝ}
    (hsep : r + 1 ≤ R) (hz : z ∈ discBoundary center R) :
    z ∉ disc center r := by
  intro hzsmall
  obtain ⟨_hzR, w, hwout, hzw⟩ := hz
  have hwle : latticeDistance center w ≤ latticeDistance center z + 1 :=
    latticeDistance_le_add_one_of_adjacent hzw
  have hzle : latticeDistance center z ≤ r := hzsmall
  exact hwout (by
    change latticeDistance center w ≤ R
    exact hwle.trans (by linarith))

lemma adjacent_profileInnerBoundaries_disjoint
    {n k : ℕ} (hn : 1 ≤ n) (hk : k + 1 ≤ n) (x : Point) :
    Disjoint (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) := by
  rw [Set.disjoint_left]
  intro z hzMiddle hzInner
  exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hzInner.1
    (scaleRadius_succ_add_one_le hn hk)) hzMiddle

/-- The walk followed by one fresh erased gap, expressed in its own local
clock. -/
def profileGapWalk
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : WalkPath :=
  fun q ↦ trajectoryFrom (profileGapStartPoint omega n horizon x k j)
    (profileGapFreshPath omega n horizon x k j) q

/-- The local first-hit start clock, with its decidability choice hidden
behind a canonical noncomputable definition. -/
noncomputable def profileGapChildStart
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k parent child : ℕ) : ℕ := by
  classical
  exact excursionStart (profileGapWalk omega n horizon x k parent)
    (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
    (profileGapLength omega n horizon x k parent) child

/-- The corresponding local first-hit completion clock. -/
noncomputable def profileGapChildFinish
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k parent child : ℕ) : ℕ := by
  classical
  exact excursionFinish (profileGapWalk omega n horizon x k parent)
    (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
    (profileGapLength omega n horizon x k parent) child

/-- The complete two-state scan of a local actual gap. -/
noncomputable def profileGapScan
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k parent : ℕ) : BoundaryScanState := by
  classical
  exact scanThrough (profileGapWalk omega n horizon x k parent)
    (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
    (profileGapLength omega n horizon x k parent)

lemma profileGapWalk_end_eq
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ} :
    profileGapWalk omega n horizon x k j
        (profileGapLength omega n horizon x k j) =
      profileGapExitPoint omega n horizon x k j := by
  let a := profileInnerHitTime (trajectory omega) n horizon x k j
  let b := profileGapExitTime (trajectory omega) n horizon x k j
  have hab : a ≤ b := profileInnerHitTime_le_profileGapExitTime
    (trajectory omega) n horizon x k j
  unfold profileGapWalk profileGapStartPoint profileGapFreshPath
    profileGapLength profileGapExitPoint
  rw [trajectoryFrom_shiftSteps_eq, Nat.add_sub_of_le hab]

lemma adjacent_profileGapWalk
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j q : ℕ) :
    Adjacent (profileGapWalk omega n horizon x k j q)
      (profileGapWalk omega n horizon x k j (q + 1)) := by
  exact TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ _ _ _

/-- If a nearest-neighbor path is inside a set at the completion of an
inner visit and outside it at the horizon, its next search for the inner
vertex boundary completes by the horizon. -/
lemma excursionStart_succ_le_of_crosses_innerBoundary
    {s : WalkPath} {A inner : Set Point}
    [DecidablePred (· ∈ innerBoundary A)] [DecidablePred (· ∈ inner)]
    {horizon child : ℕ}
    (hstep : ∀ q, Adjacent (s q) (s (q + 1)))
    (hfinish : excursionFinish s (innerBoundary A) inner horizon child ≤ horizon)
    (hin : s (excursionFinish s (innerBoundary A) inner horizon child) ∈ A)
    (hout : s horizon ∉ A) :
    excursionStart s (innerBoundary A) inner horizon (child + 1) ≤ horizon := by
  rw [TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global]
  exact firstHitThrough_innerBoundary_le_of_exit s A hstep hfinish hin hout

/-- Every child excursion completed inside one actual parent gap returns to
the child outer boundary before that parent gap exits. -/
lemma child_nextOuter_le_profileGapLength
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent child : ℕ}
    [outerDec : DecidablePred (· ∈ profileInnerBoundary n k x)]
    [innerDec : DecidablePred (· ∈ profileInnerBoundary n (k + 1) x)]
    (hn : 1 ≤ n) (hkpos : 1 ≤ k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (hchild : excursionFinish
      (profileGapWalk omega n horizon x k parent)
      (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k parent) child ≤
        profileGapLength omega n horizon x k parent) :
    excursionStart
      (profileGapWalk omega n horizon x k parent)
      (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k parent) (child + 1) ≤
        profileGapLength omega n horizon x k parent := by
  let s := profileGapWalk omega n horizon x k parent
  let L := profileGapLength omega n horizon x k parent
  have hfinishMem : s (excursionFinish s
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      L child) ∈ profileInnerBoundary n (k + 1) x :=
    excursionFinish_mem_inner_of_le s _ _ L child hchild
  have hinnerDisc : s (excursionFinish s
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      L child) ∈ disc x (scaleRadius n k) :=
    hfinishMem.1.trans (by
      exact (scaleRadius_antitone_of_le (by omega : k ≤ k + 1) hk))
  have hendBoundary : s L ∈ profileOuterBoundary n k x := by
    change profileGapWalk omega n horizon x k parent
      (profileGapLength omega n horizon x k parent) ∈ _
    rw [profileGapWalk_end_eq]
    exact profileGapExitPoint_mem_outerBoundary hcomplete
  have hsep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1) := by
    have hkpred : k - 1 + 1 = k := by omega
    simpa only [hkpred] using scaleRadius_succ_add_one_le hn
      (k := k - 1) (by omega : (k - 1) + 1 ≤ n)
  have hendOutside : s L ∉ disc x (scaleRadius n k) := by
    exact not_mem_smaller_disc_of_mem_larger_boundary hsep hendBoundary
  exact @excursionStart_succ_le_of_crosses_innerBoundary s
    (disc x (scaleRadius n k)) (profileInnerBoundary n (k + 1) x)
    outerDec innerDec L child
    (fun q ↦ adjacent_profileGapWalk omega n horizon x k parent q)
    hchild hinnerDisc hendOutside

/-- The local boundary automaton of an actual completed parent gap ends in
the canonical seeking-inner state and its counter is the literal offspring
count. -/
theorem scanThrough_profileGap_eq_offspringCount
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent : ℕ}
    (hn : 1 ≤ n) (hkpos : 1 ≤ k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) :
    profileGapScan omega n horizon x k parent =
      ⟨false, profileGapOffspringCount omega n horizon x k parent⟩ := by
  classical
  unfold profileGapScan
  let s := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let L := profileGapLength omega n horizon x k parent
  let count := completedExcursionCount s outer inner L
  have hdisjoint : Disjoint outer inner :=
    adjacent_profileInnerBoundaries_disjoint hn hk x
  have hcountLe : count ≤ L + 1 := completedExcursionCount_le s outer inner L
  have hstartMem : s 0 ∈ outer := by
    rw [show s 0 = profileGapStartPoint omega n horizon x k parent by
      simp [s, profileGapWalk]]
    exact profileGapStartPoint_mem_innerBoundary hcomplete
  have houterZero : excursionStart s outer inner L 0 ≤ L := by
    unfold excursionStart
    apply (firstHitThrough_le_horizon_iff s outer 0 L).2
    exact ⟨0, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le L⟩, hstartMem⟩⟩
  have hinner : ∀ child, child < count →
      excursionFinish s outer inner L child ≤ L := by
    intro child hchild
    exact finish_le_horizon_of_lt_completedExcursionCount s outer inner L hchild
  have houterSucc : ∀ child, child < count →
      excursionStart s outer inner L (child + 1) ≤ L := by
    intro child hchild
    exact child_nextOuter_le_profileGapLength hn hkpos hk hcomplete
      (hinner child hchild)
  have hnext : excursionFinish s outer inner L count = L + 1 :=
    excursionFinish_completedExcursionCount_eq_sentinel
      s outer inner hdisjoint L
  let schedule := FirstHitExcursionSchedule.ofExactClocks
    s outer inner L count hcountLe houterZero hinner houterSucc hnext
  have hscan := scanThrough_eq_false_count_of_schedule hdisjoint schedule
  have hcountEq : count =
      profileGapOffspringCount omega n horizon x k parent := by
    rfl
  simpa only [s, outer, inner, L, hcountEq] using hscan

end

end Erdos1165.AnnularOffspringScan

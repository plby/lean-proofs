/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularProfileOffspringPartition

/-!
# Identifying parent-local and global profile-child clocks

The offspring partition records only the cardinality of the children in
each parent gap.  Recursive source parsing also needs its chronological
content: local child `j` in parent gap `i` is global child
`sum_{h<i} offspring(h) + j`.  This file begins with the exact finite
index formula and records horizon-stability for every completed first hit.
-/

namespace Erdos1165.AnnularProfileChildClockIdentification

open ThickPoint TerminalClockSplice TerminalExcursionPathwise
open TerminalBoundaryScan
open AnnularProfileClocks AnnularProfileGapAtoms AnnularProfileNestedEdge
open AnnularProfileLevelSkeleton
open AnnularOffspringScan
open TerminalGlobalExitSplice
open TerminalSequentialVisitLaw
open AnnularProfileOffspringPartition PathInsertion

noncomputable section

/-- `gapChildIndexEquiv` is the literal parent-major prefix-sum index. -/
theorem gapChildIndexEquiv_val
    {a b : ℕ} (g : GapPattern a b)
    (i : Fin a) (j : Fin (gapMultiplicity g i)) :
    ((gapChildIndexEquiv g ⟨i, j⟩ : Fin b) : ℕ) =
      ∑ h : Fin i, gapMultiplicity g (Fin.castLE i.isLt.le h) + j := by
  simp only [gapChildIndexEquiv, Equiv.trans_apply, finCongr_apply,
    Fin.val_cast, finSigmaFinEquiv_apply]

/-- The canonical actual offspring pattern numbers a local child by the
sum of all earlier actual offspring multiplicities. -/
theorem gapChildIndexEquiv_actualProfileOffspringGapPattern_val
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    let g := actualProfileOffspringGapPattern hn hk0 hk hx hparents
      hparentCount hchildCount hcomplete
    ((gapChildIndexEquiv g
        ⟨i, Fin.cast (gapMultiplicity_actualProfileOffspringGapPattern
          hn hk0 hk hx hparents hparentCount hchildCount hcomplete i).symm j⟩ :
        Fin children) : ℕ) =
      ∑ h : Fin i,
          profileGapOffspringCount omega n horizon x k
            (Fin.castLE i.isLt.le h) + j := by
  dsimp only
  rw [gapChildIndexEquiv_val]
  simp only [gapMultiplicity_actualProfileOffspringGapPattern,
    Fin.val_cast]

/-- Range-sum form of the actual parent-major child index. -/
theorem gapChildIndexEquiv_actualProfileOffspringGapPattern_val_range
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    let g := actualProfileOffspringGapPattern hn hk0 hk hx hparents
      hparentCount hchildCount hcomplete
    ((gapChildIndexEquiv g
        ⟨i, Fin.cast (gapMultiplicity_actualProfileOffspringGapPattern
          hn hk0 hk hx hparents hparentCount hchildCount hcomplete i).symm j⟩ :
        Fin children) : ℕ) =
      (∑ h ∈ Finset.range i,
          profileGapOffspringCount omega n horizon x k h) + j := by
  dsimp only
  rw [gapChildIndexEquiv_actualProfileOffspringGapPattern_val]
  simp only [Fin.sum_univ_eq_sum_range, Fin.val_castLE]

/-- The canonical global child index carried by one actual parent-local
offspring slot. -/
noncomputable def actualProfileChildIndex
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) : Fin children :=
  let g := actualProfileOffspringGapPattern hn hk0 hk hx hparents
    hparentCount hchildCount hcomplete
  gapChildIndexEquiv g
    ⟨i, Fin.cast (gapMultiplicity_actualProfileOffspringGapPattern
      hn hk0 hk hx hparents hparentCount hchildCount hcomplete i).symm j⟩

@[simp] theorem actualProfileChildIndex_val
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    (actualProfileChildIndex hn hk0 hk hx hparents hparentCount hchildCount
      hcomplete i j : ℕ) =
      (∑ h ∈ Finset.range i,
        profileGapOffspringCount omega n horizon x k h) + j := by
  exact gapChildIndexEquiv_actualProfileOffspringGapPattern_val_range
    hn hk0 hk hx hparents hparentCount hchildCount hcomplete i j

/-- Once a first hit has occurred by a smaller horizon, extending the
horizon does not change its time. -/
theorem firstHitThrough_eq_of_horizon_le
    {s : WalkPath} {A : Set Point} [DecidablePred (· ∈ A)]
    {start small big : ℕ} (hsmallBig : small ≤ big)
    (hcomplete : firstHitThrough s A start small ≤ small) :
    firstHitThrough s A start big = firstHitThrough s A start small := by
  let stop := firstHitThrough s A start small
  have hfirstSmall : IsFirstHitSegment s A start stop small :=
    isFirstHitSegment_firstHitThrough_of_le s A start small hcomplete
  have hfirstBig : IsFirstHitSegment s A start stop big :=
    ⟨hfirstSmall.1, hfirstSmall.2.1.trans hsmallBig,
      hfirstSmall.2.2.1, hfirstSmall.2.2.2⟩
  exact firstHitThrough_eq_of_isFirstHitSegment s A hfirstBig

/-- Every completed alternating excursion clock is stable when the finite
horizon is extended.  Both its outer entrance and inner completion are
identified simultaneously, so no equality of the two truncated profiles is
required. -/
theorem excursionStart_eq_and_excursionFinish_eq_of_horizon_le
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {small big : ℕ} (hsmallBig : small ≤ big) :
    ∀ j, excursionFinish s outer inner small j ≤ small →
      excursionStart s outer inner big j =
          excursionStart s outer inner small j ∧
        excursionFinish s outer inner big j =
          excursionFinish s outer inner small j := by
  intro j
  induction j with
  | zero =>
      intro hfinish
      have hstart : excursionStart s outer inner small 0 ≤ small :=
        (excursionStart_le_finish s outer inner small 0).trans hfinish
      have hstartEq : excursionStart s outer inner big 0 =
          excursionStart s outer inner small 0 := by
        unfold excursionStart
        simp only [Function.iterate_zero_apply]
        exact firstHitThrough_eq_of_horizon_le (s := s) (A := outer)
          hsmallBig hstart
      refine ⟨hstartEq, ?_⟩
      unfold excursionFinish
      rw [hstartEq]
      exact firstHitThrough_eq_of_horizon_le (s := s) (A := inner)
        hsmallBig hfinish
  | succ j ih =>
      intro hfinish
      have hprevFinish : excursionFinish s outer inner small j ≤ small :=
        (excursionFinish_mono s outer inner small (Nat.le_succ j)).trans
          hfinish
      have hprev := ih hprevFinish
      have hstart : excursionStart s outer inner small (j + 1) ≤ small :=
        (excursionStart_le_finish s outer inner small (j + 1)).trans hfinish
      have hstartFirst : firstHitThrough s outer
          (excursionFinish s outer inner small j) small ≤ small := by
        rw [← TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global]
        exact hstart
      have hstartStable : firstHitThrough s outer
          (excursionFinish s outer inner small j) big =
          firstHitThrough s outer
            (excursionFinish s outer inner small j) small :=
        firstHitThrough_eq_of_horizon_le (s := s) (A := outer)
          hsmallBig hstartFirst
      have hstartEq : excursionStart s outer inner big (j + 1) =
          excursionStart s outer inner small (j + 1) := by
        rw [TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global,
          TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global,
          hprev.2]
        exact hstartStable
      refine ⟨hstartEq, ?_⟩
      change firstHitThrough s inner
          (excursionStart s outer inner big (j + 1)) big =
        firstHitThrough s inner
          (excursionStart s outer inner small (j + 1)) small
      rw [hstartEq]
      exact firstHitThrough_eq_of_horizon_le (s := s) (A := inner)
        hsmallBig hfinish

theorem excursionStart_eq_of_horizon_le
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {small big j : ℕ} (hsmallBig : small ≤ big)
    (hfinish : excursionFinish s outer inner small j ≤ small) :
    excursionStart s outer inner big j =
      excursionStart s outer inner small j :=
  (excursionStart_eq_and_excursionFinish_eq_of_horizon_le hsmallBig j
    hfinish).1

theorem excursionFinish_eq_of_horizon_le
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {small big j : ℕ} (hsmallBig : small ≤ big)
    (hfinish : excursionFinish s outer inner small j ≤ small) :
    excursionFinish s outer inner big j =
      excursionFinish s outer inner small j :=
  (excursionStart_eq_and_excursionFinish_eq_of_horizon_le hsmallBig j
    hfinish).2

/-- If the complete scan is seeking the inner boundary, then the outer
entrance of the first unfinished excursion has genuinely occurred. -/
theorem excursionStart_completedExcursionCount_le_of_scan_seekingInner
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (horizon : ℕ)
    (hseeking : (scanThrough s outer inner horizon).seekingOuter = false) :
    excursionStart s outer inner horizon
        (completedExcursionCount s outer inner horizon) ≤ horizon := by
  let count := completedExcursionCount s outer inner horizon
  change excursionStart s outer inner horizon count ≤ horizon
  by_contra hnot
  have hstartUpper : excursionStart s outer inner horizon count ≤ horizon + 1 := by
    unfold excursionStart
    exact firstHitThrough_le_sentinel s outer _ horizon
  have hstartSentinel : excursionStart s outer inner horizon count =
      horizon + 1 := by omega
  by_cases hcountZero : count = 0
  · have hstartZero : excursionStart s outer inner horizon 0 =
        horizon + 1 := by simpa only [hcountZero] using hstartSentinel
    have houterAvoid : AvoidsThrough s outer 0 horizon := by
      unfold excursionStart at hstartZero
      simp only [Function.iterate_zero_apply] at hstartZero
      simpa using avoidsThrough_of_firstHitThrough_eq_sentinel
        s outer hstartZero
    have hscan : scanThrough s outer inner horizon = initialState := by
      unfold scanThrough
      apply scanSegment_seekingOuter_of_avoids
      intro q hq
      simpa only [Nat.zero_add] using
        houterAvoid q (Nat.zero_le q) (by omega)
    rw [hscan] at hseeking
    exact Bool.noConfusion hseeking
  · obtain ⟨j, hcountSucc⟩ := Nat.exists_eq_succ_of_ne_zero hcountZero
    have hcountLe : j + 1 ≤ horizon + 1 := by
      have hle := completedExcursionCount_le s outer inner horizon
      change count ≤ horizon + 1 at hle
      omega
    have hjFinish : excursionFinish s outer inner horizon j ≤ horizon := by
      apply (excursionFinish_le_horizon_iff_lt_completedExcursionCount
        s outer inner horizon (by omega)).2
      change j < count
      omega
    have hprefix := scan_to_excursionFinish
      s outer inner hdisjoint horizon j hjFinish
    have heq :=
      TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global
        s outer inner horizon j
    have houterAvoid : AvoidsThrough s outer
        (excursionFinish s outer inner horizon j) horizon := by
      apply avoidsThrough_of_firstHitThrough_eq_sentinel s outer
      rw [← heq]
      simpa only [hcountSucc] using hstartSentinel
    have htail : scanSegment s outer inner
        (excursionFinish s outer inner horizon j + 1)
        (horizon - excursionFinish s outer inner horizon j)
        ⟨true, j + 1⟩ = ⟨true, j + 1⟩ := by
      apply scanSegment_seekingOuter_of_avoids
      intro q hq
      apply houterAvoid
      · omega
      · omega
    have hscan : scanThrough s outer inner horizon = ⟨true, j + 1⟩ := by
      rw [scanThrough, show horizon + 1 =
          (excursionFinish s outer inner horizon j + 1) +
            (horizon - excursionFinish s outer inner horizon j) by omega,
        scanSegment_add, hprefix]
      simp only [Nat.zero_add]
      exact htail
    rw [hscan] at hseeking
    exact Bool.noConfusion hseeking

/-- A completed outer entrance, even for the first unfinished inward
excursion, is stable under extension of the finite horizon. -/
theorem excursionStart_eq_of_horizon_le_of_start_le
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {small big : ℕ} (hsmallBig : small ≤ big) :
    ∀ j, excursionStart s outer inner small j ≤ small →
      excursionStart s outer inner big j =
        excursionStart s outer inner small j := by
  intro j
  induction j with
  | zero =>
      intro hstart
      unfold excursionStart
      simp only [Function.iterate_zero_apply]
      exact firstHitThrough_eq_of_horizon_le (s := s) (A := outer)
        hsmallBig hstart
  | succ j _ih =>
      intro hstart
      have hprevFinish : excursionFinish s outer inner small j ≤ small :=
        (excursionFinish_le_next_start s outer inner small j).trans hstart
      have hprevStable := excursionFinish_eq_of_horizon_le
        (s := s) (outer := outer) (inner := inner) hsmallBig hprevFinish
      have hstartFirst : firstHitThrough s outer
          (excursionFinish s outer inner small j) small ≤ small := by
        rw [← TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global]
        exact hstart
      rw [TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global,
        TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global,
        hprevStable]
      exact firstHitThrough_eq_of_horizon_le (s := s) (A := outer)
        hsmallBig hstartFirst

/-- A seeking-inner scanner state followed by a literal first inner hit
identifies the corresponding global excursion-finish clock. -/
theorem excursionFinish_eq_of_scanThrough_seekingInner
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner)
    {start finish horizon index : ℕ}
    (hscan : scanThrough s outer inner start = ⟨false, index⟩)
    (hstartHorizon : start ≤ horizon)
    (hfirst : IsFirstHitSegment s inner start finish horizon) :
    excursionFinish s outer inner horizon index = finish := by
  have hcompleted := scanThrough_completed_eq_completedExcursionCount
    s outer inner hdisjoint start
  rw [hscan] at hcompleted
  have hcount : completedExcursionCount s outer inner start = index :=
    hcompleted.symm
  have hseeking : (scanThrough s outer inner start).seekingOuter = false := by
    rw [hscan]
  have houterStart : excursionStart s outer inner start index ≤ start := by
    rw [← hcount]
    exact excursionStart_completedExcursionCount_le_of_scan_seekingInner
      s outer inner hdisjoint start hseeking
  have houterStartStable : excursionStart s outer inner horizon index =
      excursionStart s outer inner start index :=
    excursionStart_eq_of_horizon_le_of_start_le
      (s := s) (outer := outer) (inner := inner) hstartHorizon index houterStart
  have hsentinel : excursionFinish s outer inner start index = start + 1 := by
    rw [← hcount]
    exact excursionFinish_completedExcursionCount_eq_sentinel
      s outer inner hdisjoint start
  have havoid : AvoidsThrough s inner
      (excursionStart s outer inner start index) start := by
    unfold excursionFinish at hsentinel
    exact avoidsThrough_of_firstHitThrough_eq_sentinel s inner hsentinel
  have hcombined : IsFirstHitSegment s inner
      (excursionStart s outer inner start index) finish horizon := by
    refine ⟨houterStart.trans hfirst.1, hfirst.2.1, hfirst.2.2.1, ?_⟩
    intro q houterQ hqFinish hqInner
    by_cases hqStart : q ≤ start
    · exact havoid q houterQ hqStart hqInner
    · exact hfirst.2.2.2 q (by omega) hqFinish hqInner
  unfold excursionFinish
  rw [houterStartStable]
  exact firstHitThrough_eq_of_isFirstHitSegment s inner hcombined

/-- The following first outer hit identifies the next global entrance clock
once the preceding inner clock has been identified. -/
theorem excursionFinish_eq_and_start_succ_eq_of_scanThrough
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner)
    {start finish returnTime horizon index : ℕ}
    (hscan : scanThrough s outer inner start = ⟨false, index⟩)
    (hstartHorizon : start ≤ horizon)
    (hfirstInner : IsFirstHitSegment s inner start finish horizon)
    (hfirstOuter : IsFirstHitSegment s outer finish returnTime horizon) :
    excursionFinish s outer inner horizon index = finish ∧
      excursionStart s outer inner horizon (index + 1) = returnTime := by
  have hfinish := excursionFinish_eq_of_scanThrough_seekingInner
    hdisjoint hscan hstartHorizon hfirstInner
  refine ⟨hfinish, ?_⟩
  rw [TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global,
    hfinish]
  exact firstHitThrough_eq_of_isFirstHitSegment s outer hfirstOuter

/-- The scanner at an actual outer-entrance clock is in the canonical
seeking-inner state with the clock index as its counter. -/
theorem scan_to_excursionStart
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (hdisjoint : Disjoint outer inner) (horizon : ℕ) :
    ∀ j, excursionStart s outer inner horizon j ≤ horizon →
      scanSegment s outer inner 0
          (excursionStart s outer inner horizon j + 1) initialState =
        ⟨false, j⟩ := by
  intro j hstart
  cases j with
  | zero =>
      have hfirst : IsFirstHitSegment s outer 0
          (excursionStart s outer inner horizon 0) horizon := by
        simpa [excursionStart] using
          isFirstHitSegment_firstHitThrough_of_le s outer 0 horizon hstart
      change scanSegment s outer inner 0
          (excursionStart s outer inner horizon 0 + 1) ⟨true, 0⟩ =
        ⟨false, 0⟩
      simpa only [Nat.sub_zero] using
        (scanSegment_after_firstOuter s outer inner hfirst (completed := 0))
  | succ j =>
      have hfinish : excursionFinish s outer inner horizon j ≤ horizon :=
        (excursionFinish_le_next_start s outer inner horizon j).trans hstart
      have hprefix := scan_to_excursionFinish
        s outer inner hdisjoint horizon j hfinish
      have heq :=
        TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global
          s outer inner horizon j
      have hfirst : IsFirstHitSegment s outer
          (excursionFinish s outer inner horizon j)
          (excursionStart s outer inner horizon (j + 1)) horizon := by
        have hsegment := isFirstHitSegment_firstHitThrough_of_le s outer
          (excursionFinish s outer inner horizon j) horizon (heq ▸ hstart)
        rw [← heq] at hsegment
        exact hsegment
      have hinnerMem : s (excursionFinish s outer inner horizon j) ∈ inner :=
        excursionFinish_mem_inner_of_le s outer inner horizon j hfinish
      have hstrict := IsFirstHitSegment.lt_of_mem_disjoint
        hdisjoint.symm hinnerMem hfirst
      rw [show excursionStart s outer inner horizon (j + 1) + 1 =
          (excursionFinish s outer inner horizon j + 1) +
            (excursionStart s outer inner horizon (j + 1) -
              excursionFinish s outer inner horizon j) by omega,
        scanSegment_add, hprefix]
      simp only [Nat.zero_add]
      exact scanSegment_after_firstOuter_strict
        s outer inner hfirst hstrict

/-! ## Actual parent-prefix scanner state -/

/-- On entering parent gap `parent`, the global child scanner is seeking the
child-inner boundary and its counter is the sum of the offspring counts of
the earlier parent gaps. -/
theorem scanThrough_profileParentEntrance_eq_prefixOffspring
    {omega : StepPath} {n horizon k parents parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparent : parent < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon) :
    @scanThrough (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k parent) =
      ⟨false, ∑ i ∈ Finset.range parent,
        profileGapOffspringCount omega n horizon x k i⟩ := by
  classical
  induction parent with
  | zero =>
      simpa only [scanThrough, Finset.range_zero, Finset.sum_empty] using
        scan_prefix_to_first_parent hn hk0 hk hx
          (hcomplete 0 (by omega))
  | succ parent ih =>
      have hprevious : parent < parents := by omega
      have hnext : parent + 1 < parents := hparent
      have horderOne := profileInnerHitTime_le_profileGapExitTime
        (trajectory omega) n horizon x k parent
      have horderTwo := profileGapExitTime_le_profileInnerHitTime_of_lt
        (trajectory omega) n horizon x k (show parent < parent + 1 by omega)
      rw [scanThrough, show
          profileInnerHitTime (trajectory omega) n horizon x k (parent + 1) + 1 =
            (profileInnerHitTime (trajectory omega) n horizon x k parent + 1) +
              (profileGapExitTime (trajectory omega) n horizon x k parent -
                profileInnerHitTime (trajectory omega) n horizon x k parent) +
              (profileInnerHitTime (trajectory omega) n horizon x k (parent + 1) -
                profileGapExitTime (trajectory omega) n horizon x k parent) by
            omega,
        scanSegment_add, scanSegment_add]
      have hprefix := ih hprevious
      unfold scanThrough at hprefix
      rw [hprefix]
      simp only [Nat.zero_add]
      rw [scan_profileGap_add_offspring hn hk0 hk
        (hcomplete parent hprevious)]
      have hmiddle :
          profileInnerHitTime (trajectory omega) n horizon x k parent + 1 +
                (profileGapExitTime (trajectory omega) n horizon x k parent -
                  profileInnerHitTime (trajectory omega) n horizon x k parent) =
            profileGapExitTime (trajectory omega) n horizon x k parent + 1 := by
        omega
      rw [hmiddle, scan_between_parent_gaps hn hk0 hk hnext hcomplete]
      simp only [Finset.sum_range_succ]

/-! ## First-hit clocks within one genuine parent gap -/

/-- The first local outer entrance is the initial point of the gap and hence
occurs by its local horizon. -/
theorem profileGapChildStart_zero_le
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) :
    @excursionStart (profileGapWalk omega n horizon x k parent)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileGapLength omega n horizon x k parent) 0 ≤
      profileGapLength omega n horizon x k parent := by
  classical
  let s := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let L := profileGapLength omega n horizon x k parent
  have hstartMem : s 0 ∈ outer := by
    rw [show s 0 = profileGapStartPoint omega n horizon x k parent by
      simp [s, profileGapWalk]]
    exact profileGapStartPoint_mem_innerBoundary hcomplete
  unfold excursionStart
  simp only [Function.iterate_zero_apply]
  exact (firstHitThrough_le_of_mem (s := s) (A := outer)
    (start := 0) (horizon := L) (q := 0) le_rfl (Nat.zero_le L)
      hstartMem).trans (Nat.zero_le L)

/-- Every local entrance following an actually completed child return occurs
before the parent gap exits. -/
theorem profileGapChildStart_succ_le
    {omega : StepPath} {n horizon k parent j : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (hj : j < profileGapOffspringCount omega n horizon x k parent) :
    @excursionStart (profileGapWalk omega n horizon x k parent)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileGapLength omega n horizon x k parent) (j + 1) ≤
      profileGapLength omega n horizon x k parent := by
  classical
  let s := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let L := profileGapLength omega n horizon x k parent
  have hjCount : j < completedExcursionCount s outer inner L := by
    change j < completedExcursionCount
      (PlanarPotential.trajectoryFrom
        (profileGapStartPoint omega n horizon x k parent)
        (profileGapFreshPath omega n horizon x k parent))
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k parent) at hj
    change j < completedExcursionCount
      (fun q ↦ PlanarPotential.trajectoryFrom
        (profileGapStartPoint omega n horizon x k parent)
        (profileGapFreshPath omega n horizon x k parent) q)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k parent)
    exact hj
  have hfinish : excursionFinish s outer inner L j ≤ L :=
    finish_le_horizon_of_lt_completedExcursionCount s outer inner L hjCount
  change excursionStart s outer inner L (j + 1) ≤ L
  exact child_nextOuter_le_profileGapLength (by omega : 1 ≤ n)
    (by omega : 1 ≤ k) hk hcomplete hfinish

/-- Local gap coordinates are literal absolute coordinates in the source
trajectory. -/
theorem profileGapWalk_eq_trajectory_add
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k parent q : ℕ) :
    profileGapWalk omega n horizon x k parent q =
      trajectory omega
        (profileInnerHitTime (trajectory omega) n horizon x k parent + q) := by
  unfold profileGapWalk profileGapStartPoint profileGapFreshPath
  rw [trajectoryFrom_shiftSteps_eq]

/-- The global scanner at an absolute local-child outer entrance carries the
parent-major prefix count plus the local child index.  The local entrance
bound is kept explicit so the zero and successor cases remain small default-
heartbeat declarations. -/
theorem scanThrough_absoluteProfileGapChildStart_eq
    {omega : StepPath} {n horizon k parents parent j : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparent : parent < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (hlocalStart :
      @excursionStart (profileGapWalk omega n horizon x k parent)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileGapLength omega n horizon x k parent) j ≤
          profileGapLength omega n horizon x k parent) :
    let localStart :=
      @excursionStart (profileGapWalk omega n horizon x k parent)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileGapLength omega n horizon x k parent) j
    @scanThrough (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k parent +
          localStart) =
      ⟨false, (∑ i ∈ Finset.range parent,
        profileGapOffspringCount omega n horizon x k i) + j⟩ := by
  classical
  dsimp only
  let globalPath := trajectory omega
  let localPath := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let t := profileInnerHitTime globalPath n horizon x k parent
  let L := profileGapLength omega n horizon x k parent
  let localStart := excursionStart localPath outer inner L j
  let prefixCount := ∑ i ∈ Finset.range parent,
    profileGapOffspringCount omega n horizon x k i
  have hdisjoint : Disjoint outer inner :=
    adjacent_profileInnerBoundaries_disjoint (by omega : 1 ≤ n) hk x
  have hprefix : scanThrough globalPath outer inner t = ⟨false, prefixCount⟩ := by
    simpa only [globalPath, outer, inner, t, prefixCount] using
      scanThrough_profileParentEntrance_eq_prefixOffspring
        hn hk0 hk hx hparent hcomplete
  have hlocalScan : scanSegment localPath outer inner 0 (localStart + 1)
      initialState = ⟨false, j⟩ := by
    exact scan_to_excursionStart localPath outer inner hdisjoint L j hlocalStart
  have hzeroMem : localPath 0 ∈ outer := by
    rw [show localPath 0 = profileGapStartPoint omega n horizon x k parent by
      simp [localPath, profileGapWalk]]
    exact profileGapStartPoint_mem_innerBoundary
      (hcomplete parent hparent)
  have hlocalZero : scanSegment localPath outer inner 0 1 initialState =
      ⟨false, 0⟩ := by
    simp [scanSegment_succ, scanSegment_zero, initialState, visit, hzeroMem]
  have hlocalTail : scanSegment localPath outer inner 1 localStart ⟨false, 0⟩ =
      ⟨false, j⟩ := by
    rw [show localStart + 1 = 1 + localStart by omega,
      scanSegment_add, hlocalZero] at hlocalScan
    simpa only [Nat.zero_add] using hlocalScan
  have htranslated : scanSegment localPath outer inner 1 localStart
      ⟨false, prefixCount⟩ = ⟨false, prefixCount + j⟩ := by
    have hshift := scanSegment_addCompleted localPath outer inner 1 localStart
      prefixCount ⟨false, 0⟩
    rw [hlocalTail] at hshift
    simpa [addCompleted] using hshift
  have hcongr : scanSegment globalPath outer inner (t + 1) localStart
      ⟨false, prefixCount⟩ =
        scanSegment localPath outer inner 1 localStart ⟨false, prefixCount⟩ := by
    apply scanSegment_congr
    intro q hq
    dsimp only [globalPath, localPath, t]
    rw [profileGapWalk_eq_trajectory_add]
    congr 1
    omega
  change scanThrough globalPath outer inner (t + localStart) =
    ⟨false, prefixCount + j⟩
  rw [scanThrough, show t + localStart + 1 = (t + 1) + localStart by omega,
    scanSegment_add]
  have hprefixSegment : scanSegment globalPath outer inner 0 (t + 1)
      initialState = ⟨false, prefixCount⟩ := by
    simpa only [scanThrough] using hprefix
  simp only [Nat.zero_add]
  rw [hprefixSegment, hcongr, htranslated]

/-- Translate one local first-hit segment in a genuine parent gap to its
absolute source-path coordinates. -/
theorem IsFirstHitSegment.of_profileGapWalk
    {omega : StepPath} {n horizon k parent localStart localStop : ℕ}
    {x : Point} {A : Set Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (hstop : localStop ≤ profileGapLength omega n horizon x k parent)
    (hsegment : IsFirstHitSegment
      (profileGapWalk omega n horizon x k parent) A
      localStart localStop (profileGapLength omega n horizon x k parent)) :
    IsFirstHitSegment (trajectory omega) A
      (profileInnerHitTime (trajectory omega) n horizon x k parent + localStart)
      (profileInnerHitTime (trajectory omega) n horizon x k parent + localStop)
      horizon := by
  let t := profileInnerHitTime (trajectory omega) n horizon x k parent
  let u := profileGapExitTime (trajectory omega) n horizon x k parent
  let L := profileGapLength omega n horizon x k parent
  have htu := profileInnerHitTime_le_profileGapExitTime
    (trajectory omega) n horizon x k parent
  have htL : t + L = u := by
    dsimp only [t, L, profileGapLength, u]
    omega
  have huH : u ≤ horizon := by simpa only [u] using hcomplete
  have habsoluteStop : t + localStop ≤ horizon := by omega
  have hstartStop := hsegment.1
  apply hsegment.transport_equalBlock
    (duration := localStop - localStart)
  · omega
  · omega
  · exact habsoluteStop
  · intro q hq
    rw [profileGapWalk_eq_trajectory_add]
    congr 1
    omega

/-- The local child inward segment and its deleted return are literal global
first-hit segments at the translated absolute clocks. -/
theorem absoluteProfileGapChild_firstHitSegments
    {omega : StepPath} {n horizon k parent j : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (hj : j < profileGapOffspringCount omega n horizon x k parent) :
    let localPath := profileGapWalk omega n horizon x k parent
    let outer := profileInnerBoundary n k x
    let inner := profileInnerBoundary n (k + 1) x
    let L := profileGapLength omega n horizon x k parent
    let localStart :=
      @excursionStart localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L j
    let localFinish :=
      @excursionFinish localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L j
    let localReturn :=
      @excursionStart localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L (j + 1)
    let t := profileInnerHitTime (trajectory omega) n horizon x k parent
    IsFirstHitSegment (trajectory omega) inner
        (t + localStart) (t + localFinish) horizon ∧
      IsFirstHitSegment (trajectory omega) outer
        (t + localFinish) (t + localReturn) horizon := by
  classical
  dsimp only
  let localPath := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let L := profileGapLength omega n horizon x k parent
  let localStart := excursionStart localPath outer inner L j
  let localFinish := excursionFinish localPath outer inner L j
  let localReturn := excursionStart localPath outer inner L (j + 1)
  let t := profileInnerHitTime (trajectory omega) n horizon x k parent
  let u := profileGapExitTime (trajectory omega) n horizon x k parent
  have hreturn : localReturn ≤ L := by
    simpa only [localReturn, localPath, outer, inner, L] using
      profileGapChildStart_succ_le hn hk0 hk hcomplete hj
  have hfinish : localFinish ≤ L :=
    (excursionFinish_le_next_start localPath outer inner L j).trans hreturn
  have hstartFinish : localStart ≤ localFinish :=
    excursionStart_le_finish localPath outer inner L j
  have hfinishReturn : localFinish ≤ localReturn :=
    excursionFinish_le_next_start localPath outer inner L j
  have hlocalInner : IsFirstHitSegment localPath inner
      localStart localFinish L := by
    exact isFirstHitSegment_firstHitThrough_of_le
      localPath inner localStart L hfinish
  have heq :=
    TerminalClockSplice.excursionStart_succ_eq_firstHitThrough_finish_global
      localPath outer inner L j
  have hlocalOuter : IsFirstHitSegment localPath outer
      localFinish localReturn L := by
    have hfirst := isFirstHitSegment_firstHitThrough_of_le
      localPath outer localFinish L (heq ▸ hreturn)
    rw [← heq] at hfirst
    exact hfirst
  have hglobalInner : IsFirstHitSegment (trajectory omega) inner
      (t + localStart) (t + localFinish) horizon := by
    simpa only [localPath, inner, t, L] using
      (IsFirstHitSegment.of_profileGapWalk hcomplete hfinish hlocalInner)
  have hglobalOuter : IsFirstHitSegment (trajectory omega) outer
      (t + localFinish) (t + localReturn) horizon := by
    simpa only [localPath, outer, t, L] using
      (IsFirstHitSegment.of_profileGapWalk hcomplete hreturn hlocalOuter)
  exact ⟨hglobalInner, hglobalOuter⟩

/-! ## Parent-major global clock identification -/

/-- The local child return in one parent gap is exactly the global
scale-`k+1` profile gap at its parent-major prefix-sum index. -/
theorem profileChildClocks_eq_parentLocal
    {omega : StepPath} {n horizon k parents parent j : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparent : parent < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (hj : j < profileGapOffspringCount omega n horizon x k parent) :
    let childIndex := (∑ i ∈ Finset.range parent,
      profileGapOffspringCount omega n horizon x k i) + j
    let localPath := profileGapWalk omega n horizon x k parent
    let outer := profileInnerBoundary n k x
    let inner := profileInnerBoundary n (k + 1) x
    let L := profileGapLength omega n horizon x k parent
    let localFinish :=
      @excursionFinish localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L j
    let localReturn :=
      @excursionStart localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L (j + 1)
    let t := profileInnerHitTime (trajectory omega) n horizon x k parent
    profileInnerHitTime (trajectory omega) n horizon x (k + 1) childIndex =
        t + localFinish ∧
      profileGapExitTime (trajectory omega) n horizon x (k + 1) childIndex =
        t + localReturn := by
  classical
  dsimp only
  let childIndex := (∑ i ∈ Finset.range parent,
    profileGapOffspringCount omega n horizon x k i) + j
  let localPath := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let L := profileGapLength omega n horizon x k parent
  let localStart := excursionStart localPath outer inner L j
  let localFinish := excursionFinish localPath outer inner L j
  let localReturn := excursionStart localPath outer inner L (j + 1)
  let t := profileInnerHitTime (trajectory omega) n horizon x k parent
  let u := profileGapExitTime (trajectory omega) n horizon x k parent
  have hreturn : localReturn ≤ L := by
    simpa only [localReturn, localPath, outer, inner, L] using
      profileGapChildStart_succ_le hn hk0 hk (hcomplete parent hparent) hj
  have hfinish : localFinish ≤ L :=
    (excursionFinish_le_next_start localPath outer inner L j).trans hreturn
  have hstart : localStart ≤ L :=
    (excursionStart_le_finish localPath outer inner L j).trans hfinish
  have hscan : scanThrough (trajectory omega) outer inner (t + localStart) =
      ⟨false, childIndex⟩ := by
    simpa only [outer, inner, t, localStart, localPath, L, childIndex] using
      scanThrough_absoluteProfileGapChildStart_eq
        hn hk0 hk hx hparent hcomplete hstart
  have hsegments :
      IsFirstHitSegment (trajectory omega) inner
          (t + localStart) (t + localFinish) horizon ∧
        IsFirstHitSegment (trajectory omega) outer
          (t + localFinish) (t + localReturn) horizon := by
    simpa only [inner, outer, t, localStart, localFinish, localReturn,
      localPath, L] using
      absoluteProfileGapChild_firstHitSegments
        hn hk0 hk (hcomplete parent hparent) hj
  have htu := profileInnerHitTime_le_profileGapExitTime
    (trajectory omega) n horizon x k parent
  have htL : t + L = u := by
    dsimp only [t, L, profileGapLength, u]
    omega
  have huH : u ≤ horizon := by
    simpa only [u] using hcomplete parent hparent
  have habsoluteStart : t + localStart ≤ horizon := by omega
  have hdisjoint : Disjoint outer inner :=
    adjacent_profileInnerBoundaries_disjoint (by omega : 1 ≤ n) hk x
  have hclocks := excursionFinish_eq_and_start_succ_eq_of_scanThrough
    hdisjoint hscan habsoluteStart hsegments.1 hsegments.2
  have houterEq : profileOuterBoundary n (k + 1) x = outer := by
    simp only [profileOuterBoundary, outer, profileInnerBoundary,
      Nat.add_sub_cancel]
  have hinnerEq : profileInnerBoundary n (k + 1) x = inner := rfl
  constructor
  · unfold profileInnerHitTime
    rw [houterEq, hinnerEq]
    exact hclocks.1
  · unfold profileGapExitTime profileOuterHitTime
    rw [houterEq, hinnerEq]
    exact hclocks.2

/-- Canonically indexed form of `profileChildClocks_eq_parentLocal`, using
the actual weak-composition child equivalence. -/
theorem profileChildClocks_actualProfileChildIndex
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    let localPath := profileGapWalk omega n horizon x k i
    let outer := profileInnerBoundary n k x
    let inner := profileInnerBoundary n (k + 1) x
    let L := profileGapLength omega n horizon x k i
    let localFinish :=
      @excursionFinish localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L j
    let localReturn :=
      @excursionStart localPath outer inner
        (Classical.decPred _) (Classical.decPred _) L (j + 1)
    let t := profileInnerHitTime (trajectory omega) n horizon x k i
    profileInnerHitTime (trajectory omega) n horizon x (k + 1)
          (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
            hchildCount hcomplete i j) =
        t + localFinish ∧
      profileGapExitTime (trajectory omega) n horizon x (k + 1)
          (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
            hchildCount hcomplete i j) =
        t + localReturn := by
  dsimp only
  have hclocks := profileChildClocks_eq_parentLocal
    hn hk0 hk hx i.isLt hcomplete j.isLt
  simpa only [actualProfileChildIndex_val] using hclocks



end

end Erdos1165.AnnularProfileChildClockIdentification

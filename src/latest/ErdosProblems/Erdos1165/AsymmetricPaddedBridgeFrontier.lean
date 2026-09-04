/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedBridgeClock
import ErdosProblems.Erdos1165.AsymmetricPaddedRecursiveFrontier
import ErdosProblems.Erdos1165.AnnularProfileChildWordIdentification

namespace Erdos1165.AsymmetricPaddedBridgeFrontier

open AlternatingConcatPrefixFree
open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AnnularProfileGapAtoms AnnularProfileLevelSkeleton
open AnnularProfileNestedEdge AnnularOffspringScan
open AnnularRecursiveBoundaryParser
open AnnularRecursiveDecoratedProfileCode AnnularOffspringKernelRadial
open AsymmetricPaddedBridgeCode AsymmetricPaddedParsedBridgeCode
open AsymmetricPaddedBridgeClock
open AsymmetricPaddedBridgeExtraction
open AsymmetricPaddedBridgeLiteralFactorization
open AnnularProfileOffspringPartition
open AnnularProfileChildClockIdentification
open AnnularProfileChildWordIdentification
open AsymmetricPaddedRecursiveFrontier AsymmetricPaddedRemoteRenewal
open MarkedBridgeFactorization PathInsertion PlanarPotential RealDiscFinite
open ProfileGapChain
open TerminalBoundaryScan TerminalClockSplice
open TerminalExcursionPathwise TerminalProfileBoundarySeparation
open TerminalSkeletonWords TerminalSpliceProfileGeometry
open ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable
attribute [-simp] AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn

/-! ## Translation of profile clocks to an arbitrary bridge start -/

theorem trajectory_profileInnerBoundary_iff_trajectoryFrom
    (origin center : Point) (omega : StepPath) (n k q : ℕ) :
    trajectory omega q ∈ profileInnerBoundary n k (center - origin) ↔
      trajectoryFrom origin omega q ∈ profileInnerBoundary n k center := by
  unfold profileInnerBoundary
  have hpoint : trajectory omega q - (center - origin) =
      trajectoryFrom origin omega q - center := by
    rw [trajectoryFrom_eq_add_trajectory]
    abel
  constructor
  · intro h
    apply (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (scaleRadius n k) (trajectoryFrom origin omega q)).mpr
    rw [← hpoint]
    exact (BoundaryStoppedHarnack.mem_discBoundary_translate
      (center - origin) (scaleRadius n k) (trajectory omega q)).mp h
  · intro h
    apply (BoundaryStoppedHarnack.mem_discBoundary_translate
      (center - origin) (scaleRadius n k) (trajectory omega q)).mpr
    rw [hpoint]
    exact (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (scaleRadius n k) (trajectoryFrom origin omega q)).mp h

theorem trajectory_profileOuterBoundary_iff_trajectoryFrom
    (origin center : Point) (omega : StepPath) (n k q : ℕ) :
    trajectory omega q ∈ profileOuterBoundary n k (center - origin) ↔
      trajectoryFrom origin omega q ∈ profileOuterBoundary n k center := by
  simpa only [profileOuterBoundary, profileInnerBoundary] using
    trajectory_profileInnerBoundary_iff_trajectoryFrom
      origin center omega n (k - 1) q

theorem firstHitThrough_eq_of_mem_iff
    {s t : WalkPath} {A B : Set Point}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hmem : ∀ q, s q ∈ A ↔ t q ∈ B) (start horizon : ℕ) :
    firstHitThrough s A start horizon =
      firstHitThrough t B start horizon := by
  unfold firstHitThrough hitTimesThrough
  have htimes :
      Finset.filter (fun q ↦ s q ∈ A) (Finset.Icc start horizon) =
        Finset.filter (fun q ↦ t q ∈ B) (Finset.Icc start horizon) := by
    apply Finset.filter_congr
    intro q _hq
    exact hmem q
  rw [htimes]

theorem excursionStart_eq_of_mem_iff
    {s t : WalkPath} {outerS innerS outerT innerT : Set Point}
    [DecidablePred (· ∈ outerS)] [DecidablePred (· ∈ innerS)]
    [DecidablePred (· ∈ outerT)] [DecidablePred (· ∈ innerT)]
    (houter : ∀ q, s q ∈ outerS ↔ t q ∈ outerT)
    (hinner : ∀ q, s q ∈ innerS ↔ t q ∈ innerT)
    (horizon j : ℕ) :
    excursionStart s outerS innerS horizon j =
      excursionStart t outerT innerT horizon j := by
  have hstep : excursionStep s outerS innerS horizon =
      excursionStep t outerT innerT horizon := by
    funext start
    unfold excursionStep
    rw [firstHitThrough_eq_of_mem_iff houter,
      firstHitThrough_eq_of_mem_iff hinner]
  unfold excursionStart
  rw [hstep, firstHitThrough_eq_of_mem_iff houter]

theorem excursionFinish_eq_of_mem_iff
    {s t : WalkPath} {outerS innerS outerT innerT : Set Point}
    [DecidablePred (· ∈ outerS)] [DecidablePred (· ∈ innerS)]
    [DecidablePred (· ∈ outerT)] [DecidablePred (· ∈ innerT)]
    (houter : ∀ q, s q ∈ outerS ↔ t q ∈ outerT)
    (hinner : ∀ q, s q ∈ innerS ↔ t q ∈ innerT)
    (horizon j : ℕ) :
    excursionFinish s outerS innerS horizon j =
      excursionFinish t outerT innerT horizon j := by
  unfold excursionFinish
  rw [excursionStart_eq_of_mem_iff houter hinner,
    firstHitThrough_eq_of_mem_iff hinner]

theorem completedExcursionCount_eq_of_mem_iff
    {s t : WalkPath} {outerS innerS outerT innerT : Set Point}
    [DecidablePred (· ∈ outerS)] [DecidablePred (· ∈ innerS)]
    [DecidablePred (· ∈ outerT)] [DecidablePred (· ∈ innerT)]
    (houter : ∀ q, s q ∈ outerS ↔ t q ∈ outerT)
    (hinner : ∀ q, s q ∈ innerS ↔ t q ∈ innerT)
    (horizon : ℕ) :
    completedExcursionCount s outerS innerS horizon =
      completedExcursionCount t outerT innerT horizon := by
  unfold completedExcursionCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _hj
  rw [excursionFinish_eq_of_mem_iff houter hinner]

theorem profileOuterHitTime_translate
    (origin center : Point) (omega : StepPath) (n horizon k j : ℕ) :
    profileOuterHitTime (trajectory omega) n horizon (center - origin) k j =
      profileOuterHitTime (trajectoryFrom origin omega) n horizon center k j := by
  unfold profileOuterHitTime
  exact excursionStart_eq_of_mem_iff
    (trajectory_profileOuterBoundary_iff_trajectoryFrom
      origin center omega n k)
    (trajectory_profileInnerBoundary_iff_trajectoryFrom
      origin center omega n k) horizon j

theorem profileInnerHitTime_translate
    (origin center : Point) (omega : StepPath) (n horizon k j : ℕ) :
    profileInnerHitTime (trajectory omega) n horizon (center - origin) k j =
      profileInnerHitTime (trajectoryFrom origin omega) n horizon center k j := by
  unfold profileInnerHitTime
  exact excursionFinish_eq_of_mem_iff
    (trajectory_profileOuterBoundary_iff_trajectoryFrom
      origin center omega n k)
    (trajectory_profileInnerBoundary_iff_trajectoryFrom
      origin center omega n k) horizon j

theorem profileGapExitTime_translate
    (origin center : Point) (omega : StepPath) (n horizon k j : ℕ) :
    profileGapExitTime (trajectory omega) n horizon (center - origin) k j =
      profileGapExitTime (trajectoryFrom origin omega) n horizon center k j := by
  unfold profileGapExitTime
  exact profileOuterHitTime_translate origin center omega n horizon k (j + 1)

theorem profileCompletedCount_translate
    (origin center : Point) (omega : StepPath) (n horizon k : ℕ) :
    profileCompletedCount (trajectory omega) n horizon
        (center - origin) k =
      profileCompletedCount (trajectoryFrom origin omega) n horizon center k := by
  unfold profileCompletedCount
  exact completedExcursionCount_eq_of_mem_iff
    (trajectory_profileOuterBoundary_iff_trajectoryFrom
      origin center omega n k)
    (trajectory_profileInnerBoundary_iff_trajectoryFrom
      origin center omega n k) horizon

/-! ## An origin-free first profile prefix -/

def directPaddedParentSchedule
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) :
    FirstHitExcursionSchedule
      (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) source.bridge.1.1
      (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge) := by
  let s := trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := source.bridge.1.1
  let count := paddedBridgeReturnCount n l p center source.start.1
    source.endpoint.1 source.bridge
  have hcount : completedExcursionCount s outer inner horizon = count := rfl
  have hcountLe : count ≤ horizon + 1 := by
    rw [← hcount]
    exact completedExcursionCount_le s outer inner horizon
  have hinner : ∀ j, j < count →
      excursionFinish s outer inner horizon j ≤ horizon := by
    intro j hj
    apply finish_le_horizon_of_lt_completedExcursionCount
    rwa [hcount]
  have houterZero : excursionStart s outer inner horizon 0 ≤ horizon := by
    exact (excursionStart_le_finish s outer inner horizon 0).trans
      (hinner 0 hparents)
  have houterSucc : ∀ j, j < count →
      excursionStart s outer inner horizon (j + 1) ≤ horizon := by
    intro j hj
    simpa only [s, outer, inner, horizon, count] using
      (paddedBridgeReturnComplete hn hlp hp source.bridge ⟨j, hj⟩)
  have hdisjoint : Disjoint outer inner := by
    have hp' : (p - 1) + 1 ≤ n := by omega
    simpa only [outer, inner, Nat.sub_add_cancel (by omega : 0 < p)] using
      (adjacent_profileInnerBoundaries_disjoint
        (by omega : 1 ≤ n) hp' center)
  have hnext : excursionFinish s outer inner horizon count = horizon + 1 := by
    have hsent := excursionFinish_completedExcursionCount_eq_sentinel
      s outer inner hdisjoint horizon
    rw [hcount] at hsent
    exact hsent
  exact FirstHitExcursionSchedule.ofExactClocks s outer inner horizon count
    hcountLe houterZero hinner houterSucc hnext

theorem paddedPath_avoids_inner_before_first_outer
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) :
    ∀ q < excursionStart
        (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) source.bridge.1.1 0,
      trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1) q ∉
        profileInnerBoundary n p center := by
  classical
  let s := trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := source.bridge.1.1
  have hcount : completedExcursionCount s outer inner horizon =
      paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge := rfl
  have hfinish : excursionFinish s outer inner horizon 0 ≤ horizon := by
    apply finish_le_horizon_of_lt_completedExcursionCount
    rw [hcount]
    exact hparents
  have houterLe : excursionStart s outer inner horizon 0 ≤ horizon :=
    (excursionStart_le_finish s outer inner horizon 0).trans hfinish
  have hfirstOuter : IsFirstHitSegment s outer 0
      (excursionStart s outer inner horizon 0) horizon := by
    simpa only [excursionStart, Function.iterate_zero_apply] using
      (isFirstHitSegment_firstHitThrough_of_le s outer 0 horizon houterLe)
  by_cases hadjacent : p = l + 2
  · have hstart : s 0 ∈ profileInnerBoundary n (p - 1) center := by
      have hlevel : p - 1 = l + 1 := by omega
      simpa only [s, trajectoryFrom_zero, profileInnerBoundary, hlevel] using
        (mem_discBoundaryFinset.mp source.start.2)
    have hzero : excursionStart s outer inner horizon 0 = 0 := by
      by_contra hne
      exact hfirstOuter.2.2.2 0 (Nat.zero_le _)
        (Nat.pos_of_ne_zero hne) hstart
    intro q hq
    rw [hzero] at hq
    omega
  · have hgap : l + 2 < p := by omega
    have hsepStep :
        scaleRadius n (p - 1) + 1 ≤ scaleRadius n (p - 2) :=
      scaleRadius_add_one_le_previous hn (by omega) (by omega)
    have hsep :
        scaleRadius n (p - 1) + 1 ≤ scaleRadius n (l + 1) :=
      hsepStep.trans (scaleRadius_antitone_of_le (by omega) (by omega))
    have hstartOutside : source.start.1 ∉
        disc center (scaleRadius n (p - 1)) := by
      exact not_mem_smaller_disc_of_mem_larger_boundary hsep
        (mem_discBoundaryFinset.mp source.start.2)
    intro q hq hqInner
    have hqDisc : s q ∈ disc center (scaleRadius n (p - 1)) :=
      hqInner.1.trans (scaleRadius_antitone_of_le (by omega) hp)
    obtain ⟨e, he0, heq, heBoundary⟩ := exists_discBoundary_between
      (s := s) (center := center) (radius := scaleRadius n (p - 1))
      (start := 0) (stop := q)
      (fun r ↦ TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ
        source.start.1 (extendStoppedWord source.bridge.1) r)
      (Nat.zero_le q) (by simpa only [s, trajectoryFrom_zero] using hstartOutside)
      hqDisc
    exact hfirstOuter.2.2.2 e he0 (heq.trans_lt hq)
      (by simpa only [outer, profileInnerBoundary] using heBoundary)

/-- A literal visit to the level-`p` boundary forces at least one completed
level-`p` entrance in the padded bridge. -/
theorem paddedBridgeReturnCount_pos_of_inner_hit
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) {q : ℕ}
    (hqH : q ≤ source.bridge.1.1)
    (hqmem : trajectoryFrom source.start.1
      (extendStoppedWord source.bridge.1) q ∈
        profileInnerBoundary n p center) :
    0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge := by
  let s := trajectoryFrom source.start.1
    (extendStoppedWord source.bridge.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := source.bridge.1.1
  have hstartLe : excursionStart s outer inner horizon 0 ≤ q := by
    change firstHitThrough s outer 0 horizon ≤ q
    by_cases hadjacent : p = l + 2
    · have hstart : s 0 ∈ outer := by
        have hlevel : p - 1 = l + 1 := by omega
        simpa only [s, outer, trajectoryFrom_zero, profileInnerBoundary,
          hlevel] using (mem_discBoundaryFinset.mp source.start.2)
      exact (firstHitThrough_le_of_mem (Nat.zero_le 0)
        (Nat.zero_le horizon) hstart).trans (Nat.zero_le q)
    · have hgap : l + 2 < p := by omega
      have hsepStep :
          scaleRadius n (p - 1) + 1 ≤ scaleRadius n (p - 2) :=
        scaleRadius_add_one_le_previous hn (by omega) (by omega)
      have hsep :
          scaleRadius n (p - 1) + 1 ≤ scaleRadius n (l + 1) :=
        hsepStep.trans (scaleRadius_antitone_of_le (by omega) (by omega))
      have hstartOutside : source.start.1 ∉
          disc center (scaleRadius n (p - 1)) :=
        not_mem_smaller_disc_of_mem_larger_boundary hsep
          (mem_discBoundaryFinset.mp source.start.2)
      have hqDisc : s q ∈ disc center (scaleRadius n (p - 1)) :=
        hqmem.1.trans (scaleRadius_antitone_of_le (by omega) hp)
      obtain ⟨e, he0, heq, heBoundary⟩ := exists_discBoundary_between
        (s := s) (center := center) (radius := scaleRadius n (p - 1))
        (start := 0) (stop := q)
        (fun r ↦ TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ
          source.start.1 (extendStoppedWord source.bridge.1) r)
        (Nat.zero_le q)
        (by simpa only [s, trajectoryFrom_zero] using hstartOutside) hqDisc
      have hfirst : firstHitThrough s outer 0 horizon ≤ e := by
        apply firstHitThrough_le_of_mem he0 (heq.trans hqH)
        simpa only [outer, profileInnerBoundary] using heBoundary
      exact hfirst.trans heq
  have hfinish : excursionFinish s outer inner horizon 0 ≤ horizon := by
    change firstHitThrough s inner
      (excursionStart s outer inner horizon 0) horizon ≤ horizon
    exact (firstHitThrough_le_of_mem hstartLe hqH
      (by simpa only [s, inner] using hqmem)).trans hqH
  change 0 < completedExcursionCount s outer inner horizon
  exact (completedExcursionCount_pos_iff s outer inner horizon).2
    ⟨0, Nat.zero_le horizon, hfinish⟩

/-- A completed level-`p+1` entrance always has a level-`p` parent. -/
theorem paddedBridgeReturnCount_pos_of_succ_pos
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hchildren : 0 < paddedBridgeReturnCount n l (p + 1) center
      source.start.1 source.endpoint.1 source.bridge) :
    0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge := by
  let s := trajectoryFrom source.start.1
    (extendStoppedWord source.bridge.1)
  let horizon := source.bridge.1.1
  let outer := profileInnerBoundary n p center
  let inner := profileInnerBoundary n (p + 1) center
  have hfinish : excursionFinish s outer inner horizon 0 ≤ horizon := by
    apply finish_le_horizon_of_lt_completedExcursionCount
    simpa only [paddedBridgeReturnCount, boundaryExcursionCount,
      show p + 1 - 1 = p by omega, s, outer, inner, horizon] using hchildren
  have hstart : excursionStart s outer inner horizon 0 ≤ horizon :=
    (excursionStart_le_finish s outer inner horizon 0).trans hfinish
  have hmem : s (excursionStart s outer inner horizon 0) ∈
      profileInnerBoundary n p center := by
    simpa only [outer] using
      (excursionStart_mem_outer_of_finish_le s outer inner horizon 0 hfinish)
  exact paddedBridgeReturnCount_pos_of_inner_hit hn hlp (by omega) source
    hstart (by simpa only [s] using hmem)

theorem translated_scan_prefix_to_first_parent
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) :
    let omega := extendStoppedWord source.bridge.1
    let shiftedCenter := center - source.start.1
    @scanSegment (trajectory omega)
        (profileInnerBoundary n p shiftedCenter)
        (profileInnerBoundary n (p + 1) shiftedCenter)
        (Classical.decPred _) (Classical.decPred _)
        0 (profileInnerHitTime (trajectory omega) n source.bridge.1.1
          shiftedCenter p 0 + 1) initialState = ⟨false, 0⟩ := by
  classical
  dsimp only
  let omega := extendStoppedWord source.bridge.1
  let s := trajectoryFrom source.start.1 omega
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := source.bridge.1.1
  let a := excursionStart s outer inner horizon 0
  let b := excursionFinish s outer inner horizon 0
  let t := profileInnerHitTime (trajectory omega) n source.bridge.1.1
    (center - source.start.1) p 0
  have hcount : completedExcursionCount s outer inner horizon =
      paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge := rfl
  have hbH : b ≤ horizon := by
    dsimp only [b]
    apply finish_le_horizon_of_lt_completedExcursionCount
    rw [hcount]
    exact hparents
  have hab : a ≤ b := excursionStart_le_finish s outer inner horizon 0
  have hinnerFirst : IsFirstHitSegment s inner a b horizon := by
    dsimp only [b]
    exact isFirstHitSegment_firstHitThrough_of_le s inner a horizon hbH
  have ht : t = b := by
    rw [show t = profileInnerHitTime s n source.bridge.1.1 center p 0 by
      exact profileInnerHitTime_translate source.start.1 center omega n
        source.bridge.1.1 p 0]
    rfl
  have hfullFirst : IsFirstHitSegment s (profileInnerBoundary n p center)
      0 b source.bridge.1.1 := by
    refine ⟨Nat.zero_le _, hinnerFirst.2.1, hinnerFirst.2.2.1, ?_⟩
    intro q _hq0 hqt hqmem
    by_cases hqOuter : q < a
    · exact paddedPath_avoids_inner_before_first_outer hn hlp hp source
        hparents q hqOuter hqmem
    · exact hinnerFirst.2.2.2 q (Nat.le_of_not_gt hqOuter) hqt hqmem
  have horiginFirst : IsFirstHitSegment (trajectory omega)
      (profileInnerBoundary n p (center - source.start.1)) 0 t
      source.bridge.1.1 := by
    rw [ht]
    refine ⟨hfullFirst.1, hfullFirst.2.1, ?_, ?_⟩
    · exact (trajectory_profileInnerBoundary_iff_trajectoryFrom
        source.start.1 center omega n p _).mpr hfullFirst.2.2.1
    · intro q hq0 hqstop hqmem
      exact hfullFirst.2.2.2 q hq0 hqstop
        ((trajectory_profileInnerBoundary_iff_trajectoryFrom
          source.start.1 center omega n p q).mp hqmem)
  have hscan := scanSegment_after_firstOuter (trajectory omega)
      (profileInnerBoundary n p (center - source.start.1))
      (profileInnerBoundary n (p + 1) (center - source.start.1))
      (completed := 0) horiginFirst
  simpa only [t, Nat.sub_zero, initialState] using hscan

theorem profileCompletedCount_succ_eq_sum_offspring_of_prefix
    {omega : StepPath} {n horizon k parents : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparents : 0 < parents)
    (hcount : profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (hprefix :
      @scanSegment (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        0 (profileInnerHitTime (trajectory omega) n horizon x k 0 + 1)
        initialState = ⟨false, 0⟩) :
    profileCompletedCount (trajectory omega) n horizon x (k + 1) =
      ∑ i : Fin parents,
        profileGapOffspringCount omega n horizon x k i := by
  classical
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let entrance : ℕ → ℕ := fun i ↦
    profileInnerHitTime (trajectory omega) n horizon x k i
  let exit : ℕ → ℕ := fun i ↦
    profileGapExitTime (trajectory omega) n horizon x k i
  let offspring : ℕ → ℕ := fun i ↦
    profileGapOffspringCount omega n horizon x k i
  have hentranceExit : ∀ i < parents, entrance i ≤ exit i := by
    intro i _hi
    exact profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k i
  have hexitEntrance : ∀ i, i + 1 < parents →
      exit i ≤ entrance (i + 1) := by
    intro i hi
    exact profileGapExitTime_le_profileInnerHitTime_of_lt
      (trajectory omega) n horizon x k (by omega)
  have hlast : exit (parents - 1) ≤ horizon :=
    hcomplete (parents - 1) (by omega)
  have hscan :
      @scanThrough (trajectory omega) outer inner
          (Classical.decPred _) (Classical.decPred _) horizon =
        ⟨false, ∑ i ∈ Finset.range parents, offspring i⟩ := by
    apply scanThrough_eq_sum_of_interval_scans hparents entrance exit offspring
      hentranceExit hexitEntrance hlast
    · simpa only [outer, inner, entrance] using hprefix
    · intro i hi c
      exact scan_profileGap_add_offspring hn hk0 hk (hcomplete i hi) c
    · intro i hi c
      exact scan_between_parent_gaps hn hk0 hk hi hcomplete c
    · intro c
      exact scan_after_last_parent_gap hn hk0 hk hparents hcount hcomplete c
  have hdisjoint : Disjoint outer inner :=
    adjacent_profileInnerBoundaries_disjoint (by omega) hk x
  have hcompleted := scanThrough_completed_eq_completedExcursionCount
    (trajectory omega) outer inner hdisjoint horizon
  have hrange : profileCompletedCount (trajectory omega) n horizon x (k + 1) =
      ∑ i ∈ Finset.range parents, offspring i := by
    change completedExcursionCount (trajectory omega) outer inner horizon = _
    rw [← hcompleted]
    exact congrArg BoundaryScanState.completed hscan
  rw [hrange, Fin.sum_univ_eq_sum_range]

/-! ## Adjacent direct-return children -/

def directPaddedChildBridge
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    PaddedCoarseBridge n (p - 1) center where
  start := ⟨(directPaddedInnerPoint hn hlp hp source i).1, by
    change (directPaddedInnerPoint hn hlp hp source i).1 ∈
      discBoundaryFinset center (scaleRadius n (p - 1 + 1))
    simpa only [Nat.sub_add_cancel (by omega : 0 < p)] using
      (directPaddedInnerPoint hn hlp hp source i).2⟩
  endpoint := directPaddedMiddlePoint hn hlp hp source i
  bridge := by
    simpa only [profileOuterBoundary, profileInnerBoundary] using
      (directPaddedReturnWordCode hn hlp hp source i)

@[simp] theorem directPaddedChildBridge_start_val
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    (directPaddedChildBridge hn hlp hp source i).start.1 =
      (directPaddedInnerPoint hn hlp hp source i).1 := rfl

@[simp] theorem directPaddedChildBridge_endpoint_val
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    (directPaddedChildBridge hn hlp hp source i).endpoint.1 =
      (directPaddedMiddlePoint hn hlp hp source i).1 := rfl

@[simp] theorem directPaddedChildBridge_bridge_val
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    (directPaddedChildBridge hn hlp hp source i).bridge.1 =
      (directPaddedReturnWordCode hn hlp hp source i).1 := rfl

theorem directPaddedReturnWord_eq_profileGapStoppedWord
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    (directPaddedReturnWordCode hn hlp hp source i).1 =
      profileGapStoppedWord (extendStoppedWord source.bridge.1) n
        source.bridge.1.1 (center - source.start.1) p i := by
  let omega := extendStoppedWord source.bridge.1
  let s := trajectoryFrom source.start.1 omega
  let shiftedCenter := center - source.start.1
  have hinner := profileInnerHitTime_translate source.start.1 center omega n
    source.bridge.1.1 p i
  have hexit := profileGapExitTime_translate source.start.1 center omega n
    source.bridge.1.1 p i
  calc
    (directPaddedReturnWordCode hn hlp hp source i).1 =
        listStoppedWord
          (List.ofFn (directPaddedReturnWordCode hn hlp hp source i).1.2) :=
      (listStoppedWord_ofFn _).symm
    _ = listStoppedWord
        (incrementSlice omega
          (profileInnerHitTime (trajectory omega) n source.bridge.1.1
            shiftedCenter p i)
          (profileGapExitTime (trajectory omega) n source.bridge.1.1
            shiftedCenter p i)) := by
      rw [directPaddedReturnWordCode_toList]
      change listStoppedWord
          (incrementSlice omega
            (profileInnerHitTime s n source.bridge.1.1 center p i)
            (profileGapExitTime s n source.bridge.1.1 center p i)) = _
      rw [← hinner, ← hexit]
    _ = listStoppedWord
        (List.ofFn
          (profileGapStoppedWord omega n source.bridge.1.1
            shiftedCenter p i).2) := by
      rw [profileGapStoppedWord_toList]
    _ = profileGapStoppedWord omega n source.bridge.1.1
        shiftedCenter p i := listStoppedWord_ofFn _

theorem directPaddedInnerPoint_val_eq_add_profileGapStartPoint
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    (directPaddedInnerPoint hn hlp hp source i).1 =
      source.start.1 +
        profileGapStartPoint (extendStoppedWord source.bridge.1) n
          source.bridge.1.1 (center - source.start.1) p i := by
  let omega := extendStoppedWord source.bridge.1
  let s := trajectoryFrom source.start.1 omega
  have hclock := profileInnerHitTime_translate source.start.1 center omega n
    source.bridge.1.1 p i
  have hfinish : excursionFinish s
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) source.bridge.1.1 i =
      (profileInnerHitTime (trajectory omega) n source.bridge.1.1
        (center - source.start.1) p i) := by
    change profileInnerHitTime s n source.bridge.1.1 center p i = _
    exact hclock.symm
  change trajectoryFrom source.start.1 omega (excursionFinish s
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) source.bridge.1.1 i) =
    source.start.1 + trajectory omega
      (profileInnerHitTime (trajectory omega) n source.bridge.1.1
        (center - source.start.1) p i)
  rw [trajectoryFrom_eq_add_trajectory, hfinish]

theorem profileGapExtendedPath_add_eq_childPath
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) (q : ℕ) :
    source.start.1 +
        trajectoryFrom
          (profileGapStartPoint (extendStoppedWord source.bridge.1) n
            source.bridge.1.1 (center - source.start.1) p i)
          (extendStoppedWord
            (profileGapStoppedWord (extendStoppedWord source.bridge.1) n
              source.bridge.1.1 (center - source.start.1) p i)) q =
      trajectoryFrom (directPaddedChildBridge hn hlp hp source i).start.1
        (extendStoppedWord
          (directPaddedChildBridge hn hlp hp source i).bridge.1) q := by
  change source.start.1 + trajectoryFrom _ _ q =
    trajectoryFrom (directPaddedInnerPoint hn hlp hp source i).1
      (extendStoppedWord
        (directPaddedReturnWordCode hn hlp hp source i).1) q
  rw [directPaddedReturnWord_eq_profileGapStoppedWord]
  rw [directPaddedInnerPoint_val_eq_add_profileGapStartPoint]
  unfold trajectoryFrom
  abel

theorem point_mem_profileInnerBoundary_iff_add
    (origin center z : Point) (n k : ℕ) :
    z ∈ profileInnerBoundary n k (center - origin) ↔
      origin + z ∈ profileInnerBoundary n k center := by
  unfold profileInnerBoundary
  constructor
  · intro h
    apply (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (scaleRadius n k) (origin + z)).mpr
    have h' := (BoundaryStoppedHarnack.mem_discBoundary_translate
      (center - origin) (scaleRadius n k) z).mp h
    convert h' using 1 <;> abel
  · intro h
    apply (BoundaryStoppedHarnack.mem_discBoundary_translate
      (center - origin) (scaleRadius n k) z).mpr
    have h' := (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (scaleRadius n k) (origin + z)).mp h
    convert h' using 1 <;> abel

theorem profileGapOffspringCount_eq_paddedChildCount
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    profileGapOffspringCount (extendStoppedWord source.bridge.1) n
        source.bridge.1.1 (center - source.start.1) p i =
      paddedBridgeReturnCount n (p - 1) (p + 1) center
        (directPaddedChildBridge hn hlp hp source i).start.1
        (directPaddedChildBridge hn hlp hp source i).endpoint.1
        (directPaddedChildBridge hn hlp hp source i).bridge := by
  let omega := extendStoppedWord source.bridge.1
  let shiftedCenter := center - source.start.1
  let child := directPaddedChildBridge hn hlp hp source i
  let L := profileGapLength omega n source.bridge.1.1 shiftedCenter p i
  let actual := profileGapWalk omega n source.bridge.1.1 shiftedCenter p i
  let extended := trajectoryFrom
    (profileGapStartPoint omega n source.bridge.1.1 shiftedCenter p i)
    (extendStoppedWord
      (profileGapStoppedWord omega n source.bridge.1.1 shiftedCenter p i))
  let childPath := trajectoryFrom child.start.1
    (extendStoppedWord child.bridge.1)
  have hword : child.bridge.1 =
      profileGapStoppedWord omega n source.bridge.1.1 shiftedCenter p i := by
    simpa only [child, omega, shiftedCenter,
      directPaddedChildBridge_bridge_val] using
      (directPaddedReturnWord_eq_profileGapStoppedWord hn hlp hp source i)
  have hlength : child.bridge.1.1 = L := by
    rw [hword]
    rfl
  have hactualExtended : ∀ q ≤ L, actual q = extended q := by
    intro q hq
    simpa only [actual, extended, L] using
      (profileGapWalk_eq_extendStoppedWord_through
        (omega := omega) (n := n) (horizon := source.bridge.1.1)
        (x := shiftedCenter) (k := p) (parent := (i : ℕ)) hq)
  have houter : ∀ q,
      extended q ∈ profileInnerBoundary n p shiftedCenter ↔
        childPath q ∈ profileInnerBoundary n p center := by
    intro q
    have hpath := profileGapExtendedPath_add_eq_childPath
      hn hlp hp source i q
    have hpath' : source.start.1 + extended q = childPath q := by
      simpa only [omega, shiftedCenter, extended, childPath, child] using hpath
    change extended q ∈ profileInnerBoundary n p shiftedCenter ↔
      childPath q ∈ profileInnerBoundary n p center
    rw [← hpath']
    exact point_mem_profileInnerBoundary_iff_add
      source.start.1 center (extended q) n p
  have hinner : ∀ q,
      extended q ∈ profileInnerBoundary n (p + 1) shiftedCenter ↔
        childPath q ∈ profileInnerBoundary n (p + 1) center := by
    intro q
    have hpath := profileGapExtendedPath_add_eq_childPath
      hn hlp hp source i q
    have hpath' : source.start.1 + extended q = childPath q := by
      simpa only [omega, shiftedCenter, extended, childPath, child] using hpath
    change extended q ∈ profileInnerBoundary n (p + 1) shiftedCenter ↔
      childPath q ∈ profileInnerBoundary n (p + 1) center
    rw [← hpath']
    exact point_mem_profileInnerBoundary_iff_add
      source.start.1 center (extended q) n (p + 1)
  change completedExcursionCount actual
      (profileInnerBoundary n p shiftedCenter)
      (profileInnerBoundary n (p + 1) shiftedCenter) L =
    completedExcursionCount childPath
      (profileInnerBoundary n p center)
      (profileInnerBoundary n (p + 1) center) child.bridge.1.1
  rw [hlength]
  calc
    completedExcursionCount actual
        (profileInnerBoundary n p shiftedCenter)
        (profileInnerBoundary n (p + 1) shiftedCenter) L =
      completedExcursionCount extended
        (profileInnerBoundary n p shiftedCenter)
        (profileInnerBoundary n (p + 1) shiftedCenter) L :=
      Proposition13Measurability.completedExcursionCount_congr_prefix
        hactualExtended _ _
    _ = completedExcursionCount childPath
        (profileInnerBoundary n p center)
        (profileInnerBoundary n (p + 1) center) L :=
      completedExcursionCount_eq_of_mem_iff houter hinner L

theorem paddedBridgeReturnCount_succ_eq_sum_children
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) :
    paddedBridgeReturnCount n l (p + 1) center source.start.1
        source.endpoint.1 source.bridge =
      ∑ i : Fin (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge),
        paddedBridgeReturnCount n (p - 1) (p + 1) center
          (directPaddedChildBridge hn hlp (by omega) source i).start.1
          (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
          (directPaddedChildBridge hn hlp (by omega) source i).bridge := by
  let omega := extendStoppedWord source.bridge.1
  let shiftedCenter := center - source.start.1
  let parents := paddedBridgeReturnCount n l p center source.start.1
    source.endpoint.1 source.bridge
  have hparentCount : profileCompletedCount (trajectory omega) n
      source.bridge.1.1 shiftedCenter p = parents := by
    calc
      profileCompletedCount (trajectory omega) n source.bridge.1.1
          shiftedCenter p =
        profileCompletedCount
          (trajectoryFrom source.start.1 omega) n source.bridge.1.1 center p :=
        profileCompletedCount_translate source.start.1 center omega n
          source.bridge.1.1 p
      _ = parents := by
        rfl
  have hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n source.bridge.1.1
        shiftedCenter p i ≤ source.bridge.1.1 := by
    intro i hi
    rw [profileGapExitTime_translate source.start.1 center omega n
      source.bridge.1.1 p i]
    change excursionStart (trajectoryFrom source.start.1 omega)
      (profileOuterBoundary n p center) (profileInnerBoundary n p center)
      source.bridge.1.1 (i + 1) ≤ source.bridge.1.1
    rw [show profileOuterBoundary n p center =
      profileInnerBoundary n (p - 1) center by rfl]
    exact paddedBridgeReturnComplete hn hlp (by omega : p ≤ n)
      source.bridge ⟨i, hi⟩
  have hprefix := translated_scan_prefix_to_first_parent
    hn hlp (by omega : p ≤ n) source hparents
  have hpartition := profileCompletedCount_succ_eq_sum_offspring_of_prefix
    hn (by omega : 0 < p) hp1 hparents hparentCount hcomplete hprefix
  have hchildCount :
      profileCompletedCount (trajectory omega) n source.bridge.1.1
          shiftedCenter (p + 1) =
        paddedBridgeReturnCount n l (p + 1) center source.start.1
          source.endpoint.1 source.bridge := by
    calc
      profileCompletedCount (trajectory omega) n source.bridge.1.1
          shiftedCenter (p + 1) =
        profileCompletedCount
          (trajectoryFrom source.start.1 omega) n source.bridge.1.1
            center (p + 1) :=
        profileCompletedCount_translate source.start.1 center omega n
          source.bridge.1.1 (p + 1)
      _ = paddedBridgeReturnCount n l (p + 1) center source.start.1
          source.endpoint.1 source.bridge := by
        rfl
  rw [← hchildCount, hpartition]
  apply Finset.sum_congr rfl
  intro i _hi
  exact profileGapOffspringCount_eq_paddedChildCount
    hn hlp (by omega : p ≤ n) source i

/-! ## Parent-major clocks from an explicit first prefix -/

theorem scanThrough_profileParentEntrance_eq_prefixOffspring_of_prefix
    {omega : StepPath} {n horizon k parents parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparent : parent < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (hfirstPrefix :
      @scanThrough (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k 0) =
          ⟨false, 0⟩) :
    @scanThrough (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k parent) =
      ⟨false, ∑ i ∈ Finset.range parent,
        profileGapOffspringCount omega n horizon x k i⟩ := by
  classical
  induction parent with
  | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty] using hfirstPrefix
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

theorem scanThrough_absoluteProfileGapChildStart_eq_of_prefix
    {omega : StepPath} {n horizon k parents parent j : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparent : parent < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (hfirstPrefix :
      @scanThrough (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k 0) =
          ⟨false, 0⟩)
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
    adjacent_profileInnerBoundaries_disjoint (by omega) hk x
  have hprefix : scanThrough globalPath outer inner t =
      ⟨false, prefixCount⟩ := by
    simpa only [globalPath, outer, inner, t, prefixCount] using
      scanThrough_profileParentEntrance_eq_prefixOffspring_of_prefix
        hn hk0 hk hparent hcomplete hfirstPrefix
  have hlocalScan : scanSegment localPath outer inner 0 (localStart + 1)
      initialState = ⟨false, j⟩ :=
    scan_to_excursionStart localPath outer inner hdisjoint L j hlocalStart
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
    apply congrArg (trajectory omega)
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

theorem profileChildClocks_eq_parentLocal_of_prefix
    {omega : StepPath} {n horizon k parents parent j : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparent : parent < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (hfirstPrefix :
      @scanThrough (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k 0) =
          ⟨false, 0⟩)
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
      scanThrough_absoluteProfileGapChildStart_eq_of_prefix
        hn hk0 hk hparent hcomplete hfirstPrefix hstart
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
    adjacent_profileInnerBoundaries_disjoint (by omega) hk x
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

theorem profileGapChildClocks_eq_paddedChildBridge
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    (hcomplete : profileGapExitTime
      (trajectory (extendStoppedWord source.bridge.1)) n source.bridge.1.1
      (center - source.start.1) p i ≤ source.bridge.1.1)
    (j : ℕ) :
    let omega := extendStoppedWord source.bridge.1
    let shiftedCenter := center - source.start.1
    let child := directPaddedChildBridge hn hlp hp source i
    let actual := profileGapWalk omega n source.bridge.1.1 shiftedCenter p i
    let childPath := trajectoryFrom child.start.1
      (extendStoppedWord child.bridge.1)
    let L := profileGapLength omega n source.bridge.1.1 shiftedCenter p i
    excursionFinish actual
        (profileInnerBoundary n p shiftedCenter)
        (profileInnerBoundary n (p + 1) shiftedCenter) L j =
      excursionFinish childPath
        (profileInnerBoundary n p center)
        (profileInnerBoundary n (p + 1) center) child.bridge.1.1 j ∧
    excursionStart actual
        (profileInnerBoundary n p shiftedCenter)
        (profileInnerBoundary n (p + 1) shiftedCenter) L (j + 1) =
      excursionStart childPath
        (profileInnerBoundary n p center)
        (profileInnerBoundary n (p + 1) center) child.bridge.1.1 (j + 1) := by
  classical
  dsimp only
  let omega := extendStoppedWord source.bridge.1
  let shiftedCenter := center - source.start.1
  let child := directPaddedChildBridge hn hlp hp source i
  let L := profileGapLength omega n source.bridge.1.1 shiftedCenter p i
  let actual := profileGapWalk omega n source.bridge.1.1 shiftedCenter p i
  let extended := trajectoryFrom
    (profileGapStartPoint omega n source.bridge.1.1 shiftedCenter p i)
    (extendStoppedWord
      (profileGapStoppedWord omega n source.bridge.1.1 shiftedCenter p i))
  let childPath := trajectoryFrom child.start.1
    (extendStoppedWord child.bridge.1)
  have hword : child.bridge.1 =
      profileGapStoppedWord omega n source.bridge.1.1 shiftedCenter p i := by
    simpa only [child, omega, shiftedCenter,
      directPaddedChildBridge_bridge_val] using
      (directPaddedReturnWord_eq_profileGapStoppedWord hn hlp hp source i)
  have hlength : child.bridge.1.1 = L := by
    rw [hword]
    rfl
  have houter : ∀ q,
      extended q ∈ profileInnerBoundary n p shiftedCenter ↔
        childPath q ∈ profileInnerBoundary n p center := by
    intro q
    have hpath := profileGapExtendedPath_add_eq_childPath
      hn hlp hp source i q
    have hpath' : source.start.1 + extended q = childPath q := by
      simpa only [omega, shiftedCenter, extended, childPath, child] using hpath
    rw [← hpath']
    exact point_mem_profileInnerBoundary_iff_add
      source.start.1 center (extended q) n p
  have hinner : ∀ q,
      extended q ∈ profileInnerBoundary n (p + 1) shiftedCenter ↔
        childPath q ∈ profileInnerBoundary n (p + 1) center := by
    intro q
    have hpath := profileGapExtendedPath_add_eq_childPath
      hn hlp hp source i q
    have hpath' : source.start.1 + extended q = childPath q := by
      simpa only [omega, shiftedCenter, extended, childPath, child] using hpath
    rw [← hpath']
    exact point_mem_profileInnerBoundary_iff_add
      source.start.1 center (extended q) n (p + 1)
  have hactual := extractedProfileReturn_clocks_eq_actual hcomplete j
  dsimp only at hactual
  have hfinishTranslate : excursionFinish extended
      (profileInnerBoundary n p shiftedCenter)
      (profileInnerBoundary n (p + 1) shiftedCenter) L j =
      excursionFinish childPath
      (profileInnerBoundary n p center)
      (profileInnerBoundary n (p + 1) center) L j :=
    excursionFinish_eq_of_mem_iff houter hinner L j
  have hstartTranslate : excursionStart extended
      (profileInnerBoundary n p shiftedCenter)
      (profileInnerBoundary n (p + 1) shiftedCenter) L (j + 1) =
      excursionStart childPath
      (profileInnerBoundary n p center)
      (profileInnerBoundary n (p + 1) center) L (j + 1) :=
    excursionStart_eq_of_mem_iff houter hinner L (j + 1)
  rw [hlength]
  constructor
  · exact hactual.1.symm.trans hfinishTranslate
  · exact hactual.2.symm.trans hstartTranslate

noncomputable def paddedChildGapPattern
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) :
    GapPattern
      (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge)
      (paddedBridgeReturnCount n l (p + 1) center source.start.1
        source.endpoint.1 source.bridge) :=
  gapPatternOfMultiplicities
    (fun i ↦ paddedBridgeReturnCount n (p - 1) (p + 1) center
      (directPaddedChildBridge hn hlp (by omega) source i).start.1
      (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
      (directPaddedChildBridge hn hlp (by omega) source i).bridge)
    (paddedBridgeReturnCount_succ_eq_sum_children
      hn hlp hp1 source hparents).symm

@[simp] theorem gapMultiplicity_paddedChildGapPattern
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    gapMultiplicity (paddedChildGapPattern hn hlp hp1 source hparents) i =
      paddedBridgeReturnCount n (p - 1) (p + 1) center
        (directPaddedChildBridge hn hlp (by omega) source i).start.1
        (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
        (directPaddedChildBridge hn hlp (by omega) source i).bridge := by
  exact gapMultiplicity_gapPatternOfMultiplicities _ _ i

noncomputable def paddedChildIndex
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    (j : Fin (paddedBridgeReturnCount n (p - 1) (p + 1) center
      (directPaddedChildBridge hn hlp (by omega) source i).start.1
      (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
      (directPaddedChildBridge hn hlp (by omega) source i).bridge)) :
    Fin (paddedBridgeReturnCount n l (p + 1) center source.start.1
      source.endpoint.1 source.bridge) :=
  gapChildIndexEquiv (paddedChildGapPattern hn hlp hp1 source hparents)
    ⟨i, Fin.cast
      (gapMultiplicity_paddedChildGapPattern hn hlp hp1 source hparents i).symm
      j⟩

@[simp] theorem paddedChildIndex_val
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    (j : Fin (paddedBridgeReturnCount n (p - 1) (p + 1) center
      (directPaddedChildBridge hn hlp (by omega) source i).start.1
      (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
      (directPaddedChildBridge hn hlp (by omega) source i).bridge)) :
    (paddedChildIndex hn hlp hp1 source hparents i j : ℕ) =
      (∑ h : Fin i,
        paddedBridgeReturnCount n (p - 1) (p + 1) center
          (directPaddedChildBridge hn hlp (by omega) source
            (Fin.castLE i.isLt.le h)).start.1
          (directPaddedChildBridge hn hlp (by omega) source
            (Fin.castLE i.isLt.le h)).endpoint.1
          (directPaddedChildBridge hn hlp (by omega) source
            (Fin.castLE i.isLt.le h)).bridge) + j := by
  unfold paddedChildIndex
  rw [gapChildIndexEquiv_val]
  simp only [Fin.val_cast, gapMultiplicity_paddedChildGapPattern]

theorem paddedChildIndex_val_profile
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    (j : Fin (paddedBridgeReturnCount n (p - 1) (p + 1) center
      (directPaddedChildBridge hn hlp (by omega) source i).start.1
      (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
      (directPaddedChildBridge hn hlp (by omega) source i).bridge)) :
    (paddedChildIndex hn hlp hp1 source hparents i j : ℕ) =
      (∑ h ∈ Finset.range i,
        profileGapOffspringCount (extendStoppedWord source.bridge.1) n
          source.bridge.1.1 (center - source.start.1) p h) + j := by
  rw [paddedChildIndex_val]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro h _hh
  exact (profileGapOffspringCount_eq_paddedChildCount
    hn hlp (by omega : p ≤ n) source (Fin.castLE i.isLt.le h)).symm

theorem paddedGlobalChildClocks_eq_local
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    (j : Fin (paddedBridgeReturnCount n (p - 1) (p + 1) center
      (directPaddedChildBridge hn hlp (by omega) source i).start.1
      (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
      (directPaddedChildBridge hn hlp (by omega) source i).bridge)) :
    let omega := extendStoppedWord source.bridge.1
    let fullPath := trajectoryFrom source.start.1 omega
    let child := directPaddedChildBridge hn hlp (by omega) source i
    let childPath := trajectoryFrom child.start.1
      (extendStoppedWord child.bridge.1)
    profileInnerHitTime fullPath n source.bridge.1.1 center (p + 1)
        (paddedChildIndex hn hlp hp1 source hparents i j) =
      profileInnerHitTime fullPath n source.bridge.1.1 center p i +
        excursionFinish childPath
          (profileInnerBoundary n p center)
          (profileInnerBoundary n (p + 1) center) child.bridge.1.1 j ∧
    profileGapExitTime fullPath n source.bridge.1.1 center (p + 1)
        (paddedChildIndex hn hlp hp1 source hparents i j) =
      profileInnerHitTime fullPath n source.bridge.1.1 center p i +
        excursionStart childPath
          (profileInnerBoundary n p center)
          (profileInnerBoundary n (p + 1) center) child.bridge.1.1 (j + 1) := by
  classical
  dsimp only
  let omega := extendStoppedWord source.bridge.1
  let shiftedCenter := center - source.start.1
  let fullPath := trajectoryFrom source.start.1 omega
  let child := directPaddedChildBridge hn hlp (by omega : p ≤ n) source i
  let childPath := trajectoryFrom child.start.1
    (extendStoppedWord child.bridge.1)
  let parents := paddedBridgeReturnCount n l p center source.start.1
    source.endpoint.1 source.bridge
  have hcomplete : ∀ r < parents,
      profileGapExitTime (trajectory omega) n source.bridge.1.1
        shiftedCenter p r ≤ source.bridge.1.1 := by
    intro r hr
    rw [profileGapExitTime_translate source.start.1 center omega n
      source.bridge.1.1 p r]
    change excursionStart fullPath (profileOuterBoundary n p center)
      (profileInnerBoundary n p center) source.bridge.1.1 (r + 1) ≤
        source.bridge.1.1
    rw [show profileOuterBoundary n p center =
      profileInnerBoundary n (p - 1) center by rfl]
    exact paddedBridgeReturnComplete hn hlp (by omega : p ≤ n)
      source.bridge ⟨r, hr⟩
  have hprefixSegment := translated_scan_prefix_to_first_parent
    hn hlp (by omega : p ≤ n) source hparents
  have hfirstPrefix :
      @scanThrough (trajectory omega)
        (profileInnerBoundary n p shiftedCenter)
        (profileInnerBoundary n (p + 1) shiftedCenter)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n source.bridge.1.1
          shiftedCenter p 0) = ⟨false, 0⟩ := by
    simpa only [scanThrough] using hprefixSegment
  have hoffspring := profileGapOffspringCount_eq_paddedChildCount
    hn hlp (by omega : p ≤ n) source i
  have hjProfile : (j : ℕ) < profileGapOffspringCount omega n
      source.bridge.1.1 shiftedCenter p i := by
    rw [hoffspring]
    exact j.isLt
  have hprofile := profileChildClocks_eq_parentLocal_of_prefix
    hn (by omega : 0 < p) hp1 i.isLt hcomplete hfirstPrefix hjProfile
  dsimp only at hprofile
  have hindex := paddedChildIndex_val_profile
    hn hlp hp1 source hparents i j
  rw [← hindex] at hprofile
  have hlocal := profileGapChildClocks_eq_paddedChildBridge
    hn hlp (by omega : p ≤ n) source i (hcomplete i i.isLt) j
  dsimp only at hlocal
  have hglobalInner := profileInnerHitTime_translate source.start.1 center omega n
    source.bridge.1.1 (p + 1)
      (paddedChildIndex hn hlp hp1 source hparents i j)
  have hglobalExit := profileGapExitTime_translate source.start.1 center omega n
    source.bridge.1.1 (p + 1)
      (paddedChildIndex hn hlp hp1 source hparents i j)
  have hparentInner := profileInnerHitTime_translate source.start.1 center omega n
    source.bridge.1.1 p i
  constructor
  · calc
      profileInnerHitTime fullPath n source.bridge.1.1 center (p + 1)
          (paddedChildIndex hn hlp hp1 source hparents i j) =
        profileInnerHitTime (trajectory omega) n source.bridge.1.1
          shiftedCenter (p + 1)
            (paddedChildIndex hn hlp hp1 source hparents i j) :=
        hglobalInner.symm
      _ = profileInnerHitTime (trajectory omega) n source.bridge.1.1
            shiftedCenter p i +
          excursionFinish
            (profileGapWalk omega n source.bridge.1.1 shiftedCenter p i)
            (profileInnerBoundary n p shiftedCenter)
            (profileInnerBoundary n (p + 1) shiftedCenter)
            (profileGapLength omega n source.bridge.1.1 shiftedCenter p i) j :=
        hprofile.1
      _ = profileInnerHitTime fullPath n source.bridge.1.1 center p i +
          excursionFinish childPath
            (profileInnerBoundary n p center)
            (profileInnerBoundary n (p + 1) center) child.bridge.1.1 j := by
        rw [hparentInner, hlocal.1]
  · calc
      profileGapExitTime fullPath n source.bridge.1.1 center (p + 1)
          (paddedChildIndex hn hlp hp1 source hparents i j) =
        profileGapExitTime (trajectory omega) n source.bridge.1.1
          shiftedCenter (p + 1)
            (paddedChildIndex hn hlp hp1 source hparents i j) :=
        hglobalExit.symm
      _ = profileInnerHitTime (trajectory omega) n source.bridge.1.1
            shiftedCenter p i +
          excursionStart
            (profileGapWalk omega n source.bridge.1.1 shiftedCenter p i)
            (profileInnerBoundary n p shiftedCenter)
            (profileInnerBoundary n (p + 1) shiftedCenter)
            (profileGapLength omega n source.bridge.1.1 shiftedCenter p i)
            (j + 1) := hprofile.2
      _ = profileInnerHitTime fullPath n source.bridge.1.1 center p i +
          excursionStart childPath
            (profileInnerBoundary n p center)
            (profileInnerBoundary n (p + 1) center) child.bridge.1.1
            (j + 1) := by
        rw [hparentInner, hlocal.2]

theorem fullPath_parent_add_eq_childPath
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    {q : ℕ}
    (hq : q ≤ profileGapLength (extendStoppedWord source.bridge.1) n
      source.bridge.1.1 (center - source.start.1) p i) :
    trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
        (profileInnerHitTime
          (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
          n source.bridge.1.1 center p i + q) =
      trajectoryFrom (directPaddedChildBridge hn hlp hp source i).start.1
        (extendStoppedWord
          (directPaddedChildBridge hn hlp hp source i).bridge.1) q := by
  let omega := extendStoppedWord source.bridge.1
  let shiftedCenter := center - source.start.1
  let fullPath := trajectoryFrom source.start.1 omega
  let actual := profileGapWalk omega n source.bridge.1.1 shiftedCenter p i
  let extended := trajectoryFrom
    (profileGapStartPoint omega n source.bridge.1.1 shiftedCenter p i)
    (extendStoppedWord
      (profileGapStoppedWord omega n source.bridge.1.1 shiftedCenter p i))
  let child := directPaddedChildBridge hn hlp hp source i
  let childPath := trajectoryFrom child.start.1
    (extendStoppedWord child.bridge.1)
  have hparent := profileInnerHitTime_translate source.start.1 center omega n
    source.bridge.1.1 p i
  have hactual : actual q = trajectory omega
      (profileInnerHitTime (trajectory omega) n source.bridge.1.1
        shiftedCenter p i + q) := by
    exact profileGapWalk_eq_trajectory_add omega n source.bridge.1.1
      shiftedCenter p i q
  have hactualExtended : actual q = extended q := by
    simpa only [actual, extended] using
      (profileGapWalk_eq_extendStoppedWord_through
        (omega := omega) (n := n) (horizon := source.bridge.1.1)
        (x := shiftedCenter) (k := p) (parent := (i : ℕ)) hq)
  have hchild : source.start.1 + extended q = childPath q := by
    simpa only [omega, shiftedCenter, extended, childPath, child] using
      (profileGapExtendedPath_add_eq_childPath hn hlp hp source i q)
  calc
    fullPath (profileInnerHitTime fullPath n source.bridge.1.1 center p i + q) =
        source.start.1 + trajectory omega
          (profileInnerHitTime fullPath n source.bridge.1.1 center p i + q) := by
      simp only [fullPath, trajectoryFrom_eq_add_trajectory]
    _ = source.start.1 + trajectory omega
          (profileInnerHitTime (trajectory omega) n source.bridge.1.1
            shiftedCenter p i + q) := by rw [hparent]
    _ = source.start.1 + actual q := by rw [hactual]
    _ = source.start.1 + extended q := by rw [hactualExtended]
    _ = childPath q := hchild

theorem incrementSlice_full_parent_eq_child
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ profileGapLength (extendStoppedWord source.bridge.1) n
      source.bridge.1.1 (center - source.start.1) p i) :
    incrementSlice (extendStoppedWord source.bridge.1)
        (profileInnerHitTime
          (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
          n source.bridge.1.1 center p i + a)
        (profileInnerHitTime
          (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
          n source.bridge.1.1 center p i + b) =
      incrementSlice
        (extendStoppedWord
          (directPaddedChildBridge hn hlp hp source i).bridge.1) a b := by
  let omega := extendStoppedWord source.bridge.1
  let shiftedCenter := center - source.start.1
  have hparent := profileInnerHitTime_translate source.start.1 center omega n
    source.bridge.1.1 p i
  have hslice := incrementSlice_extend_profileGapStoppedWord
    (omega := omega) (n := n) (horizon := source.bridge.1.1)
    (x := shiftedCenter) (k := p) (parent := (i : ℕ)) hab hb
  have hword := directPaddedReturnWord_eq_profileGapStoppedWord
    hn hlp hp source i
  rw [directPaddedChildBridge_bridge_val, hword]
  change incrementSlice omega
      (profileInnerHitTime (trajectoryFrom source.start.1 omega) n
        source.bridge.1.1 center p i + a)
      (profileInnerHitTime (trajectoryFrom source.start.1 omega) n
        source.bridge.1.1 center p i + b) = _
  rw [← hparent]
  simpa only [omega, shiftedCenter] using hslice.symm

theorem directPaddedReturnDatum_paddedChildIndex_eq
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge))
    (j : Fin (paddedBridgeReturnCount n (p - 1) (p + 1) center
      (directPaddedChildBridge hn hlp (by omega) source i).start.1
      (directPaddedChildBridge hn hlp (by omega) source i).endpoint.1
      (directPaddedChildBridge hn hlp (by omega) source i).bridge)) :
    directPaddedReturnDatum hn (by omega : l + 1 < p + 1) hp1 source
        (paddedChildIndex hn hlp hp1 source hparents i j) =
      directPaddedReturnDatum hn (by omega : (p - 1) + 1 < p + 1) hp1
        (directPaddedChildBridge hn hlp (by omega) source i) j := by
  classical
  let omega := extendStoppedWord source.bridge.1
  let fullPath := trajectoryFrom source.start.1 omega
  let child := directPaddedChildBridge hn hlp (by omega : p ≤ n) source i
  let childPath := trajectoryFrom child.start.1
    (extendStoppedWord child.bridge.1)
  let localFinish := excursionFinish childPath
    (profileInnerBoundary n p center)
    (profileInnerBoundary n (p + 1) center) child.bridge.1.1 j
  let localReturn := excursionStart childPath
    (profileInnerBoundary n p center)
    (profileInnerBoundary n (p + 1) center) child.bridge.1.1 (j + 1)
  let L := profileGapLength omega n source.bridge.1.1
    (center - source.start.1) p i
  have hclocks := paddedGlobalChildClocks_eq_local
    hn hlp hp1 source hparents i j
  dsimp only at hclocks
  have hreturn : localReturn ≤ child.bridge.1.1 := by
    dsimp only [localReturn, childPath]
    exact paddedBridgeReturnComplete hn (by omega : (p - 1) + 1 < p + 1)
      hp1 child.bridge j
  have hfinish : localFinish ≤ localReturn := by
    exact excursionFinish_le_next_start childPath
      (profileInnerBoundary n p center)
      (profileInnerBoundary n (p + 1) center) child.bridge.1.1 j
  have hwordParent := directPaddedReturnWord_eq_profileGapStoppedWord
    hn hlp (by omega : p ≤ n) source i
  have hlength : child.bridge.1.1 = L := by
    change (directPaddedReturnWordCode hn hlp (by omega : p ≤ n) source i).1.1 = L
    rw [hwordParent]
    rfl
  have hreturnL : localReturn ≤ L := by omega
  have hfinishL : localFinish ≤ L := hfinish.trans hreturnL
  have hinnerPoint :
      (directPaddedReturnDatum hn (by omega : l + 1 < p + 1) hp1 source
        (paddedChildIndex hn hlp hp1 source hparents i j)).1 =
      (directPaddedReturnDatum hn (by omega : (p - 1) + 1 < p + 1) hp1
        child j).1 := by
    apply Subtype.ext
    change fullPath
        (profileInnerHitTime fullPath n source.bridge.1.1 center (p + 1)
          (paddedChildIndex hn hlp hp1 source hparents i j)) =
      childPath localFinish
    rw [hclocks.1]
    exact fullPath_parent_add_eq_childPath
      hn hlp (by omega : p ≤ n) source i hfinishL
  have hmiddlePoint :
      (directPaddedReturnDatum hn (by omega : l + 1 < p + 1) hp1 source
        (paddedChildIndex hn hlp hp1 source hparents i j)).2.1 =
      (directPaddedReturnDatum hn (by omega : (p - 1) + 1 < p + 1) hp1
        child j).2.1 := by
    apply Subtype.ext
    change fullPath
        (profileGapExitTime fullPath n source.bridge.1.1 center (p + 1)
          (paddedChildIndex hn hlp hp1 source hparents i j)) =
      childPath localReturn
    rw [hclocks.2]
    exact fullPath_parent_add_eq_childPath
      hn hlp (by omega : p ≤ n) source i hreturnL
  have hwordVal :
      (directPaddedReturnDatum hn (by omega : l + 1 < p + 1) hp1 source
        (paddedChildIndex hn hlp hp1 source hparents i j)).2.2.1 =
      (directPaddedReturnDatum hn (by omega : (p - 1) + 1 < p + 1) hp1
        child j).2.2.1 := by
    change (directPaddedReturnWordCode hn (by omega : l + 1 < p + 1)
      hp1 source (paddedChildIndex hn hlp hp1 source hparents i j)).1 =
      (directPaddedReturnWordCode hn
        (by omega : (p - 1) + 1 < p + 1) hp1 child j).1
    let globalWord := directPaddedReturnWordCode hn
      (by omega : l + 1 < p + 1) hp1 source
      (paddedChildIndex hn hlp hp1 source hparents i j)
    let localWord := directPaddedReturnWordCode hn
      (by omega : (p - 1) + 1 < p + 1) hp1 child j
    have hglobalFinish : excursionFinish fullPath
        (profileInnerBoundary n p center)
        (profileInnerBoundary n (p + 1) center) source.bridge.1.1
        (paddedChildIndex hn hlp hp1 source hparents i j) =
      profileInnerHitTime fullPath n source.bridge.1.1 center (p + 1)
        (paddedChildIndex hn hlp hp1 source hparents i j) := by
      unfold profileInnerHitTime
      rw [show profileOuterBoundary n (p + 1) center =
        profileInnerBoundary n p center by
          simp only [profileOuterBoundary, profileInnerBoundary,
            Nat.add_sub_cancel]]
    have hglobalReturn : excursionStart fullPath
        (profileInnerBoundary n p center)
        (profileInnerBoundary n (p + 1) center) source.bridge.1.1
        ((paddedChildIndex hn hlp hp1 source hparents i j : ℕ) + 1) =
      profileGapExitTime fullPath n source.bridge.1.1 center (p + 1)
        (paddedChildIndex hn hlp hp1 source hparents i j) := by
      unfold profileGapExitTime profileOuterHitTime
      rw [show profileOuterBoundary n (p + 1) center =
        profileInnerBoundary n p center by
          simp only [profileOuterBoundary, profileInnerBoundary,
            Nat.add_sub_cancel]]
    have hslice : incrementSlice omega
        (profileInnerHitTime fullPath n source.bridge.1.1 center (p + 1)
          (paddedChildIndex hn hlp hp1 source hparents i j))
        (profileGapExitTime fullPath n source.bridge.1.1 center (p + 1)
          (paddedChildIndex hn hlp hp1 source hparents i j)) =
      incrementSlice (extendStoppedWord child.bridge.1) localFinish
        localReturn := by
      rw [hclocks.1, hclocks.2]
      exact incrementSlice_full_parent_eq_child
        hn hlp (by omega : p ≤ n) source i hfinish hreturnL
    calc
      globalWord.1 = listStoppedWord (List.ofFn globalWord.1.2) :=
        (listStoppedWord_ofFn _).symm
      _ = listStoppedWord
          (incrementSlice omega
            (profileInnerHitTime fullPath n source.bridge.1.1 center (p + 1)
              (paddedChildIndex hn hlp hp1 source hparents i j))
            (profileGapExitTime fullPath n source.bridge.1.1 center (p + 1)
              (paddedChildIndex hn hlp hp1 source hparents i j))) := by
        apply congrArg listStoppedWord
        simpa only [globalWord, omega, fullPath,
          show p + 1 - 1 = p by omega, hglobalFinish, hglobalReturn] using
          (directPaddedReturnWordCode_toList hn
            (by omega : l + 1 < p + 1) hp1 source
            (paddedChildIndex hn hlp hp1 source hparents i j))
      _ = listStoppedWord
          (incrementSlice (extendStoppedWord child.bridge.1)
            localFinish localReturn) := congrArg listStoppedWord hslice
      _ = listStoppedWord (List.ofFn localWord.1.2) := by
        apply congrArg listStoppedWord
        symm
        simpa only [localWord, childPath, localFinish, localReturn,
          show p + 1 - 1 = p by omega] using
          (directPaddedReturnWordCode_toList hn
            (by omega : (p - 1) + 1 < p + 1) hp1 child j)
      _ = localWord.1 := listStoppedWord_ofFn _
  exact PaddedReturnDatum.ext hinnerPoint hmiddlePoint hwordVal

theorem List.ofFn_eq_of_cast {m n : ℕ} {X : Type*}
    (h : m = n) (f : Fin n → X) (g : Fin m → X)
    (hfg : ∀ i, f (Fin.cast h i) = g i) :
    List.ofFn f = List.ofFn g := by
  subst n
  rw [List.ofFn_inj]
  funext i
  simpa using hfg i

theorem flatten_directParsedPaddedBridgeTrees_children_eq_succ
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (hparents : 0 < paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) :
    (List.ofFn fun i : Fin (paddedBridgeReturnCount n l p center
        source.start.1 source.endpoint.1 source.bridge) ↦
      directParsedPaddedBridgeTrees hn
        (by omega : (p - 1) + 1 < p + 1) hp1
        (directPaddedChildBridge hn hlp (by omega) source i)).flatten =
      directParsedPaddedBridgeTrees hn (by omega : l + 1 < p + 1) hp1
        source := by
  let g := paddedChildGapPattern hn hlp hp1 source hparents
  let childCount := paddedBridgeReturnCount n l (p + 1) center
    source.start.1 source.endpoint.1 source.bridge
  let treeOfDatum := fun datum : PaddedReturnDatum n (p + 1) center ↦
    (parseBoundaryGap n center hn (n - (p + 1)) (p + 1)
      (by omega) (by omega) datum.1 datum.2.1 datum.2.2).tree
  let f : Fin childCount → ProfileRefinementTree := fun r ↦
    treeOfDatum (directPaddedReturnDatum hn
      (by omega : l + 1 < p + 1) hp1 source r)
  have hgroups :
      (List.ofFn fun i : Fin (paddedBridgeReturnCount n l p center
          source.start.1 source.endpoint.1 source.bridge) ↦
        directParsedPaddedBridgeTrees hn
          (by omega : (p - 1) + 1 < p + 1) hp1
          (directPaddedChildBridge hn hlp (by omega) source i)) =
      List.ofFn fun i : Fin (paddedBridgeReturnCount n l p center
          source.start.1 source.endpoint.1 source.bridge) ↦
        List.ofFn fun j : Fin (gapMultiplicity g i) ↦
          f (gapChildIndexEquiv g ⟨i, j⟩) := by
    rw [List.ofFn_inj]
    funext parent
    rw [directParsedPaddedBridgeTrees,
      AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
    have hcount : gapMultiplicity g parent =
        paddedBridgeReturnCount n (p - 1) (p + 1) center
          (directPaddedChildBridge hn hlp (by omega) source parent).start.1
          (directPaddedChildBridge hn hlp (by omega) source parent).endpoint.1
          (directPaddedChildBridge hn hlp (by omega) source parent).bridge :=
      gapMultiplicity_paddedChildGapPattern
        hn hlp hp1 source hparents parent
    apply List.ofFn_eq_of_cast hcount
    intro gapLocal
    change treeOfDatum (directPaddedReturnDatum hn
      (by omega : (p - 1) + 1 < p + 1) hp1
      (directPaddedChildBridge hn hlp (by omega) source parent)
        (Fin.cast hcount gapLocal)) =
        f (gapChildIndexEquiv g ⟨parent, gapLocal⟩)
    have hindex : gapChildIndexEquiv g ⟨parent, gapLocal⟩ =
        paddedChildIndex hn hlp hp1 source hparents parent
          (Fin.cast hcount gapLocal) := by
      apply Fin.ext
      rw [gapChildIndexEquiv_val, paddedChildIndex_val]
      simp only [g, gapMultiplicity_paddedChildGapPattern, Fin.val_cast]
    rw [hindex]
    have hdatum := directPaddedReturnDatum_paddedChildIndex_eq
      hn hlp hp1 source hparents parent (Fin.cast hcount gapLocal)
    exact congrArg treeOfDatum hdatum.symm
  calc
    (List.ofFn fun i : Fin (paddedBridgeReturnCount n l p center
        source.start.1 source.endpoint.1 source.bridge) ↦
      directParsedPaddedBridgeTrees hn
        (by omega : (p - 1) + 1 < p + 1) hp1
        (directPaddedChildBridge hn hlp (by omega) source i)).flatten =
      (List.ofFn fun i : Fin (paddedBridgeReturnCount n l p center
          source.start.1 source.endpoint.1 source.bridge) ↦
        List.ofFn fun j : Fin (gapMultiplicity g i) ↦
          f (gapChildIndexEquiv g ⟨i, j⟩)).flatten := congrArg List.flatten hgroups
    _ = List.ofFn f := flatten_parentMajor g f
    _ = directParsedPaddedBridgeTrees hn (by omega : l + 1 < p + 1) hp1
        source := by
      rw [directParsedPaddedBridgeTrees,
        AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
      rfl

theorem flatten_directParsedPaddedBridgeTrees_children_eq_succ_all
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center) :
    (List.ofFn fun i : Fin (paddedBridgeReturnCount n l p center
        source.start.1 source.endpoint.1 source.bridge) ↦
      directParsedPaddedBridgeTrees hn
        (by omega : (p - 1) + 1 < p + 1) hp1
        (directPaddedChildBridge hn hlp (by omega) source i)).flatten =
      directParsedPaddedBridgeTrees hn (by omega : l + 1 < p + 1) hp1
        source := by
  by_cases hparents : 0 < paddedBridgeReturnCount n l p center
      source.start.1 source.endpoint.1 source.bridge
  · exact flatten_directParsedPaddedBridgeTrees_children_eq_succ
      hn hlp hp1 source hparents
  · have hparentZero : paddedBridgeReturnCount n l p center
        source.start.1 source.endpoint.1 source.bridge = 0 :=
      Nat.eq_zero_of_not_pos hparents
    have hchildZero : paddedBridgeReturnCount n l (p + 1) center
        source.start.1 source.endpoint.1 source.bridge = 0 := by
      by_contra hne
      have hchildPos : 0 < paddedBridgeReturnCount n l (p + 1) center
          source.start.1 source.endpoint.1 source.bridge := Nat.pos_of_ne_zero hne
      exact hparents
        (paddedBridgeReturnCount_pos_of_succ_pos hn hlp hp1 source hchildPos)
    simp only [hparentZero, List.ofFn_zero, List.flatten_nil]
    rw [directParsedPaddedBridgeTrees,
      AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
    symm
    apply List.eq_nil_of_length_eq_zero
    simpa only [List.length_ofFn] using hchildZero

theorem listStoppedWord_incrementSlice_extend_full (word : StoppedWord) :
    AlternatingConcatPrefixFree.listStoppedWord
        (TerminalSkeletonWords.incrementSlice
          (extendStoppedWord word) 0 word.1) = word := by
  calc
    AlternatingConcatPrefixFree.listStoppedWord
        (TerminalSkeletonWords.incrementSlice
          (extendStoppedWord word) 0 word.1) =
        AlternatingConcatPrefixFree.listStoppedWord
          (List.ofFn word.2) := by
      congr 1
      apply List.ext_get
      · simp [TerminalSkeletonWords.incrementSlice_length]
      · intro j hj hj'
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp [TerminalSkeletonWords.incrementSlice, extendStoppedWord]
    _ = word := AlternatingConcatPrefixFree.listStoppedWord_ofFn word

theorem listStoppedWord_incrementSlice_extend_from_eq_zero
    (word : StoppedWord) (t : ℕ) (ht : t = 0) :
    AlternatingConcatPrefixFree.listStoppedWord
        (TerminalSkeletonWords.incrementSlice
          (extendStoppedWord word) t word.1) = word := by
  subst t
  exact listStoppedWord_incrementSlice_extend_full word

theorem listStoppedWord_incrementSlice_extend_zero_to_eq_zero
    (word : StoppedWord) (t : ℕ) (ht : t = 0) :
    AlternatingConcatPrefixFree.listStoppedWord
        (TerminalSkeletonWords.incrementSlice
          (extendStoppedWord word) 0 t) = ⟨0, ![]⟩ := by
  subst t
  apply Sigma.ext (by simp [TerminalSkeletonWords.incrementSlice_length])
  apply (Fin.heq_fun_iff (by
    simp [TerminalSkeletonWords.incrementSlice_length])).2
  intro i
  exact Fin.elim0 i

theorem incrementSliceBoundaryExitWordCode_full_val
    {boundary : Set Point} {start endpoint : Point}
    (bridge : BoundaryExitWordCode boundary start endpoint)
    (hbegin : 0 ≤ bridge.1.1)
    (hend : PlanarPotential.trajectoryFrom start
      (extendStoppedWord bridge.1) bridge.1.1 ∈ boundary)
    (havoid : ∀ r, 0 ≤ r → r < bridge.1.1 →
      PlanarPotential.trajectoryFrom start
        (extendStoppedWord bridge.1) r ∉ boundary) :
    (AsymmetricSplitLevelSplice.incrementSliceBoundaryExitWordCode start
      (extendStoppedWord bridge.1) boundary
      hbegin hend havoid).1 = bridge.1 := by
  exact listStoppedWord_incrementSlice_extend_full bridge.1

theorem sigmaBoundaryExcursionCode_eq_of_val_eq
    {outer middle inner : Set Point} {start exit : Point} {q r : ℕ}
    (hqr : q = r)
    (left : BoundaryExcursionExitWordCode outer middle inner start q exit)
    (right : BoundaryExcursionExitWordCode outer middle inner start r exit)
    (hval : left.1 = right.1) :
    (⟨q, left⟩ : Σ s, BoundaryExcursionExitWordCode
      outer middle inner start s exit) = ⟨r, right⟩ := by
  apply Sigma.ext hqr
  apply (Subtype.heq_iff_coe_eq (fun stopped ↦ by
    constructor
    · rintro ⟨hfirst, hcount, hend⟩
      exact ⟨hfirst, hcount.trans hqr, hend⟩
    · rintro ⟨hfirst, hcount, hend⟩
      exact ⟨hfirst, hcount.trans hqr.symm, hend⟩)).2
  exact hval

theorem flatMap_profileRefinementTreeFrontier_zero
    (trees : List ProfileRefinementTree) :
    trees.flatMap (profileRefinementTreeFrontier 0) = trees := by
  induction trees with
  | nil => rfl
  | cons tree trees ih =>
      simp only [List.flatMap_cons, profileRefinementTreeFrontier,
        List.singleton_append, ih]

theorem split_adjacent_eval
    {n l : ℕ} {center : Point}
    (source : PaddedCoarseBridge n l center)
    (ht0 : paddedPreludeHitTime n l (l + 2) center source.start.1
      source.endpoint.1 source.bridge = 0)
    (hnotOuter : source.start.1 ∉ profileInnerBoundary n l center) :
    ∃ (first : BoundaryExitWordCode
          (profileInnerBoundary n (l + 1) center ∪
            profileInnerBoundary n l center) source.start.1 source.start.1)
        (q : ℕ)
        (parent : BoundaryExcursionExitWordCode
          (profileInnerBoundary n l center)
          (profileInnerBoundary n (l + 1) center)
          (profileInnerBoundary n (l + 2) center)
          source.start.1 q source.endpoint.1)
        (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
          List.ofFn source.bridge.1.2),
      paddedPreludeSplit (p := l + 2) source.start source.endpoint
          source.bridge = .entered source.start first q parent word_eq ∧
        parent.1 = source.bridge.1 := by
  unfold paddedPreludeSplit
  simp only [Nat.add_one_sub_one, Lean.Elab.WF.paramLet, exists_and_right, Subtype.exists, exists_eq_right,
    List.append_left_eq_self, List.ofFn_eq_nil_iff, Sigma.exists]
  constructor
  · refine ⟨?_, ?_⟩
    · constructor
      · exact Or.inl (by
          simpa only [PlanarPotential.trajectoryFrom_zero,
            profileInnerBoundary] using
            (mem_discBoundaryFinset.mp source.start.2))
      · intro r hr
        omega
    · apply (Subtype.heq_iff_coe_eq (fun stopped ↦ by
        simp only [ht0, PlanarPotential.trajectoryFrom_zero])).2
      simp only [AsymmetricSplitLevelSplice.incrementSliceBoundaryExitWordCode,
        TerminalVisitSpliceInvariance.stoppedWordOfList]
      exact listStoppedWord_incrementSlice_extend_zero_to_eq_zero
        source.bridge.1 _ ht0
  · refine ⟨?_, ?_⟩
    · refine ⟨source.bridge.2.1, ?_, source.bridge.2.2⟩
      simp only [AsymmetricSplitLevelSplice.incrementSliceBoundaryExitWordCode,
        TerminalVisitSpliceInvariance.stoppedWordOfList]
      have htail := listStoppedWord_incrementSlice_extend_from_eq_zero
        source.bridge.1 _ ht0
      exact congrArg (fun word : StoppedWord ↦
        boundaryExcursionCount
          (profileInnerBoundary n (l + 1) center)
          (profileInnerBoundary n (l + 2) center) source.start.1
          (extendStoppedWord word) word.1) htail.symm
    ·
      apply (Subtype.heq_iff_coe_eq (fun stopped ↦ by
        have htail := listStoppedWord_incrementSlice_extend_from_eq_zero
          source.bridge.1 _ ht0
        simp only [ht0, PlanarPotential.trajectoryFrom_zero])).2
      exact listStoppedWord_incrementSlice_extend_from_eq_zero
        source.bridge.1 _ ht0

theorem base
    {n l : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < l + 2) (hp : l + 2 ≤ n)
    (source : PaddedCoarseBridge n l center) :
    (parsedPaddedBridgeDecoration hn hlp hp source).1 =
      profileRefinementTreeFrontier 1
        (parseBoundaryGap n center hn (n - (l + 1)) (l + 1) (by omega)
          (by omega) source.start source.endpoint source.bridge).tree := by
  have hstart : source.start.1 ∈
      profileInnerBoundary n (l + 1) center := by
    exact mem_discBoundaryFinset.mp source.start.2
  have ht0 : paddedPreludeHitTime n l (l + 2) center source.start.1
      source.endpoint.1 source.bridge = 0 := by
    have hle := firstHitThrough_le_of_mem
      (s := trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
      (A := profileInnerBoundary n (l + 2 - 1) center ∪
        profileInnerBoundary n l center)
      (start := 0) (horizon := source.bridge.1.1) (q := 0)
      (by omega) (by omega) (Or.inl (by simpa using hstart))
    change firstHitThrough _ _ 0 source.bridge.1.1 = 0
    omega
  have hnotOuter : source.start.1 ∉ profileInnerBoundary n l center := by
    intro houter
    exact Set.disjoint_left.mp
      (AnnularOffspringScan.adjacent_profileInnerBoundaries_disjoint
        (by omega : 1 ≤ n)
        (by omega : l + 1 ≤ n) center) houter hstart
  change parsedPaddedBridgeTrees hn hlp hp source = _
  unfold parsedPaddedBridgeTrees
  rcases split_adjacent_eval source ht0 hnotOuter with
    ⟨first, q, parent, word_eq, hsplit, hparent⟩
  rw [hsplit]
  simp only
  let q0 := boundaryExcursionCount
    (profileInnerBoundary n (l + 1) center)
    (profileInnerBoundary n (l + 2) center) source.start.1
    (extendStoppedWord source.bridge.1) source.bridge.1.1
  let parent0 : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (l + 1) center)
      (profileInnerBoundary n (l + 2) center)
      source.start.1 q0 source.endpoint.1 :=
    ⟨source.bridge.1, source.bridge.2.1, rfl, source.bridge.2.2⟩
  have hq : q = q0 := by
    calc
      q = boundaryExcursionCount
          (profileInnerBoundary n (l + 1) center)
          (profileInnerBoundary n (l + 2) center) source.start.1
          (extendStoppedWord parent.1) parent.1.1 := parent.2.2.1.symm
      _ = q0 := by simp only [hparent, q0]
  have hpack :
      (⟨q, parent⟩ : Σ s, BoundaryExcursionExitWordCode
        (profileInnerBoundary n l center)
        (profileInnerBoundary n (l + 1) center)
        (profileInnerBoundary n (l + 2) center)
      source.start.1 s source.endpoint.1) = ⟨q0, parent0⟩ :=
    sigmaBoundaryExcursionCode_eq_of_val_eq hq parent parent0 hparent
  let paddedTrees := fun pack : Σ s, BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (l + 1) center)
      (profileInnerBoundary n (l + 2) center)
      source.start.1 s source.endpoint.1 ↦
    AsymmetricPaddedCodeAssembly.finTreeList pack.1 fun j ↦
      (parseBoundaryGap n center hn (n - (l + 2)) (l + 2)
        (by omega) (by omega)
        (AsymmetricPaddedActiveFactorization.extractedPaddedInnerPoint
          source.start source.endpoint pack.2 j)
        (AsymmetricPaddedActiveFactorization.extractedPaddedMiddlePoint
          hn hlp hp source.start source.endpoint pack.2 j.succ)
        (AsymmetricPaddedActiveFactorization.extractedPaddedReturnWordCode
          hn hlp hp source.start source.endpoint pack.2 j)).tree
  have htransport := congrArg paddedTrees hpack
  change paddedTrees ⟨q, parent⟩ = _
  rw [htransport]
  simp only [paddedTrees]
  have hdepth : n - (l + 1) = (n - (l + 2)) + 1 := by omega
  have hroot :
      (parseBoundaryGap n center hn (n - (l + 1)) (l + 1) (by omega)
        (by omega) source.start source.endpoint source.bridge).tree =
      (parseBoundaryGap n center hn ((n - (l + 2)) + 1) (l + 1) (by omega)
        (by omega) source.start source.endpoint source.bridge).tree := by
    simp only [hdepth]
  rw [hroot]
  simp only [parseBoundaryGap,
    AnnularRecursiveProfileActualCode.parsedProfileGapOfBoundaryExcursion,
    profileRefinementTreeFrontier,
    AnnularRecursiveProfileActualCode.profileRefinementForestOfFin_eq_ofList_ofFn,
    profileRefinementForestFrontier_ofList]
  rw [AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
  rw [flatMap_profileRefinementTreeFrontier_zero]
  have hparent0 : parent0 =
      boundaryExitWordAsExcursionCode source.start source.endpoint
        source.bridge := by
    rfl
  rw [hparent0]
  apply congrArg List.ofFn
  funext j
  rfl

theorem directParsedPaddedChildBridge_eq_frontier_one
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center)
    (i : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    directParsedPaddedBridgeTrees hn
        (by omega : (p - 1) + 1 < p + 1) hp1
        (directPaddedChildBridge hn hlp (by omega) source i) =
      profileRefinementTreeFrontier 1
        (parseBoundaryGap n center hn (n - p) p (by omega) (by omega)
          (directPaddedInnerPoint hn hlp (by omega) source i)
          (directPaddedMiddlePoint hn hlp (by omega) source i)
          (directPaddedReturnWordCode hn hlp (by omega) source i)).tree := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  let child := directPaddedChildBridge hn hlp (by omega : r + 1 ≤ n) source i
  calc
    directParsedPaddedBridgeTrees hn
        (by omega : r + 1 < (r + 1) + 1) hp1 child =
      parsedPaddedBridgeTrees hn
        (by omega : r + 1 < (r + 1) + 1) hp1 child :=
      (parsedPaddedBridgeTrees_eq_direct hn (by omega) hp1 child).symm
    _ = (parsedPaddedBridgeDecoration hn
        (by omega : r + 1 < (r + 1) + 1) hp1 child).1 := rfl
    _ = profileRefinementTreeFrontier 1
        (parseBoundaryGap n center hn (n - (r + 1)) (r + 1)
          (by omega) (by omega)
          (directPaddedInnerPoint hn hlp (by omega) source i)
          (directPaddedMiddlePoint hn hlp (by omega) source i)
          (directPaddedReturnWordCode hn hlp (by omega) source i)).tree := by
      have hstart : child.start =
          directPaddedInnerPoint hn hlp (by omega) source i := by
        apply Subtype.ext
        rfl
      have hendpoint : child.endpoint =
          directPaddedMiddlePoint hn hlp (by omega) source i := by
        rfl
      have hbridge : child.bridge =
          directPaddedReturnWordCode hn hlp (by omega) source i := by
        apply Subtype.ext
        rfl
      have hbase := base (n := n) (l := r) (center := center)
        hn (by omega) (by omega) child
      cases hstart
      cases hendpoint
      cases hbridge
      exact hbase

theorem directParsedPaddedBridgeTrees_succ_eq_flatMap_frontier_one
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp1 : p + 1 ≤ n)
    (source : PaddedCoarseBridge n l center) :
    directParsedPaddedBridgeTrees hn (by omega : l + 1 < p + 1) hp1
        source =
      (directParsedPaddedBridgeTrees hn hlp (by omega : p ≤ n) source).flatMap
        (profileRefinementTreeFrontier 1) := by
  rw [← flatten_directParsedPaddedBridgeTrees_children_eq_succ_all
    hn hlp hp1 source]
  rw [directParsedPaddedBridgeTrees,
    AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  rw [List.ofFn_inj]
  funext i
  exact directParsedPaddedChildBridge_eq_frontier_one
    hn hlp hp1 source i

mutual
  theorem flatMap_profileRefinementTreeFrontier_one :
      ∀ (depth : ℕ) (tree : ProfileRefinementTree),
        (profileRefinementTreeFrontier depth tree).flatMap
            (profileRefinementTreeFrontier 1) =
          profileRefinementTreeFrontier (depth + 1) tree
    | 0, tree => by
        simp only [profileRefinementTreeFrontier, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
    | depth + 1, .leaf => rfl
    | depth + 1, .node forest =>
        flatMap_profileRefinementForestFrontier_one depth forest

  theorem flatMap_profileRefinementForestFrontier_one :
      ∀ (depth : ℕ) (forest : ProfileRefinementForest),
        (profileRefinementForestFrontier depth forest).flatMap
            (profileRefinementTreeFrontier 1) =
          profileRefinementForestFrontier (depth + 1) forest
    | _depth, .nil => rfl
    | depth, .cons child tail => by
        simp only [profileRefinementForestFrontier, List.flatMap_append]
        rw [flatMap_profileRefinementTreeFrontier_one,
          flatMap_profileRefinementForestFrontier_one]
end

theorem parsedPaddedBridgeTrees_add_eq_frontier
    {n l d : ℕ} {center : Point}
    (hn : 2 ≤ n) (hp : l + 2 + d ≤ n)
    (source : PaddedCoarseBridge n l center) :
    parsedPaddedBridgeTrees hn (by omega : l + 1 < l + 2 + d) hp source =
      profileRefinementTreeFrontier (d + 1)
        (parseBoundaryGap n center hn (n - (l + 1)) (l + 1)
          (by omega) (by omega) source.start source.endpoint
          source.bridge).tree := by
  revert hp source
  induction d with
  | zero =>
      intro hp source
      change (parsedPaddedBridgeDecoration hn
        (by omega : l + 1 < l + 2) hp source).1 = _
      simpa only [Nat.add_zero] using
        (base (n := n) (l := l) (center := center)
          hn (by omega) hp source)
  | succ d ih =>
      intro hp source
      let p := l + 2 + d
      have hp0 : p ≤ n := by omega
      have hlp0 : l + 1 < p := by omega
      have ih0 := ih hp0 source
      calc
        parsedPaddedBridgeTrees hn
            (by omega : l + 1 < l + 2 + (d + 1)) hp source =
          directParsedPaddedBridgeTrees hn
            (by omega : l + 1 < p + 1) hp source :=
          parsedPaddedBridgeTrees_eq_direct hn (by omega) hp source
        _ = (directParsedPaddedBridgeTrees hn hlp0 hp0 source).flatMap
              (profileRefinementTreeFrontier 1) :=
          directParsedPaddedBridgeTrees_succ_eq_flatMap_frontier_one
            hn hlp0 hp source
        _ = (parsedPaddedBridgeTrees hn hlp0 hp0 source).flatMap
              (profileRefinementTreeFrontier 1) := by
          exact congrArg
            (fun trees : List ProfileRefinementTree ↦
              trees.flatMap (profileRefinementTreeFrontier 1))
            (parsedPaddedBridgeTrees_eq_direct hn hlp0 hp0 source).symm
        _ = (profileRefinementTreeFrontier (d + 1)
              (parseBoundaryGap n center hn (n - (l + 1)) (l + 1)
                (by omega) (by omega) source.start source.endpoint
                source.bridge).tree).flatMap
              (profileRefinementTreeFrontier 1) := by
          exact congrArg
            (fun trees : List ProfileRefinementTree ↦
              trees.flatMap (profileRefinementTreeFrontier 1)) ih0
        _ = profileRefinementTreeFrontier ((d + 1) + 1)
              (parseBoundaryGap n center hn (n - (l + 1)) (l + 1)
                (by omega) (by omega) source.start source.endpoint
                source.bridge).tree :=
          flatMap_profileRefinementTreeFrontier_one _ _

theorem parsedPaddedBridgeTrees_eq_frontier
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) :
    parsedPaddedBridgeTrees hn hlp hp source =
      profileRefinementTreeFrontier (p - (l + 1))
        (parseBoundaryGap n center hn (n - (l + 1)) (l + 1)
          (by omega) (by omega) source.start source.endpoint
          source.bridge).tree := by
  have hl2p : l + 2 ≤ p := by omega
  obtain ⟨d, rfl⟩ : ∃ d, p = l + 2 + d := by
    exact ⟨p - (l + 2), by omega⟩
  have hdepth : l + 2 + d - (l + 1) = d + 1 := by omega
  simpa only [hdepth] using
    (parsedPaddedBridgeTrees_add_eq_frontier
      (n := n) (l := l) (d := d) (center := center) hn hp source)

end
end Erdos1165.AsymmetricPaddedBridgeFrontier

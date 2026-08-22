/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularOffspringScan
import ErdosProblems.Erdos1165.AnnularSpatialSplice
import ErdosProblems.Erdos1165.AnnularProfileNestedEdge
import ErdosProblems.Erdos1165.TerminalProfileBoundarySeparation

/-!
# Chronological partition of profile offspring

The child excursions at two adjacent annular scales are partitioned by the
chronological parent gaps.  This file first records the purely finite scanner
algebra.  The geometric specialization below uses the literal first-hit
clocks; no probabilistic or kernel premise is involved.
-/

open Set
open scoped BigOperators

namespace Erdos1165.AnnularProfileOffspringPartition

open ThickPoint TerminalExcursionPathwise TerminalBoundaryScan
open TerminalGlobalExitSplice TerminalSequentialVisitLaw
open AnnularProfileClocks AnnularProfileGapAtoms AnnularProfileLevelSkeleton
open AnnularOffspringScan
open AnnularProfileNestedEdge PathInsertion
open PotentialEuclideanGeometry TerminalSpliceProfileGeometry
open TerminalProfileBoundarySeparation

noncomputable section

/-- A scanner state whose completed counter is translated by `c`. -/
private theorem addCompleted_false (c q : ℕ) :
    addCompleted c ⟨false, q⟩ = ⟨false, c + q⟩ := by
  rfl

/-- Concatenating finitely many disjoint active intervals, separated by
scanner-inert pieces, adds their completed-excursion counters.  The initial
piece includes the first active starting point; every active interval and
later retained piece starts at the next time coordinate. -/
theorem scanThrough_eq_sum_of_interval_scans
    {s : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {horizon parents : ℕ} (hparents : 0 < parents)
    (entrance exit count : ℕ → ℕ)
    (hentranceExit : ∀ i < parents, entrance i ≤ exit i)
    (hexitEntrance : ∀ i, i + 1 < parents →
      exit i ≤ entrance (i + 1))
    (hlast : exit (parents - 1) ≤ horizon)
    (hprefix : scanSegment s outer inner 0 (entrance 0 + 1) initialState =
      ⟨false, 0⟩)
    (hactive : ∀ i < parents, ∀ c,
      scanSegment s outer inner (entrance i + 1)
          (exit i - entrance i) ⟨false, c⟩ =
        ⟨false, c + count i⟩)
    (hinert : ∀ i, i + 1 < parents → ∀ c,
      scanSegment s outer inner (exit i + 1)
          (entrance (i + 1) - exit i) ⟨false, c⟩ =
        ⟨false, c⟩)
    (hsuffix : ∀ c,
      scanSegment s outer inner (exit (parents - 1) + 1)
          (horizon - exit (parents - 1)) ⟨false, c⟩ =
        ⟨false, c⟩) :
    scanThrough s outer inner horizon =
      ⟨false, ∑ i ∈ Finset.range parents, count i⟩ := by
  have hthroughExit : ∀ j, j < parents →
      scanSegment s outer inner 0 (exit j + 1) initialState =
        ⟨false, ∑ i ∈ Finset.range (j + 1), count i⟩ := by
    intro j hj
    induction j with
    | zero =>
        rw [show exit 0 + 1 = (entrance 0 + 1) +
            (exit 0 - entrance 0) by
          have := hentranceExit 0 hj
          omega,
          scanSegment_add, hprefix]
        simp only [Nat.zero_add]
        rw [hactive 0 hj 0]
        simp
    | succ j ih =>
        have hjParent : j < parents := by omega
        have hjNext : j + 1 < parents := hj
        rw [show exit (j + 1) + 1 =
            (exit j + 1) +
              (entrance (j + 1) - exit j) +
              (exit (j + 1) - entrance (j + 1)) by
          have hbetween := hexitEntrance j hjNext
          have hnext := hentranceExit (j + 1) hj
          omega,
          scanSegment_add, scanSegment_add, ih hjParent]
        simp only [Nat.zero_add]
        rw [hinert j hjNext]
        rw [show exit j + 1 + (entrance (j + 1) - exit j) =
            entrance (j + 1) + 1 by
          have := hexitEntrance j hjNext
          omega,
          hactive (j + 1) hj]
        simp only [Finset.sum_range_succ]
  have hlastIndex : parents - 1 < parents := by omega
  rw [scanThrough, show horizon + 1 =
      (exit (parents - 1) + 1) + (horizon - exit (parents - 1)) by omega,
    scanSegment_add, hthroughExit (parents - 1) hlastIndex]
  simp only [Nat.zero_add]
  rw [show parents - 1 + 1 = parents by omega, hsuffix]

/-- A nearest-neighbour path starting outside a disc and ending inside it
hits the literal inner vertex boundary in between. -/
theorem exists_discBoundary_between
    {s : WalkPath} (hstep : ∀ q, Adjacent (s q) (s (q + 1)))
    {center : Point} {radius : ℝ} {start stop : ℕ}
    (hstartStop : start ≤ stop) (hstart : s start ∉ disc center radius)
    (hstop : s stop ∈ disc center radius) :
    ∃ q, start ≤ q ∧ q ≤ stop ∧
      s q ∈ discBoundary center radius := by
  classical
  let P : ℕ → Prop := fun r ↦ s (start + r) ∈ disc center radius
  have hP : ∃ r, P r := ⟨stop - start, by
    dsimp only [P]
    rwa [Nat.add_sub_of_le hstartStop]⟩
  let r := Nat.find hP
  have hrMem : s (start + r) ∈ disc center radius := Nat.find_spec hP
  have hrLe : r ≤ stop - start := Nat.find_min' hP (by
    dsimp only [P]
    rwa [Nat.add_sub_of_le hstartStop])
  have hrPos : 0 < r := by
    by_contra hnot
    have hrZero : r = 0 := by omega
    rw [hrZero] at hrMem
    exact hstart (by simpa using hrMem)
  let previous := r - 1
  have hpreviousLt : previous < r := by dsimp only [previous]; omega
  have hpreviousOut : s (start + previous) ∉ disc center radius := by
    intro hmem
    exact (Nat.not_le_of_gt hpreviousLt)
      (Nat.find_min' hP (by simpa [P] using hmem))
  have hsucc : start + previous + 1 = start + r := by
    dsimp only [previous]
    omega
  refine ⟨start + r, by omega, by omega, hrMem,
    s (start + previous), hpreviousOut, ?_⟩
  rw [← hsucc]
  unfold Adjacent at hstep ⊢
  rw [show (s (start + previous + 1)).1 - (s (start + previous)).1 =
        -((s (start + previous)).1 - (s (start + previous + 1)).1) by ring,
      show (s (start + previous + 1)).2 - (s (start + previous)).2 =
        -((s (start + previous)).2 - (s (start + previous + 1)).2) by ring,
      Int.natAbs_neg, Int.natAbs_neg]
  exact hstep (start + previous)

/-- Every candidate centre is far enough from the origin that the origin is
outside every regular profile disc. -/
theorem zero_outside_candidate_profileDisc
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) {x : Point}
    (hx : x ∈ candidateBox n) :
    (0 : Point) ∉ disc x (scaleRadius n k) := by
  intro hmem
  have hdistance : euclideanRadius (-x) ≤ scaleRadius n k := by
    change latticeDistance x 0 ≤ scaleRadius n k at hmem
    rw [TerminalSpliceProfileGeometry.latticeDistance_eq_euclideanRadius_sub]
      at hmem
    simpa using hmem
  have hgeom := AnnularSpatialSplice.candidate_neg_euclideanRadius_bounds hx
  have hrk0 : scaleRadius n k ≤ scaleRadius n 0 :=
    scaleRadius_antitone_of_le (Nat.zero_le k) hk
  have hr0pos : 0 < scaleRadius n 0 := by
    have hnRadius : (n : ℝ) ≤ scaleRadius n 1 :=
      AnnularSpatialSplice.natCast_le_scaleRadius_one n (by omega)
    have hr10 : scaleRadius n 1 ≤ scaleRadius n 0 :=
      scaleRadius_antitone_of_le (by omega) (by omega)
    have hnpos : (0 : ℝ) < n := by positivity
    linarith
  nlinarith

/-- A literal hit bounds the finite first-hit clock. -/
theorem firstHitThrough_le_of_mem
    {s : WalkPath} {A : Set Point} [DecidablePred (· ∈ A)]
    {start horizon q : ℕ} (hstart : start ≤ q) (hqH : q ≤ horizon)
    (hq : s q ∈ A) :
    firstHitThrough s A start horizon ≤ q := by
  have hqFin : q ∈ hitTimesThrough s A start horizon :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hstart, hqH⟩, hq⟩
  have hne : (hitTimesThrough s A start horizon).Nonempty := ⟨q, hqFin⟩
  simp only [firstHitThrough, dif_pos hne]
  exact Finset.min'_le _ q hqFin

/-- Before the first completed parent entrance, the global walk has not yet
visited the parent inner boundary. -/
theorem avoids_profileInnerBoundary_before_first_parent
    {omega : StepPath} {n horizon k : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k ≤ n)
    (hx : x ∈ candidateBox n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k 0 ≤
      horizon) :
    ∀ q, q < profileInnerHitTime (trajectory omega) n horizon x k 0 →
      trajectory omega q ∉ profileInnerBoundary n k x := by
  classical
  intro q hqt hqBoundary
  have htH : profileInnerHitTime (trajectory omega) n horizon x k 0 ≤
      horizon :=
    (profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k 0).trans hcomplete
  have hqH : q ≤ horizon := by omega
  have hqDisc : trajectory omega q ∈ disc x (scaleRadius n k) :=
    hqBoundary.1
  obtain ⟨e, he0, heq, heBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    (Nat.zero_le q) (zero_outside_candidate_profileDisc hn hk hx) hqDisc
  have heH : e ≤ horizon := heq.trans hqH
  have heOuterDisc : trajectory omega e ∈ disc x (scaleRadius n (k - 1)) :=
    heBoundary.1.trans
      (scaleRadius_antitone_of_le (by omega : k - 1 ≤ k) hk)
  obtain ⟨d, hd0, hde, hdBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    (Nat.zero_le e)
    (zero_outside_candidate_profileDisc hn (by omega : k - 1 ≤ n) hx)
    heOuterDisc
  have hdH : d ≤ horizon := hde.trans heH
  have haD : profileOuterHitTime (trajectory omega) n horizon x k 0 ≤ d := by
    unfold profileOuterHitTime excursionStart
    simpa only [Function.iterate_zero, id_eq] using
      firstHitThrough_le_of_mem (s := trajectory omega)
        (A := profileOuterBoundary n k x) (start := 0) (horizon := horizon)
        (q := d) (Nat.zero_le d) hdH (by
          simpa [profileOuterBoundary] using hdBoundary)
  have htE : profileInnerHitTime (trajectory omega) n horizon x k 0 ≤ e := by
    unfold profileInnerHitTime
    exact firstHitThrough_le_of_mem (haD.trans hde) heH (by
      simpa [profileInnerBoundary] using heBoundary)
  omega

/-- The initial global prefix through the first parent-inner hit has exactly
the canonical seeking-child state with zero completed children. -/
theorem scan_prefix_to_first_parent
    {omega : StepPath} {n horizon k : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k 0 ≤
      horizon) :
    @scanSegment (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        0 (profileInnerHitTime (trajectory omega) n horizon x k 0 + 1)
        initialState = ⟨false, 0⟩ := by
  classical
  let t := profileInnerHitTime (trajectory omega) n horizon x k 0
  have htH : t ≤ horizon :=
    (profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k 0).trans hcomplete
  have htMem : trajectory omega t ∈ profileInnerBoundary n k x :=
    profileInnerHit_mem_of_le htH
  have hfirst : ∀ q, q < t →
      trajectory omega (0 + q) ∉ profileInnerBoundary n k x := by
    intro q hq
    simpa only [Nat.zero_add] using
      avoids_profileInnerBoundary_before_first_parent hn hk0 (by omega) hx
        hcomplete q hq
  simpa only [t, initialState, Nat.zero_add] using
    scanSegment_firstOuter (trajectory omega)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      0 t 0 hfirst (by simpa only [Nat.zero_add] using htMem)

/-- One actual parent gap translates the child scanner counter by its
literal offspring count. -/
theorem scan_profileGap_add_offspring
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) (c : ℕ) :
    @scanSegment (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileInnerHitTime (trajectory omega) n horizon x k parent + 1)
        (profileGapExitTime (trajectory omega) n horizon x k parent -
          profileInnerHitTime (trajectory omega) n horizon x k parent)
        ⟨false, c⟩ =
      ⟨false, c + profileGapOffspringCount omega n horizon x k parent⟩ := by
  classical
  let t := profileInnerHitTime (trajectory omega) n horizon x k parent
  let u := profileGapExitTime (trajectory omega) n horizon x k parent
  let L := profileGapLength omega n horizon x k parent
  let gapWalk := profileGapWalk omega n horizon x k parent
  let outer := profileInnerBoundary n k x
  let inner := profileInnerBoundary n (k + 1) x
  let offspring := profileGapOffspringCount omega n horizon x k parent
  have htu : t ≤ u :=
    profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k parent
  have hL : L = u - t := rfl
  have htH : t ≤ horizon := htu.trans hcomplete
  have htMem : gapWalk 0 ∈ outer := by
    simpa only [gapWalk, profileGapWalk, PlanarPotential.trajectoryFrom_zero,
      outer] using
      (profileGapStartPoint_mem_innerBoundary hcomplete)
  have hzero : scanSegment gapWalk outer inner 0 1 initialState =
      ⟨false, 0⟩ := by
    simp [scanSegment_succ, scanSegment_zero, initialState, visit, htMem]
  have hlocalZero : scanSegment gapWalk outer inner 1 L ⟨false, 0⟩ =
      ⟨false, offspring⟩ := by
    have hscan := scanThrough_profileGap_eq_offspringCount
      (omega := omega) (n := n) (horizon := horizon) (x := x)
      (k := k) (parent := parent) (by omega) hk0 hk hcomplete
    change scanThrough gapWalk outer inner L = ⟨false, offspring⟩ at hscan
    rw [scanThrough, show L + 1 = 1 + L by omega,
      scanSegment_add, hzero] at hscan
    exact hscan
  have hlocal : scanSegment gapWalk outer inner 1 L ⟨false, c⟩ =
      ⟨false, c + offspring⟩ := by
    have htranslated := scanSegment_addCompleted gapWalk outer inner 1 L c
      ⟨false, 0⟩
    rw [hlocalZero] at htranslated
    simpa [addCompleted] using htranslated
  have hpath : ∀ q, q < L →
      trajectory omega ((t + 1) + q) = gapWalk (1 + q) := by
    intro q hq
    unfold gapWalk profileGapWalk profileGapStartPoint profileGapFreshPath
    rw [trajectoryFrom_shiftSteps_eq]
    apply congrArg (trajectory omega)
    dsimp only [t]
    omega
  change scanSegment (trajectory omega) outer inner (t + 1) (u - t)
      ⟨false, c⟩ = ⟨false, c + offspring⟩
  rw [← hL]
  rw [scanSegment_congr (trajectory omega) gapWalk outer inner hpath]
  exact hlocal

/-- Between the end of one parent gap and the next parent entrance, the walk
does not visit the child inner boundary. -/
theorem avoids_childBoundary_between_parent_gaps
    {omega : StepPath} {n horizon k parents parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparent : parent + 1 < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon) :
    ∀ q,
      profileGapExitTime (trajectory omega) n horizon x k parent < q →
      q ≤ profileInnerHitTime (trajectory omega) n horizon x k (parent + 1) →
      trajectory omega q ∉ profileInnerBoundary n (k + 1) x := by
  classical
  let u := profileGapExitTime (trajectory omega) n horizon x k parent
  let t := profileInnerHitTime (trajectory omega) n horizon x k (parent + 1)
  have hnextComplete := hcomplete (parent + 1) hparent
  have htH : t ≤ horizon :=
    (profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k (parent + 1)).trans hnextComplete
  have huBoundary : trajectory omega u ∈ profileOuterBoundary n k x :=
    profileGapExit_mem_outerBoundary (hcomplete parent (by omega))
  have hsep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1) :=
    scaleRadius_add_one_le_previous hn hk0 (by omega)
  have huOutside : trajectory omega u ∉ disc x (scaleRadius n k) :=
    not_mem_smaller_disc_of_mem_larger_boundary hsep (by
      simpa only [u, profileOuterBoundary] using huBoundary)
  intro q huq hqt hqChild
  have hqH : q ≤ horizon := hqt.trans htH
  have hqDisc : trajectory omega q ∈ disc x (scaleRadius n k) :=
    hqChild.1.trans (scaleRadius_antitone_of_le (by omega) hk)
  obtain ⟨e, heu, heq, heBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    huq.le huOutside hqDisc
  have heH : e ≤ horizon := heq.trans hqH
  have htE : t ≤ e := by
    unfold t profileInnerHitTime
    apply firstHitThrough_le_of_mem
    · simpa only [u, profileGapExitTime, profileOuterHitTime] using heu
    · exact heH
    · simpa only [profileInnerBoundary] using heBoundary
  have heqT : e = t := by omega
  have hqeqT : q = t := by omega
  have htParent : trajectory omega t ∈ profileInnerBoundary n k x :=
    profileInnerHit_mem_of_le htH
  rw [hqeqT] at hqChild
  exact Set.disjoint_left.mp
    (adjacent_profileInnerBoundaries_disjoint (by omega) hk x)
    htParent hqChild

/-- After the last complete parent gap, no further child-inner hit can occur
before the global horizon: such a hit would force another complete parent
entrance. -/
theorem avoids_childBoundary_after_last_parent_gap
    {omega : StepPath} {n horizon k parents : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparents : 0 < parents)
    (hcount : profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon) :
    ∀ q,
      profileGapExitTime (trajectory omega) n horizon x k (parents - 1) < q →
      q ≤ horizon →
      trajectory omega q ∉ profileInnerBoundary n (k + 1) x := by
  classical
  let last := parents - 1
  let u := profileGapExitTime (trajectory omega) n horizon x k last
  have hlast : last < parents := by dsimp only [last]; omega
  have huH : u ≤ horizon := hcomplete last hlast
  have huBoundary : trajectory omega u ∈ profileOuterBoundary n k x :=
    profileGapExit_mem_outerBoundary huH
  have hsep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1) :=
    scaleRadius_add_one_le_previous hn hk0 (by omega)
  have huOutside : trajectory omega u ∉ disc x (scaleRadius n k) :=
    not_mem_smaller_disc_of_mem_larger_boundary hsep (by
      simpa only [u, profileOuterBoundary] using huBoundary)
  have hparentDisjoint : Disjoint (profileOuterBoundary n k x)
      (profileInnerBoundary n k x) := by
    simpa only [profileOuterBoundary, profileInnerBoundary] using
      profileBoundaries_disjoint hn hk0 (by omega : k ≤ n + 1) x
  have htLastH : profileInnerHitTime (trajectory omega) n horizon x k last ≤
      horizon :=
    (profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k last).trans huH
  have hparentsH : parents < horizon + 1 := by
    have hfinishLast : excursionFinish (trajectory omega)
        (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        horizon last ≤ horizon := by
      simpa only [profileInnerHitTime] using htLastH
    have hindex := index_succ_le_excursionFinish_of_le
      (trajectory omega) (profileOuterBoundary n k x)
      (profileInnerBoundary n k x) hparentDisjoint horizon last hfinishLast
    dsimp only [last] at hfinishLast hindex
    omega
  intro q huq hqH hqChild
  have hqDisc : trajectory omega q ∈ disc x (scaleRadius n k) :=
    hqChild.1.trans (scaleRadius_antitone_of_le (by omega) hk)
  obtain ⟨e, heu, heq, heBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    huq.le huOutside hqDisc
  have heH : e ≤ horizon := heq.trans hqH
  have htNext : profileInnerHitTime (trajectory omega) n horizon x k parents ≤
      e := by
    unfold profileInnerHitTime
    apply firstHitThrough_le_of_mem
    · simpa only [u, last, profileGapExitTime,
        profileOuterHitTime, show parents - 1 + 1 = parents by omega] using heu
    · exact heH
    · simpa only [profileInnerBoundary] using heBoundary
  have hmore : parents <
      profileCompletedCount (trajectory omega) n horizon x k := by
    apply (excursionFinish_le_horizon_iff_lt_completedExcursionCount
      (trajectory omega) (profileOuterBoundary n k x)
      (profileInnerBoundary n k x) horizon hparentsH).mp
    exact htNext.trans heH
  rw [hcount] at hmore
  exact (Nat.lt_irrefl parents hmore)

/-- Every retained piece between successive parent gaps is inert for the
child scanner while it is seeking the child inner boundary. -/
theorem scan_between_parent_gaps
    {omega : StepPath} {n horizon k parents parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparent : parent + 1 < parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (c : ℕ) :
    @scanSegment (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileGapExitTime (trajectory omega) n horizon x k parent + 1)
        (profileInnerHitTime (trajectory omega) n horizon x k (parent + 1) -
          profileGapExitTime (trajectory omega) n horizon x k parent)
        ⟨false, c⟩ = ⟨false, c⟩ := by
  classical
  apply scanSegment_seekingInner_of_avoids
  intro q hq
  apply avoids_childBoundary_between_parent_gaps hn hk0 hk hparent hcomplete
  · omega
  · have horder := profileGapExitTime_le_profileInnerHitTime_of_lt
      (trajectory omega) n horizon x k (show parent < parent + 1 by omega)
    omega

/-- The final retained suffix is inert for the child scanner. -/
theorem scan_after_last_parent_gap
    {omega : StepPath} {n horizon k parents : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hparents : 0 < parents)
    (hcount : profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (c : ℕ) :
    @scanSegment (trajectory omega)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (Classical.decPred _) (Classical.decPred _)
        (profileGapExitTime (trajectory omega) n horizon x k (parents - 1) + 1)
        (horizon - profileGapExitTime (trajectory omega) n horizon x k
          (parents - 1)) ⟨false, c⟩ = ⟨false, c⟩ := by
  classical
  apply scanSegment_seekingInner_of_avoids
  intro q hq
  apply avoids_childBoundary_after_last_parent_gap hn hk0 hk hparents hcount
    hcomplete
  · omega
  · have huH := hcomplete (parents - 1) (by omega)
    omega

/-- The number of global child excursions is exactly the sum of the literal
offspring counts of the chronological parent gaps. -/
theorem profileCompletedCount_succ_eq_sum_offspring
    {omega : StepPath} {n horizon k parents : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hcount : profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon) :
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
    intro i hi
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
    · exact scan_prefix_to_first_parent hn hk0 hk hx (hcomplete 0 hparents)
    · intro i hi c
      exact scan_profileGap_add_offspring hn hk0 hk (hcomplete i hi) c
    · intro i hi c
      exact scan_between_parent_gaps hn hk0 hk hi hcomplete c
    · intro c
      exact scan_after_last_parent_gap hn hk0 hk hparents hcount hcomplete c
  have hdisjoint : Disjoint outer inner := by
    exact adjacent_profileInnerBoundaries_disjoint (by omega) hk x
  have hcompleted := scanThrough_completed_eq_completedExcursionCount
    (trajectory omega) outer inner hdisjoint horizon
  have hrange : profileCompletedCount (trajectory omega) n horizon x (k + 1) =
      ∑ i ∈ Finset.range parents, offspring i := by
    change completedExcursionCount (trajectory omega) outer inner horizon = _
    rw [← hcompleted]
    exact congrArg BoundaryScanState.completed hscan
  rw [hrange, Fin.sum_univ_eq_sum_range]

/-! ## Canonical weak composition carried by an actual path -/

/-- The weak composition with prescribed parent multiplicities. -/
noncomputable def gapPatternOfMultiplicities
    {a b : ℕ} (f : Fin a → ℕ) (h : ∑ i, f i = b) : GapPattern a b :=
  Sym.mk (∑ i : Fin a, f i • ({i} : Multiset (Fin a))) (by simp [h])

@[simp] theorem gapMultiplicity_gapPatternOfMultiplicities
    {a b : ℕ} (f : Fin a → ℕ) (h : ∑ i, f i = b) (i : Fin a) :
    gapMultiplicity (gapPatternOfMultiplicities f h) i = f i := by
  simp only [gapMultiplicity, gapPatternOfMultiplicities, Sym.coe_mk]
  rw [Multiset.count_sum']
  simp only [Multiset.count_nsmul, Multiset.count_singleton]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [if_neg (Ne.symm hji)]
  · simp

/-- The genuine parent-gap offspring vector as a weak composition of the
next global profile count. -/
noncomputable def actualProfileOffspringGapPattern
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon) :
    GapPattern parents children :=
  gapPatternOfMultiplicities
    (fun i ↦ profileGapOffspringCount omega n horizon x k i)
    ((profileCompletedCount_succ_eq_sum_offspring hn hk0 hk hx hparents
      hparentCount hcomplete).symm.trans hchildCount)

@[simp] theorem gapMultiplicity_actualProfileOffspringGapPattern
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents) :
    gapMultiplicity (actualProfileOffspringGapPattern hn hk0 hk hx hparents
      hparentCount hchildCount hcomplete) i =
      profileGapOffspringCount omega n horizon x k i := by
  apply gapMultiplicity_gapPatternOfMultiplicities

end

end Erdos1165.AnnularProfileOffspringPartition

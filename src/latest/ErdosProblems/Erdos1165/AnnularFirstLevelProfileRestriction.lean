/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialUpperCover
import ErdosProblems.Erdos1165.AnnularOffspringScan
import ErdosProblems.Erdos1165.AnnularSpatialSplice
import ErdosProblems.Erdos1165.TerminalProfileBoundarySeparation

/-!
# Restricting a fixed profile to its unique first-level gap

On a stopped fixed successful path the level-one excursion count is one.
Consequently every deeper excursion occurs between the completion of that
unique level-one inward excursion and its following return to level zero.
This file records the exact pathwise equality of all internal and terminal
profile coordinates with the corresponding fresh-gap coordinates.
-/

open Set

namespace Erdos1165.AnnularFirstLevelProfileRestriction

open AppendixFirstMoment AnnularOffspringScan AnnularProfileClocks
  AnnularProfileGapAtoms AnnularProfileLiteralAtoms AnnularRadialLabelWord
  AnnularRadialUpperCover PlanarPotential Proposition13Assembly
  AnnularSpatialSplice PotentialEuclideanGeometry
  TerminalBoundaryScan TerminalClockSplice TerminalExcursionBridge
  TerminalExcursionPathwise
  TerminalSequentialVisitLaw TerminalSpliceProfileGeometry ThickPoint

noncomputable section

private theorem adjacent_symm {a b : Point} (h : Adjacent a b) :
    Adjacent b a := by
  unfold Adjacent at h ⊢
  rw [show b.1 - a.1 = -(a.1 - b.1) by ring,
    show b.2 - a.2 = -(a.2 - b.2) by ring,
    Int.natAbs_neg, Int.natAbs_neg]
  exact h

/-- A nearest-neighbour path which starts outside a disc and is inside at a
later time meets the literal inner vertex boundary in between. -/
private theorem exists_discBoundary_between
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
  exact adjacent_symm (hstep (start + previous))

private theorem radialBoundary_subset_levelOneDisc
    {n : ℕ} (hn : 1 ≤ n) {x : Point} (label : Fin (n + 2))
    (hlabel : 1 ≤ (label : ℕ)) :
    radialBoundary n x label ⊆ disc x (scaleRadius n 1) := by
  intro z hz
  have hzDisc : z ∈ disc x (scaleRadius n label) := hz.1
  change latticeDistance x z ≤ scaleRadius n 1
  change latticeDistance x z ≤ scaleRadius n label at hzDisc
  apply hzDisc.trans
  by_cases hregular : (label : ℕ) ≤ n
  · exact scaleRadius_antitone_of_le hlabel hregular
  · have hterminal : (label : ℕ) = n + 1 := by omega
    rw [hterminal]
    exact (terminalRadius_le_regularRadius_self n hn).trans
      (scaleRadius_antitone_of_le hn le_rfl)

private theorem zero_outside_candidate_levelOneDisc
    {n : ℕ} (hn : 2 ≤ n) {x : Point} (hx : x ∈ candidateBox n) :
    (0 : Point) ∉ disc x (scaleRadius n 1) := by
  intro hmem
  have hdistance : euclideanRadius (-x) ≤ scaleRadius n 1 := by
    change latticeDistance x 0 ≤ scaleRadius n 1 at hmem
    rw [TerminalSpliceProfileGeometry.latticeDistance_eq_euclideanRadius_sub]
      at hmem
    simpa using hmem
  have hgeom := candidate_neg_euclideanRadius_bounds hx
  have hr10 : scaleRadius n 1 ≤ scaleRadius n 0 :=
    scaleRadius_antitone_of_le (by omega) (by omega)
  have hr0pos : 0 < scaleRadius n 0 := by
    have hnRadius : (n : ℝ) ≤ scaleRadius n 1 :=
      natCast_le_scaleRadius_one n (by omega)
    have hnpos : (0 : ℝ) < n := by positivity
    linarith
  nlinarith

private theorem zero_outside_candidate_levelZeroDisc
    {n : ℕ} (hn : 2 ≤ n) {x : Point} (hx : x ∈ candidateBox n) :
    (0 : Point) ∉ disc x (scaleRadius n 0) := by
  intro hmem
  have hdistance : euclideanRadius (-x) ≤ scaleRadius n 0 := by
    change latticeDistance x 0 ≤ scaleRadius n 0 at hmem
    rw [TerminalSpliceProfileGeometry.latticeDistance_eq_euclideanRadius_sub]
      at hmem
    simpa using hmem
  have hgeom := candidate_neg_euclideanRadius_bounds hx
  have hr0pos : 0 < scaleRadius n 0 := by
    have hnRadius : (n : ℝ) ≤ scaleRadius n 1 :=
      natCast_le_scaleRadius_one n (by omega)
    have hr10 : scaleRadius n 1 ≤ scaleRadius n 0 :=
      scaleRadius_antitone_of_le (by omega) (by omega)
    have hnpos : (0 : ℝ) < n := by positivity
    linarith
  nlinarith

private theorem firstHitThrough_le_of_mem
    {s : WalkPath} {A : Set Point} [DecidablePred (· ∈ A)]
    {start horizon q : ℕ} (hstart : start ≤ q) (hqH : q ≤ horizon)
    (hq : s q ∈ A) :
    firstHitThrough s A start horizon ≤ q := by
  have hqFin : q ∈ hitTimesThrough s A start horizon :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hstart, hqH⟩, hq⟩
  have hne : (hitTimesThrough s A start horizon).Nonempty := ⟨q, hqFin⟩
  simp only [firstHitThrough, dif_pos hne]
  exact Finset.min'_le _ q hqFin

private theorem scanSegment_eq_self_of_avoids
    (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (start length : ℕ) (state : BoundaryScanState)
    (houter : ∀ q, q < length → s (start + q) ∉ outer)
    (hinner : ∀ q, q < length → s (start + q) ∉ inner) :
    scanSegment s outer inner start length state = state := by
  rcases state with ⟨seekingOuter, completed⟩
  cases seekingOuter
  · exact scanSegment_seekingInner_of_avoids
      s outer inner start length completed hinner
  · exact scanSegment_seekingOuter_of_avoids
      s outer inner start length completed houter

private theorem completedExcursionCount_eq_on_interval
    {s middlePath : WalkPath} {outer inner : Set Point}
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    {t u horizon : ℕ} (htu : t ≤ u) (huH : u ≤ horizon)
    (hlocal : ∀ q, q ≤ u - t → middlePath q = s (t + q))
    (hpre : ∀ q, q < t → s q ∉ outer)
    (hpostOuter : ∀ q, u < q → q ≤ horizon → s q ∉ outer)
    (hpostInner : ∀ q, u < q → q ≤ horizon → s q ∉ inner)
    (hdisjoint : Disjoint outer inner) :
    completedExcursionCount s outer inner horizon =
      completedExcursionCount middlePath outer inner (u - t) := by
  have hprefix : scanSegment s outer inner 0 t initialState = initialState := by
    exact scanSegment_seekingOuter_of_avoids s outer inner 0 t 0
      (fun q hq ↦ by simpa using hpre q hq)
  have hmiddle (state : BoundaryScanState) :
      scanSegment s outer inner t (u - t + 1) state =
        scanSegment middlePath outer inner 0 (u - t + 1) state := by
    apply scanSegment_congr
    intro q hq
    simpa using (hlocal q (by omega)).symm
  have hsuffix (state : BoundaryScanState) :
      scanSegment s outer inner (u + 1) (horizon - u) state = state := by
    apply scanSegment_eq_self_of_avoids
    · intro q hq
      apply hpostOuter (u + 1 + q) (by omega) (by omega)
    · intro q hq
      apply hpostInner (u + 1 + q) (by omega) (by omega)
  apply completedExcursionCount_eq_of_scanThrough_eq hdisjoint
  rw [scanThrough,
    show horizon + 1 = t + (u - t + 1) + (horizon - u) by omega,
    scanSegment_add, scanSegment_add, hprefix]
  simp only [Nat.zero_add]
  rw [hmiddle]
  have hstart : t + (u - t + 1) = u + 1 := by omega
  rw [hstart, hsuffix, scanThrough]

private theorem levelOne_times_le
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    let s := trajectory omega
    let a := profileOuterHitTime s n horizon x 1 0
    let t := profileInnerHitTime s n horizon x 1 0
    let u := profileGapExitTime s n horizon x 1 0
    a ≤ t ∧ t ≤ u ∧ u ≤ horizon := by
  classical
  dsimp only
  have hu := levelOne_return_le_horizon_of_fixedProfile (by omega)
    hexit hx hfixed
  have ht : profileInnerHitTime (trajectory omega) n horizon x 1 0 ≤
      profileGapExitTime (trajectory omega) n horizon x 1 0 :=
    profileInnerHitTime_le_profileGapExitTime _ _ _ _ _ _
  have ha : excursionStart (trajectory omega)
      (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x)
      horizon 0 ≤ profileInnerHitTime (trajectory omega) n horizon x 1 0 :=
    TerminalExcursionPathwise.excursionStart_le_finish _ _ _ _ _
  exact ⟨ha, ht, hu⟩

private theorem levelOne_avoids_inner_after_gap
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    ∀ q, profileGapExitTime (trajectory omega) n horizon x 1 0 ≤ q →
      q ≤ horizon →
      trajectory omega q ∉ profileInnerBoundary n 1 x := by
  classical
  have hcount : completedExcursionCount (trajectory omega)
      (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x) horizon = 1 := by
    change profileCompletedCount (trajectory omega) n horizon x 1 = 1
    rw [← excursionProfile_eq_profileCompletedCount
      (trajectory omega) n horizon x (by omega) (by omega)]
    exact hfixed.1
  have hdisjoint : Disjoint (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) := by
    simpa [profileOuterBoundary, profileInnerBoundary] using
      (TerminalProfileBoundarySeparation.profileBoundaries_disjoint
        (n := n) (k := 1) hn (by omega) (by omega) x)
  have hzero : excursionFinish (trajectory omega)
      (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x)
      horizon 0 ≤ horizon := by
    apply (excursionFinish_le_horizon_iff_lt_completedExcursionCount
      (trajectory omega) (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) horizon (j := 0) (by omega)).2
    rw [hcount]
    omega
  have hH : 1 ≤ horizon :=
    (index_succ_le_excursionFinish_of_le (trajectory omega)
      (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x)
      hdisjoint horizon 0 hzero).trans hzero
  intro q huq hqH hqInner
  have hfinish : excursionFinish (trajectory omega)
      (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x)
      horizon 1 ≤ horizon := by
    unfold excursionFinish
    apply (firstHitThrough_le_horizon_iff (trajectory omega)
      (profileInnerBoundary n 1 x)
      (excursionStart (trajectory omega) (profileOuterBoundary n 1 x)
        (profileInnerBoundary n 1 x) horizon 1) horizon).2
    refine ⟨q, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨?_, hqH⟩, hqInner⟩⟩
    exact huq
  have hlt :=
    (excursionFinish_le_horizon_iff_lt_completedExcursionCount
      (trajectory omega) (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) horizon (j := 1) (by omega)).mp hfinish
  rw [hcount] at hlt
  omega

private theorem radialBoundary_avoids_before_levelOne_inner
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x))
    (label : Fin (n + 2)) (hlabel : 1 ≤ (label : ℕ)) :
    ∀ q, q < profileInnerHitTime (trajectory omega) n horizon x 1 0 →
      trajectory omega q ∉ radialBoundary n x label := by
  classical
  obtain ⟨_ha, ht, hu⟩ := levelOne_times_le hn hexit hx hfixed
  intro q hqt hqBoundary
  have hqH : q ≤ horizon := by omega
  have hqDiscOne : trajectory omega q ∈ disc x (scaleRadius n 1) :=
    radialBoundary_subset_levelOneDisc (by omega) label hlabel hqBoundary
  obtain ⟨e, he0, heq, heBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    (Nat.zero_le q) (zero_outside_candidate_levelOneDisc hn hx) hqDiscOne
  have heH : e ≤ horizon := heq.trans hqH
  have heDiscZero : trajectory omega e ∈ disc x (scaleRadius n 0) :=
    heBoundary.1.trans (scaleRadius_antitone_of_le (by omega) (by omega))
  obtain ⟨d, hd0, hde, hdBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    (Nat.zero_le e) (zero_outside_candidate_levelZeroDisc hn hx) heDiscZero
  have hdH : d ≤ horizon := hde.trans heH
  have haD : profileOuterHitTime (trajectory omega) n horizon x 1 0 ≤ d := by
    unfold profileOuterHitTime excursionStart
    simpa only [Function.iterate_zero, id_eq] using
      firstHitThrough_le_of_mem (s := trajectory omega)
        (A := profileOuterBoundary n 1 x) (start := 0) (horizon := horizon)
        (q := d) (Nat.zero_le d) hdH (by
          simpa [profileOuterBoundary] using hdBoundary)
  have htE : profileInnerHitTime (trajectory omega) n horizon x 1 0 ≤ e := by
    unfold profileInnerHitTime
    exact firstHitThrough_le_of_mem (haD.trans hde) heH (by
      simpa [profileInnerBoundary] using heBoundary)
  omega

private theorem radialBoundary_avoids_after_levelOne_gap
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x))
    (label : Fin (n + 2)) (hlabel : 1 ≤ (label : ℕ)) :
    ∀ q, profileGapExitTime (trajectory omega) n horizon x 1 0 < q →
      q ≤ horizon → trajectory omega q ∉ radialBoundary n x label := by
  classical
  obtain ⟨_ha, _ht, hu⟩ := levelOne_times_le hn hexit hx hfixed
  intro q huq hqH hqBoundary
  have huBoundary : trajectory omega
      (profileGapExitTime (trajectory omega) n horizon x 1 0) ∈
        profileOuterBoundary n 1 x :=
    profileGapExit_mem_outerBoundary hu
  have hsep : scaleRadius n 1 + 1 ≤ scaleRadius n 0 := by
    have h := TerminalProfileBoundarySeparation.scaleRadius_add_one_le_previous
      (n := n) (k := 1) hn (by omega) (by omega)
    rw [show 1 - 1 = 0 by omega] at h
    exact h
  have huOutside : trajectory omega
      (profileGapExitTime (trajectory omega) n horizon x 1 0) ∉
        disc x (scaleRadius n 1) :=
    not_mem_smaller_disc_of_mem_larger_boundary hsep (by
      simpa [profileOuterBoundary] using huBoundary)
  have hqDiscOne : trajectory omega q ∈ disc x (scaleRadius n 1) :=
    radialBoundary_subset_levelOneDisc (by omega) label hlabel hqBoundary
  obtain ⟨e, heu, heq, heBoundary⟩ := exists_discBoundary_between
    (fun r ↦ Proposition13Assembly.adjacent_trajectory_succ omega r)
    huq.le huOutside hqDiscOne
  exact levelOne_avoids_inner_after_gap hn hfixed e heu (heq.trans hqH) (by
    simpa [profileInnerBoundary] using heBoundary)

/-- Every excursion coordinate at levels `2,...,n+1` is unchanged when the
global walk is restricted to the unique completed level-one gap and viewed
in its fresh clock. -/
theorem excursionProfile_profileGapWalk_one_eq
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x))
    (k : Fin (n + 2)) (hk : 2 ≤ (k : ℕ)) :
    excursionProfile (profileGapWalk omega n horizon x 1 0)
        n (profileGapLength omega n horizon x 1 0) x k =
      excursionProfile (trajectory omega) n horizon x k := by
  classical
  let s := trajectory omega
  let t := profileInnerHitTime s n horizon x 1 0
  let u := profileGapExitTime s n horizon x 1 0
  let outer := discBoundary x (scaleRadius n ((k : ℕ) - 1))
  let inner := discBoundary x (scaleRadius n (k : ℕ))
  let predecessor : Fin (n + 2) := ⟨(k : ℕ) - 1, by omega⟩
  have hpredecessor : 1 ≤ (predecessor : ℕ) := by
    dsimp only [predecessor]
    omega
  obtain ⟨_ha, htu, huH⟩ := levelOne_times_le hn hexit hx hfixed
  have hcount : completedExcursionCount s outer inner horizon =
      completedExcursionCount (profileGapWalk omega n horizon x 1 0)
        outer inner (u - t) := by
    apply completedExcursionCount_eq_on_interval htu huH
    · intro q hq
      dsimp only [s, t, u]
      unfold profileGapWalk profileGapStartPoint profileGapFreshPath
      exact trajectoryFrom_shiftSteps_eq omega
        (profileInnerHitTime (trajectory omega) n horizon x 1 0) q
    · intro q hqt
      exact radialBoundary_avoids_before_levelOne_inner hn hexit hx hfixed
        predecessor hpredecessor q hqt
    · intro q huq hqH
      exact radialBoundary_avoids_after_levelOne_gap hn hexit hx hfixed
        predecessor hpredecessor q huq hqH
    · intro q huq hqH
      exact radialBoundary_avoids_after_levelOne_gap hn hexit hx hfixed
        k (by omega) q huq hqH
    · dsimp only [outer, inner]
      exact TerminalProfileBoundarySeparation.profileBoundaries_disjoint_fin
        hn x k (by omega)
  unfold excursionProfile
  rw [dif_neg (by omega : (k : ℕ) ≠ 0),
    dif_neg (by omega : (k : ℕ) ≠ 0)]
  dsimp only [s, t, u, outer, inner] at hcount
  exact hcount.symm

/-- The fresh unique level-one gap inherits every fixed internal coordinate
and both terminal bounds from the original stopped successful path. -/
theorem profileGapWalk_one_fixed_coordinates
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    (∀ i : Fin (n - 1),
      excursionProfile (profileGapWalk omega n horizon x 1 0)
          n (profileGapLength omega n horizon x 1 0) x
          ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i) ∧
    terminalLower n delta ≤
      (excursionProfile (profileGapWalk omega n horizon x 1 0)
        n (profileGapLength omega n horizon x 1 0) x
        ⟨n + 1, by omega⟩ : ℝ) ∧
    excursionProfile (profileGapWalk omega n horizon x 1 0)
        n (profileGapLength omega n horizon x 1 0) x
        ⟨n + 1, by omega⟩ ≤ n ^ 3 := by
  constructor
  · intro i
    let k : Fin (n + 2) :=
      ⟨scaleIndex i, by unfold scaleIndex; omega⟩
    have hk : 2 ≤ (k : ℕ) := by
      dsimp only [k]
      unfold scaleIndex
      omega
    rw [excursionProfile_profileGapWalk_one_eq hn hexit hx hfixed
      k hk]
    exact hfixed.2.1 i
  · let k : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hk : 2 ≤ (k : ℕ) := by dsimp only [k]; omega
    have hterminal := excursionProfile_profileGapWalk_one_eq hn hexit hx hfixed
      k hk
    rw [hterminal]
    exact hfixed.2.2

/-- Walk-facing form at the actual strong-Markov restart.  The start point
and fresh path are the stopped position and post-stopping increments, while
the finite duration is exactly the first level-zero return duration. -/
theorem firstLevelOne_fresh_fixed_coordinates
    {n horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {m : Profile n} {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    let T := firstLevelOneEntranceTime n x
    let duration := profileGapLength omega n horizon x 1 0
    (∀ i : Fin (n - 1),
      excursionProfile
          (fun q ↦ trajectoryFrom (stoppedPosition T omega)
            (postWithTopStoppingSteps T omega) q)
          n duration x ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i) ∧
    terminalLower n delta ≤
      (excursionProfile
        (fun q ↦ trajectoryFrom (stoppedPosition T omega)
          (postWithTopStoppingSteps T omega) q)
        n duration x ⟨n + 1, by omega⟩ : ℝ) ∧
    excursionProfile
        (fun q ↦ trajectoryFrom (stoppedPosition T omega)
          (postWithTopStoppingSteps T omega) q)
        n duration x ⟨n + 1, by omega⟩ ≤ n ^ 3 := by
  classical
  dsimp only
  have ht : firstLevelOneEntranceTime n x omega =
      profileInnerHitTime (trajectory omega) n horizon x 1 0 :=
    firstLevelOneEntranceTime_eq_profileInnerHitTime (by omega) hexit hx hfixed
  have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq ht
  have hpos := stoppedPosition_eq_of_eq ht
  have hcoordinates := profileGapWalk_one_fixed_coordinates hn hexit hx hfixed
  have hwalk :
      (fun q ↦ trajectoryFrom
        (stoppedPosition (firstLevelOneEntranceTime n x) omega)
        (postWithTopStoppingSteps (firstLevelOneEntranceTime n x) omega) q) =
      profileGapWalk omega n horizon x 1 0 := by
    funext q
    rw [hpost, hpos]
    rfl
  rw [hwalk]
  exact hcoordinates

end

end Erdos1165.AnnularFirstLevelProfileRestriction

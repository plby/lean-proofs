/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedParsedBridgeCode

namespace Erdos1165.AsymmetricPaddedBridgeClock

open AlternatingConcatPrefixFree AnnularBoundaryExcursionKernel
open AnnularOffspringScan AnnularProfileClocks
open AsymmetricPaddedActiveFactorization AsymmetricPaddedRemoteRenewal
open AsymmetricPaddedBridgeCode AsymmetricPaddedBridgeLiteralFactorization
open AsymmetricPaddedBridgeExtraction
open MarkedBridgeFactorization PlanarPotential RealDiscFinite
open ThickPoint TerminalBoundaryScan TerminalClockSplice
open TerminalSkeletonWords
open TerminalExcursionPathwise
open TerminalGlobalExitSplice TerminalProfileClockEquivalence

noncomputable section

attribute [local instance] Classical.propDecidable

theorem wordWalk_append_left (start : Point) (left right : List Direction)
    {q : ℕ} (hq : q ≤ left.length) :
    wordWalk start (left ++ right) q = wordWalk start left q := by
  simp [wordWalk, wordPosition, List.take_append_of_le_length hq]

theorem wordWalk_append_right (start : Point) (left right : List Direction)
    {q : ℕ} (hq : q ≤ right.length) :
    wordWalk start (left ++ right) (left.length + q) =
      wordWalk (wordEndpoint start left) right q := by
  simp [wordWalk, wordPosition, List.take_add, wordEndpoint]

theorem trajectoryFrom_extendStoppedWord_eq_wordWalk
    (start : Point) (word : StoppedWord) {q : ℕ} (hq : q ≤ word.1) :
    trajectoryFrom start (extendStoppedWord word) q =
      wordWalk start (List.ofFn word.2) q := by
  rw [wordWalk_eq_trajectoryFrom_extendStoppedWord _ _ (by simpa using hq)]
  congr 2
  exact (listStoppedWord_ofFn word).symm

theorem IsFirstHitSegment.shiftFrom
    {s : WalkPath} {A : Set Point}
    {base start stop horizon : ℕ}
    (hbase : base ≤ horizon)
    (h : IsFirstHitSegment s A (base + start) (base + stop) horizon) :
    IsFirstHitSegment (fun q ↦ s (base + q)) A start stop
      (horizon - base) := by
  have hstopH := h.2.1
  refine ⟨Nat.add_le_add_iff_left.mp h.1, by omega, ?_, ?_⟩
  · simpa only using h.2.2.1
  · intro q hstart hstop hmem
    exact h.2.2.2 (base + q) (by omega) (by omega) hmem

theorem IsFirstHitSegment.addPrefix
    {s : WalkPath} {A : Set Point}
    {base start stop horizon : ℕ}
    (hbase : base ≤ horizon)
    (h : IsFirstHitSegment (fun q ↦ s (base + q)) A start stop
      (horizon - base)) :
    IsFirstHitSegment s A (base + start) (base + stop) horizon := by
  have hstopH := h.2.1
  refine ⟨Nat.add_le_add_left h.1 base, by omega, h.2.2.1, ?_⟩
  intro q hstart hstop hmem
  let r := q - base
  have hr : base + r = q := Nat.add_sub_of_le (by omega)
  apply h.2.2.2 r
  · omega
  · omega
  · simpa only [hr] using hmem

theorem IsFirstHitSegment.congrPath
    {s t : WalkPath} {A : Set Point} {start stop horizon : ℕ}
    (hpath : ∀ q ≤ horizon, s q = t q)
    (h : IsFirstHitSegment s A start stop horizon) :
    IsFirstHitSegment t A start stop horizon := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [← hpath stop h.2.1]
    exact h.2.2.1
  · intro q hstart hstop hmem
    exact h.2.2.2 q hstart hstop ((hpath q (hstop.le.trans h.2.1)).symm ▸ hmem)

theorem AvoidsThrough.addPrefix
    {s : WalkPath} {A : Set Point}
    {base start horizon : ℕ}
    (hbase : base ≤ horizon)
    (h : AvoidsThrough (fun q ↦ s (base + q)) A start
      (horizon - base)) :
    AvoidsThrough s A (base + start) horizon := by
  intro q hstart hstop hmem
  let r := q - base
  have hr : base + r = q := Nat.add_sub_of_le (by omega)
  apply h r
  · omega
  · omega
  · simpa only [hr] using hmem

def FirstHitExcursionSchedule.addPrefix
    {s : WalkPath} {outer inner : Set Point}
    {base horizon count : ℕ}
    (hbase : base ≤ horizon)
    (hfirst : IsFirstHitSegment s outer 0 base horizon)
    (schedule : FirstHitExcursionSchedule (fun q ↦ s (base + q))
      outer inner (horizon - base) count) :
    FirstHitExcursionSchedule s outer inner horizon count where
  count_le := by
    have := schedule.count_le
    omega
  outerTime := fun j ↦ base + schedule.outerTime j
  innerTime := fun j ↦ base + schedule.innerTime j
  firstOuterZero := by
    have hzero : schedule.outerTime 0 = 0 := by
      have hle := schedule.firstOuterZero.1
      have hmem := hfirst.2.2.1
      have hlocalMem : (fun q ↦ s (base + q)) 0 ∈ outer := by simpa using hmem
      by_contra hne
      exact schedule.firstOuterZero.2.2.2 0 (Nat.zero_le _)
        (Nat.pos_of_ne_zero hne) hlocalMem
    simpa only [hzero, Nat.add_zero] using hfirst
  firstInner := by
    intro j hj
    exact IsFirstHitSegment.addPrefix hbase (schedule.firstInner j hj)
  firstOuterSucc := by
    intro j hj
    exact IsFirstHitSegment.addPrefix hbase (schedule.firstOuterSucc j hj)
  noFinalInner := AvoidsThrough.addPrefix hbase schedule.noFinalInner

def FirstHitExcursionSchedule.congrPath
    {s t : WalkPath} {outer inner : Set Point} {horizon count : ℕ}
    (hpath : ∀ q ≤ horizon, s q = t q)
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    FirstHitExcursionSchedule t outer inner horizon count where
  count_le := schedule.count_le
  outerTime := schedule.outerTime
  innerTime := schedule.innerTime
  firstOuterZero := IsFirstHitSegment.congrPath hpath schedule.firstOuterZero
  firstInner := by
    intro j hj
    exact IsFirstHitSegment.congrPath hpath (schedule.firstInner j hj)
  firstOuterSucc := by
    intro j hj
    exact IsFirstHitSegment.congrPath hpath (schedule.firstOuterSucc j hj)
  noFinalInner := by
    intro q hstart hstop hmem
    exact schedule.noFinalInner q hstart hstop ((hpath q hstop).symm ▸ hmem)

def FirstHitExcursionSchedule.castHorizon
    {s : WalkPath} {outer inner : Set Point} {horizon horizon' count : ℕ}
    (h : horizon = horizon')
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    FirstHitExcursionSchedule s outer inner horizon' count :=
  h ▸ schedule

@[simp] theorem FirstHitExcursionSchedule.castHorizon_outerTime
    {s : WalkPath} {outer inner : Set Point} {horizon horizon' count j : ℕ}
    (h : horizon = horizon')
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    (Erdos1165.AsymmetricPaddedBridgeClock.FirstHitExcursionSchedule.castHorizon h schedule).outerTime j =
      schedule.outerTime j := by
  subst horizon'
  rfl

@[simp] theorem FirstHitExcursionSchedule.castHorizon_innerTime
    {s : WalkPath} {outer inner : Set Point} {horizon horizon' count j : ℕ}
    (h : horizon = horizon')
    (schedule : FirstHitExcursionSchedule s outer inner horizon count) :
    (Erdos1165.AsymmetricPaddedBridgeClock.FirstHitExcursionSchedule.castHorizon h schedule).innerTime j =
      schedule.innerTime j := by
  subst horizon'
  rfl

def paddedParentSchedule
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1) :
    FirstHitExcursionSchedule
      (trajectoryFrom u.1 (extendStoppedWord parent.1))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) parent.1.1 q := by
  let s := trajectoryFrom u.1 (extendStoppedWord parent.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  have hcount : completedExcursionCount s outer inner parent.1.1 = q := by
    simpa only [s, outer, inner, boundaryExcursionCount] using parent.2.2.1
  have hcountLe : q ≤ parent.1.1 + 1 := by
    calc
      q = completedExcursionCount s outer inner parent.1.1 := hcount.symm
      _ ≤ parent.1.1 + 1 :=
        completedExcursionCount_le s outer inner parent.1.1
  have houterZero : excursionStart s outer inner parent.1.1 0 ≤
      parent.1.1 := by
    unfold excursionStart
    simp only [Function.iterate_zero_apply]
    apply (firstHitThrough_le_horizon_iff s outer 0 parent.1.1).2
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨le_rfl, Nat.zero_le _⟩, ?_⟩⟩
    simpa only [s, outer, trajectoryFrom_zero, profileInnerBoundary] using
      (mem_discBoundaryFinset.mp u.2)
  have hinner : ∀ j, j < q →
      excursionFinish s outer inner parent.1.1 j ≤ parent.1.1 := by
    intro j hj
    apply finish_le_horizon_of_lt_completedExcursionCount
    rw [hcount]
    exact hj
  have houterSucc : ∀ j, j < q →
      excursionStart s outer inner parent.1.1 (j + 1) ≤ parent.1.1 := by
    intro j hj
    simpa only [s, outer, inner] using
      paddedParentReturnComplete hn hlp hp u w parent ⟨j, hj⟩
  have hp0 : 0 < p := by omega
  have hdisjoint : Disjoint outer inner := by
    have hp' : (p - 1) + 1 ≤ n := by omega
    simpa only [outer, inner, Nat.sub_add_cancel hp0] using
      (adjacent_profileInnerBoundaries_disjoint
        (by omega : 1 ≤ n) hp' center)
  have hnext : excursionFinish s outer inner parent.1.1 q =
      parent.1.1 + 1 := by
    have hsent := excursionFinish_completedExcursionCount_eq_sentinel
      s outer inner hdisjoint parent.1.1
    calc
      excursionFinish s outer inner parent.1.1 q =
          excursionFinish s outer inner parent.1.1
            (completedExcursionCount s outer inner parent.1.1) :=
        congrArg (fun r ↦ excursionFinish s outer inner parent.1.1 r)
          hcount.symm
      _ = parent.1.1 + 1 := hsent
  exact FirstHitExcursionSchedule.ofExactClocks s outer inner parent.1.1 q
    hcountLe houterZero hinner houterSucc hnext

def enteredSplitSchedule
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2) :
    FirstHitExcursionSchedule
      (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) source.bridge.1.1 q := by
  let left := List.ofFn first.1.2
  let right := List.ofFn parent.1.2
  let full := List.ofFn source.bridge.1.2
  let s := trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
  let base := first.1.1
  let horizon := source.bridge.1.1
  have hlength := congrArg List.length word_eq
  simp only [List.length_append, List.length_ofFn] at hlength
  have hbase : base ≤ horizon := by
    dsimp only [base, horizon]
    omega
  have hfirstPath : ∀ r ≤ first.1.1,
      s r = trajectoryFrom source.start.1 (extendStoppedWord first.1) r := by
    intro r hr
    calc
      s r = wordWalk source.start.1 full r :=
        trajectoryFrom_extendStoppedWord_eq_wordWalk _ _ (by
          dsimp only [horizon] at hbase
          omega)
      _ = wordWalk source.start.1 (left ++ right) r := by rw [word_eq]
      _ = wordWalk source.start.1 left r := by
        apply wordWalk_append_left
        simpa only [left, List.length_ofFn] using hr
      _ = trajectoryFrom source.start.1 (extendStoppedWord first.1) r := by
        symm
        exact trajectoryFrom_extendStoppedWord_eq_wordWalk _ _ hr
  have hfirst : IsFirstHitSegment s
      (profileInnerBoundary n (p - 1) center) 0 base horizon := by
    refine ⟨Nat.zero_le _, hbase, ?_, ?_⟩
    · rw [hfirstPath base (by rfl), first.2.2]
      simpa only [base, profileInnerBoundary] using
        (mem_discBoundaryFinset.mp u.2)
    · intro r _hr0 hr hmem
      apply first.2.1.2 r
      · simpa only [base] using hr
      · exact Or.inl (by simpa only [← hfirstPath r (by omega)] using hmem)
  have hleftEnd : wordEndpoint source.start.1 left = u.1 := by
    simpa only [left] using boundaryExitWordCode_wordEndpoint first
  have htailPath : ∀ r ≤ parent.1.1,
      trajectoryFrom u.1 (extendStoppedWord parent.1) r = s (base + r) := by
    intro r hr
    calc
      trajectoryFrom u.1 (extendStoppedWord parent.1) r =
          wordWalk u.1 right r :=
        trajectoryFrom_extendStoppedWord_eq_wordWalk _ _ hr
      _ = wordWalk (wordEndpoint source.start.1 left) right r := by
        rw [hleftEnd]
      _ = wordWalk source.start.1 (left ++ right) (left.length + r) := by
        symm
        exact wordWalk_append_right _ _ _ (by
          simpa only [right, List.length_ofFn] using hr)
      _ = wordWalk source.start.1 full (left.length + r) := by rw [word_eq]
      _ = s (base + r) := by
        have hq : base + r ≤ source.bridge.1.1 := by
          dsimp only [base]
          omega
        have hwalk := trajectoryFrom_extendStoppedWord_eq_wordWalk
          source.start.1 source.bridge.1 hq
        dsimp only [s, full, left, base] at hwalk ⊢
        simpa only [List.length_ofFn] using hwalk.symm
  have hparentLength : parent.1.1 = horizon - base := by
    dsimp only [horizon, base]
    omega
  let parentSchedule := paddedParentSchedule hn hlp hp u source.endpoint parent
  let shiftedRaw := FirstHitExcursionSchedule.congrPath
    (fun r hr ↦ htailPath r hr) parentSchedule
  let shiftedSchedule : FirstHitExcursionSchedule
      (fun r ↦ s (base + r))
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) (horizon - base) q :=
    Erdos1165.AsymmetricPaddedBridgeClock.FirstHitExcursionSchedule.castHorizon
      hparentLength shiftedRaw
  exact FirstHitExcursionSchedule.addPrefix hbase hfirst shiftedSchedule

def directPaddedInnerPoint
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (j : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) : PaddedInnerPoint n p center :=
  ⟨(AsymmetricSplitLevelSplice.extractTimedReturnSkeleton
      (extendStoppedWord source.bridge.1)
      source.start.1 (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) source.bridge.1.1
      (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge)).entrancePoint j,
    mem_discBoundaryFinset.mpr
      (paddedBridgeEntrancePoint_mem_inner hn hlp hp source.bridge j)⟩

def directPaddedMiddlePoint
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (j : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) : PaddedMiddlePoint n p center := by
  let q := paddedBridgeReturnCount n l p center source.start.1
    source.endpoint.1 source.bridge
  let s := trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  have hreturn := paddedBridgeReturnComplete hn hlp hp source.bridge j
  refine ⟨AsymmetricSplitLevelSplice.returnExitPoint
    (extendStoppedWord source.bridge.1) source.start.1
    outer inner source.bridge.1.1 j, mem_discBoundaryFinset.mpr ?_⟩
  change s (excursionStart s outer inner source.bridge.1.1 (j + 1)) ∈ outer
  unfold excursionStart
  exact firstHitThrough_mem_set_of_le _ _ _ _ hreturn

def directPaddedReturnWordCode
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (j : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    BoundaryExitWordCode (profileOuterBoundary n p center)
      (directPaddedInnerPoint hn hlp hp source j).1
      (directPaddedMiddlePoint hn hlp hp source j).1 := by
  simpa only [profileOuterBoundary, profileInnerBoundary,
    directPaddedInnerPoint, directPaddedMiddlePoint,
    AsymmetricSplitLevelSplice.extractTimedReturnSkeleton] using
      (AsymmetricSplitLevelSplice.extractedReturnCodes
        (paddedBridgeReturnComplete hn hlp hp source.bridge) j)

def directParsedPaddedBridgeTrees
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) :
    List AnnularRecursiveDecoratedProfileCode.ProfileRefinementTree :=
  AsymmetricPaddedCodeAssembly.finTreeList
    (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge) fun j ↦
    (AnnularRecursiveBoundaryParser.parseBoundaryGap n center hn (n - p) p
      (by omega) (by omega)
      (directPaddedInnerPoint hn hlp hp source j)
      (directPaddedMiddlePoint hn hlp hp source j)
      (directPaddedReturnWordCode hn hlp hp source j)).tree

theorem enteredSplit_excursionStart_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    {j : ℕ} (hj : j ≤ q) :
    excursionStart
        (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) source.bridge.1.1 j =
      first.1.1 +
        excursionStart
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 j := by
  let schedule := enteredSplitSchedule hn hlp hp source u first parent word_eq
  let parentSchedule := paddedParentSchedule hn hlp hp u source.endpoint parent
  calc
    _ = schedule.outerTime j := schedule.excursionStart_eq_outerTime hj
    _ = first.1.1 + parentSchedule.outerTime j := by
      simp only [schedule, enteredSplitSchedule,
        FirstHitExcursionSchedule.addPrefix,
        FirstHitExcursionSchedule.congrPath,
        Erdos1165.AsymmetricPaddedBridgeClock.FirstHitExcursionSchedule.castHorizon_outerTime,
        parentSchedule]
    _ = _ := congrArg (first.1.1 + ·)
      (parentSchedule.excursionStart_eq_outerTime hj).symm

theorem enteredSplit_excursionFinish_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    {j : ℕ} (hj : j < q) :
    excursionFinish
        (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) source.bridge.1.1 j =
      first.1.1 +
        excursionFinish
          (trajectoryFrom u.1 (extendStoppedWord parent.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) parent.1.1 j := by
  let schedule := enteredSplitSchedule hn hlp hp source u first parent word_eq
  let parentSchedule := paddedParentSchedule hn hlp hp u source.endpoint parent
  calc
    _ = schedule.innerTime j := schedule.excursionFinish_eq_innerTime hj
    _ = first.1.1 + parentSchedule.innerTime j := by
      simp only [schedule, enteredSplitSchedule,
        FirstHitExcursionSchedule.addPrefix,
        FirstHitExcursionSchedule.congrPath,
        Erdos1165.AsymmetricPaddedBridgeClock.FirstHitExcursionSchedule.castHorizon_innerTime,
        parentSchedule]
    _ = _ := congrArg (first.1.1 + ·)
      (parentSchedule.excursionFinish_eq_innerTime hj).symm

theorem enteredSplit_count_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2) :
    paddedBridgeReturnCount n l p center source.start.1 source.endpoint.1
      source.bridge = q := by
  simpa only [paddedBridgeReturnCount, boundaryExcursionCount] using
    (FirstHitExcursionSchedule.completedExcursionCount_eq
      (enteredSplitSchedule hn hlp hp source u first parent word_eq))

theorem enteredSplit_tailPath
    {n l p q : ℕ} {center : Point}
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    {r : ℕ} (hr : r ≤ parent.1.1) :
    trajectoryFrom u.1 (extendStoppedWord parent.1) r =
      trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
        (first.1.1 + r) := by
  have hlength := congrArg List.length word_eq
  simp only [List.length_append, List.length_ofFn] at hlength
  have hleftEnd : wordEndpoint source.start.1 (List.ofFn first.1.2) = u.1 := by
    simpa only using boundaryExitWordCode_wordEndpoint first
  calc
    trajectoryFrom u.1 (extendStoppedWord parent.1) r =
        wordWalk u.1 (List.ofFn parent.1.2) r :=
      trajectoryFrom_extendStoppedWord_eq_wordWalk _ _ hr
    _ = wordWalk (wordEndpoint source.start.1 (List.ofFn first.1.2))
        (List.ofFn parent.1.2) r := by rw [hleftEnd]
    _ = wordWalk source.start.1
        (List.ofFn first.1.2 ++ List.ofFn parent.1.2)
        ((List.ofFn first.1.2).length + r) := by
      symm
      exact wordWalk_append_right _ _ _ (by simpa using hr)
    _ = wordWalk source.start.1 (List.ofFn source.bridge.1.2)
        (first.1.1 + r) := by
      simpa only [List.length_ofFn] using congrArg
        (fun word ↦ wordWalk source.start.1 word (first.1.1 + r)) word_eq
    _ = trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
        (first.1.1 + r) := by
      symm
      apply trajectoryFrom_extendStoppedWord_eq_wordWalk
      simpa only [List.length_ofFn] using (show first.1.1 + r ≤
        source.bridge.1.1 by omega)

theorem enteredSplit_innerPoint_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    (j : Fin q) :
    let hcount := enteredSplit_count_eq hn hlp hp source u first parent word_eq
    let jd : Fin (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge) := ⟨j, by rw [hcount]; exact j.isLt⟩
    directPaddedInnerPoint hn hlp hp source jd =
      extractedPaddedInnerPoint u source.endpoint parent j := by
  dsimp only
  apply Subtype.ext
  change trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
      (excursionFinish
        (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) source.bridge.1.1 j) =
    trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionFinish
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 j)
  rw [enteredSplit_excursionFinish_eq hn hlp hp source u first parent
    word_eq j.isLt]
  symm
  apply enteredSplit_tailPath source u first parent word_eq
  exact paddedParentExcursionFinish_le u source.endpoint parent j

theorem enteredSplit_middlePoint_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    (j : Fin q) :
    let hcount := enteredSplit_count_eq hn hlp hp source u first parent word_eq
    let jd : Fin (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge) := ⟨j, by rw [hcount]; exact j.isLt⟩
    directPaddedMiddlePoint hn hlp hp source jd =
      extractedPaddedMiddlePoint hn hlp hp u source.endpoint parent j.succ := by
  dsimp only
  apply Subtype.ext
  change trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
      (excursionStart
        (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) source.bridge.1.1 (j + 1)) =
    trajectoryFrom u.1 (extendStoppedWord parent.1)
      (excursionStart
        (trajectoryFrom u.1 (extendStoppedWord parent.1))
        (profileInnerBoundary n (p - 1) center)
        (profileInnerBoundary n p center) parent.1.1 (j + 1))
  rw [enteredSplit_excursionStart_eq hn hlp hp source u first parent
    word_eq (by omega)]
  symm
  apply enteredSplit_tailPath source u first parent word_eq
  simpa only using paddedParentReturnComplete hn hlp hp u source.endpoint parent j

theorem incrementSlice_extendStoppedWord_append_right
    (left right full : StoppedWord)
    (word_eq : List.ofFn left.2 ++ List.ofFn right.2 = List.ofFn full.2)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ right.1) :
    incrementSlice (extendStoppedWord full) (left.1 + a) (left.1 + b) =
      incrementSlice (extendStoppedWord right) a b := by
  have hlength := congrArg List.length word_eq
  simp only [List.length_append, List.length_ofFn] at hlength
  apply List.ext_get
  · simp only [incrementSlice_length]
    omega
  · intro k hk hk'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [incrementSlice, List.getElem_ofFn]
    have hkba : k < b - a := by
      simpa only [incrementSlice_length] using hk'
    have hright : a + k < right.1 := by omega
    have hfull : left.1 + a + k < full.1 := by omega
    simp only [extendStoppedWord, dif_pos hright, dif_pos hfull]
    let idx : Fin (List.ofFn left.2 ++ List.ofFn right.2).length :=
      ⟨left.1 + (a + k), by
        simp only [List.length_append, List.length_ofFn]
        omega⟩
    have hget := (List.get_of_eq word_eq idx).symm
    simp only [List.get_eq_getElem] at hget
    rw [List.getElem_append_right (by
      simp only [idx, List.length_ofFn]
      omega)] at hget
    simpa only [List.getElem_ofFn, List.length_ofFn,
      Nat.add_sub_cancel_left, idx, Nat.add_assoc] using hget

@[simp] theorem directPaddedReturnWordCode_toList
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (j : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) :
    List.ofFn (directPaddedReturnWordCode hn hlp hp source j).1.2 =
      incrementSlice (extendStoppedWord source.bridge.1)
        (excursionFinish
          (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) source.bridge.1.1 j)
        (excursionStart
          (trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1))
          (profileInnerBoundary n (p - 1) center)
          (profileInnerBoundary n p center) source.bridge.1.1 (j + 1)) := by
  change AsymmetricSplitLevelSplice.extractedReturnWords
    (paddedBridgeReturnComplete hn hlp hp source.bridge) j = _
  rw [AsymmetricSplitLevelSplice.extractedReturnCodes_toList]
  rfl

theorem enteredSplit_returnWord_val_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    (j : Fin q) :
    let hcount := enteredSplit_count_eq hn hlp hp source u first parent word_eq
    let jd : Fin (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge) := ⟨j, by rw [hcount]; exact j.isLt⟩
    (directPaddedReturnWordCode hn hlp hp source jd).1 =
      (extractedPaddedReturnWordCode hn hlp hp u source.endpoint parent j).1 := by
  dsimp only
  let fullPath := trajectoryFrom source.start.1
    (extendStoppedWord source.bridge.1)
  let localPath := trajectoryFrom u.1 (extendStoppedWord parent.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let a := excursionFinish localPath outer inner parent.1.1 j
  let b := excursionStart localPath outer inner parent.1.1 (j + 1)
  have hab : a ≤ b := by
    exact excursionFinish_le_next_start localPath outer inner parent.1.1 j
  have hb : b ≤ parent.1.1 := by
    simpa only [b, localPath, outer, inner] using
      paddedParentReturnComplete hn hlp hp u source.endpoint parent j
  have hslice :
      incrementSlice (extendStoppedWord source.bridge.1)
        (excursionFinish fullPath outer inner source.bridge.1.1 j)
        (excursionStart fullPath outer inner source.bridge.1.1 (j + 1)) =
      incrementSlice (extendStoppedWord parent.1) a b := by
    rw [enteredSplit_excursionFinish_eq hn hlp hp source u first parent
      word_eq j.isLt]
    rw [enteredSplit_excursionStart_eq hn hlp hp source u first parent
      word_eq (by omega)]
    exact incrementSlice_extendStoppedWord_append_right first.1 parent.1
      source.bridge.1 word_eq hab hb
  calc
    (directPaddedReturnWordCode hn hlp hp source _).1 =
        listStoppedWord
          (List.ofFn (directPaddedReturnWordCode hn hlp hp source _).1.2) :=
      (listStoppedWord_ofFn _).symm
    _ = listStoppedWord
        (incrementSlice (extendStoppedWord source.bridge.1)
          (excursionFinish fullPath outer inner source.bridge.1.1 j)
          (excursionStart fullPath outer inner source.bridge.1.1 (j + 1))) := by
      rw [directPaddedReturnWordCode_toList]
    _ = listStoppedWord (incrementSlice (extendStoppedWord parent.1) a b) :=
      congrArg listStoppedWord hslice
    _ = listStoppedWord
        (List.ofFn
          (extractedPaddedReturnWordCode hn hlp hp u source.endpoint parent j).1.2) := by
      rw [extractedPaddedReturnWordCode_toList]
      simp only [intervalWords,
        AsymmetricSplitLevelSplice.extractTimedReturnSkeleton,
        AsymmetricSplitLevelSplice.returnEntranceTime,
        AsymmetricSplitLevelSplice.returnExitTime, a, b, localPath, outer, inner]
    _ = (extractedPaddedReturnWordCode hn hlp hp u source.endpoint parent j).1 :=
      listStoppedWord_ofFn _

def PaddedReturnDatum (n p : ℕ) (center : Point) :=
  Σ innerPoint : PaddedInnerPoint n p center,
    Σ middlePoint : PaddedMiddlePoint n p center,
      BoundaryExitWordCode (profileOuterBoundary n p center)
        innerPoint.1 middlePoint.1

def directPaddedReturnDatum
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (j : Fin (paddedBridgeReturnCount n l p center source.start.1
      source.endpoint.1 source.bridge)) : PaddedReturnDatum n p center :=
  ⟨directPaddedInnerPoint hn hlp hp source j,
    directPaddedMiddlePoint hn hlp hp source j,
    directPaddedReturnWordCode hn hlp hp source j⟩

def extractedPaddedReturnDatum
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q w.1)
    (j : Fin q) : PaddedReturnDatum n p center :=
  ⟨extractedPaddedInnerPoint u w parent j,
    extractedPaddedMiddlePoint hn hlp hp u w parent j.succ,
    extractedPaddedReturnWordCode hn hlp hp u w parent j⟩

theorem PaddedReturnDatum.ext
    {n p : ℕ} {center : Point} {left right : PaddedReturnDatum n p center}
    (hinner : left.1 = right.1)
    (hmiddle : left.2.1 = right.2.1)
    (hword : left.2.2.1 = right.2.2.1) : left = right := by
  rcases left with ⟨leftInner, leftMiddle, leftWord⟩
  rcases right with ⟨rightInner, rightMiddle, rightWord⟩
  dsimp only at hinner hmiddle hword
  subst rightInner
  subst rightMiddle
  congr
  exact Subtype.ext hword

theorem enteredSplit_returnDatum_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    (j : Fin q) :
    let hcount := enteredSplit_count_eq hn hlp hp source u first parent word_eq
    let jd : Fin (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge) := ⟨j, by rw [hcount]; exact j.isLt⟩
    directPaddedReturnDatum hn hlp hp source jd =
      extractedPaddedReturnDatum hn hlp hp u source.endpoint parent j := by
  dsimp only
  have hi := enteredSplit_innerPoint_eq hn hlp hp source u first parent word_eq j
  have hm := enteredSplit_middlePoint_eq hn hlp hp source u first parent word_eq j
  have hv := enteredSplit_returnWord_val_eq hn hlp hp source u first parent word_eq j
  dsimp only at hi hm hv
  apply PaddedReturnDatum.ext
  · simpa only [directPaddedReturnDatum, extractedPaddedReturnDatum] using hi
  · simpa only [directPaddedReturnDatum, extractedPaddedReturnDatum] using hm
  · simpa only [directPaddedReturnDatum, extractedPaddedReturnDatum] using hv

theorem enteredSplit_parsedTree_eq
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2)
    (j : Fin q) :
    let hcount := enteredSplit_count_eq hn hlp hp source u first parent word_eq
    let jd : Fin (paddedBridgeReturnCount n l p center source.start.1
        source.endpoint.1 source.bridge) := ⟨j, by rw [hcount]; exact j.isLt⟩
    (AnnularRecursiveBoundaryParser.parseBoundaryGap n center hn (n - p) p
      (by omega) (by omega)
      (directPaddedInnerPoint hn hlp hp source jd)
      (directPaddedMiddlePoint hn hlp hp source jd)
      (directPaddedReturnWordCode hn hlp hp source jd)).tree =
    (AnnularRecursiveBoundaryParser.parseBoundaryGap n center hn (n - p) p
      (by omega) (by omega)
      (extractedPaddedInnerPoint u source.endpoint parent j)
      (extractedPaddedMiddlePoint hn hlp hp u source.endpoint parent j.succ)
      (extractedPaddedReturnWordCode hn hlp hp u source.endpoint parent j)).tree := by
  dsimp only
  have hd := enteredSplit_returnDatum_eq hn hlp hp source u first parent word_eq j
  dsimp only at hd
  exact congrArg (fun datum : PaddedReturnDatum n p center ↦
    (AnnularRecursiveBoundaryParser.parseBoundaryGap n center hn (n - p) p
      (by omega) (by omega) datum.1 datum.2.1 datum.2.2).tree) hd

theorem directParsedPaddedBridgeTrees_eq_entered
    {n l p q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (u : PaddedMiddlePoint n p center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 u.1)
    (parent : BoundaryExcursionExitWordCode
      (profileInnerBoundary n l center)
      (profileInnerBoundary n (p - 1) center)
      (profileInnerBoundary n p center) u.1 q source.endpoint.1)
    (word_eq : List.ofFn first.1.2 ++ List.ofFn parent.1.2 =
      List.ofFn source.bridge.1.2) :
    directParsedPaddedBridgeTrees hn hlp hp source =
      AsymmetricPaddedCodeAssembly.finTreeList q fun j ↦
        (AnnularRecursiveBoundaryParser.parseBoundaryGap n center hn (n - p) p
          (by omega) (by omega)
          (extractedPaddedInnerPoint u source.endpoint parent j)
          (extractedPaddedMiddlePoint hn hlp hp u source.endpoint parent j.succ)
          (extractedPaddedReturnWordCode hn hlp hp u source.endpoint parent j)).tree := by
  let hcount := enteredSplit_count_eq hn hlp hp source u first parent word_eq
  unfold directParsedPaddedBridgeTrees
  rw [AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn,
    AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
  apply List.ext_get
  · simp only [List.length_ofFn, hcount]
  · intro k hk hk'
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn,
      List.getElem_ofFn]
    let j : Fin q := ⟨k, by simpa only [List.length_ofFn] using hk'⟩
    simpa only [j] using
      (enteredSplit_parsedTree_eq hn hlp hp source u first parent word_eq j)

theorem directSplit_count_eq_zero
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center)
    (first : BoundaryExitWordCode
      (profileInnerBoundary n (p - 1) center ∪
        profileInnerBoundary n l center) source.start.1 source.endpoint.1)
    (word_eq : first.1 = source.bridge.1) :
    paddedBridgeReturnCount n l p center source.start.1 source.endpoint.1
      source.bridge = 0 := by
  let s := trajectoryFrom source.start.1 (extendStoppedWord source.bridge.1)
  let outer := profileInnerBoundary n (p - 1) center
  let inner := profileInnerBoundary n p center
  let horizon := source.bridge.1.1
  have havoid : ∀ r ≤ horizon, s r ∉ outer := by
    intro r hr hmem
    by_cases hlt : r < horizon
    · apply first.2.1.2 r (by simpa only [horizon, word_eq] using hlt)
      exact Or.inl (by simpa only [s, outer, word_eq] using hmem)
    · have hre : r = horizon := by omega
      have hend : s horizon = source.endpoint.1 := by
        simpa only [s, horizon] using source.bridge.2.2
      exact Set.disjoint_left.mp
        (paddedRemoteRenewal_geometry hn hlp hp center).2.2.1
        (by simpa only [outer, hre, hend] using hmem)
        (by simpa only [profileInnerBoundary] using
          (mem_discBoundaryFinset.mp source.endpoint.2))
  have hdisjoint : Disjoint outer inner :=
    (paddedRemoteRenewal_geometry hn hlp hp center).1
  have hscan : scanThrough s outer inner horizon = initialState := by
    unfold scanThrough initialState
    exact scanSegment_seekingOuter_of_avoids s outer inner 0 (horizon + 1) 0
      (by
        intro r hr
        simpa only [Nat.zero_add] using havoid r (by omega))
  have hcount : completedExcursionCount s outer inner horizon = 0 := by
    rw [← scanThrough_completed_eq_completedExcursionCount s outer inner
      hdisjoint horizon, hscan]
    rfl
  simpa only [paddedBridgeReturnCount, boundaryExcursionCount,
    s, outer, inner, horizon] using hcount

theorem parsedPaddedBridgeTrees_eq_direct
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) :
    AsymmetricPaddedParsedBridgeCode.parsedPaddedBridgeTrees hn hlp hp source =
      directParsedPaddedBridgeTrees hn hlp hp source := by
  generalize hsplit : paddedPreludeSplit (p := p) source.start source.endpoint
    source.bridge = split
  cases split with
  | direct first word_eq =>
      simp only [AsymmetricPaddedParsedBridgeCode.parsedPaddedBridgeTrees,
        hsplit]
      unfold directParsedPaddedBridgeTrees
      symm
      rw [AsymmetricPaddedCodeAssembly.finTreeList_eq_ofFn]
      apply List.eq_nil_iff_length_eq_zero.mpr
      simpa only [List.length_ofFn] using
        (directSplit_count_eq_zero hn hlp hp source first word_eq)
  | entered u first q parent word_eq =>
      simp only [AsymmetricPaddedParsedBridgeCode.parsedPaddedBridgeTrees,
        hsplit]
      exact (directParsedPaddedBridgeTrees_eq_entered hn hlp hp source u first
        parent word_eq).symm

end

end Erdos1165.AsymmetricPaddedBridgeClock

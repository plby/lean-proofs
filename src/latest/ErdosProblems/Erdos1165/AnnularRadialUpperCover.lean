/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLinearUpper
import ErdosProblems.Erdos1165.AnnularRadialWordOfList
import ErdosProblems.Erdos1165.AnnularFixedProfileTraceParser
import ErdosProblems.Erdos1165.AnnularProfileClocks
import ErdosProblems.Erdos1165.AnnularProfileLiteralAtoms
import ErdosProblems.Erdos1165.TerminalSequentialVisitLaw

/-!
# The arbitrary-prefix linear radial upper cover

For an upper bound the spatial approach to the successful point must not be
charged by a selected lower-bound splice.  We instead retain the whole past
through the first level-one entrance following the first level-zero hit.  The
fresh future begins on the literal level-one boundary and ends at its first
return to level zero.  Thus the retained prefix has mass at most one and the
only nontrivial factor is one chronological radial word; there is no final
spatial factor and no nested product of overlapping stopped intervals.

This file first isolates the exact stopped-clock and Strong-Markov layer.  The
walk-facing trace classifier below is then used to instantiate the fresh event
by the bounded fixed-profile radial-word family.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AnnularRadialUpperCover

open AppendixFirstMoment Proposition13Assembly
open AnnularProfileClocks AnnularProfileLiteralAtoms
open AnnularRadialLabelWord AnnularRadialProfileWords
open AnnularRadialLinearUpper AnnularRadialWordOfList
open AnnularRadialOneStepRow AnnularFixedProfileTraceParser
open TerminalExcursionBridge TerminalSequentialVisitLaw
open ThickPoint BoundaryVisitRegeneration PlanarPotential

noncomputable section

/-- The outer boundary for the forced first profile coordinate `N_1 = 1`. -/
def levelOneOuterBoundary (n : ℕ) (x : Point) : Set Point :=
  radialBoundary n x ⟨0, by omega⟩

/-- The inner boundary for the forced first profile coordinate `N_1 = 1`. -/
def levelOneInnerBoundary (n : ℕ) (x : Point) : Set Point :=
  radialBoundary n x ⟨1, by omega⟩

/-- First level-one entrance after the first level-zero hit. -/
def firstLevelOneEntranceTime (n : ℕ) (x : Point) :
    StepPath → WithTop ℕ :=
  terminalEntranceTime zeroClock
    (levelOneOuterBoundary n x) (levelOneInnerBoundary n x) 0

/-- First return to level zero after `firstLevelOneEntranceTime`. -/
def firstLevelZeroReturnTime (n : ℕ) (x : Point) :
    StepPath → WithTop ℕ :=
  terminalExitTime zeroClock
    (levelOneOuterBoundary n x) (levelOneInnerBoundary n x) 0

theorem isStoppingTime_firstLevelOneEntranceTime (n : ℕ) (x : Point) :
    IsStoppingTime incrementFiltration (firstLevelOneEntranceTime n x) := by
  exact isStoppingTime_terminalEntranceTime isStoppingTime_zeroClock _ _ 0

private theorem levelOne_profileCompletedCount_eq_one
    {n horizon : ℕ} {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    profileCompletedCount (trajectory omega) n horizon x 1 = 1 := by
  rw [← excursionProfile_eq_profileCompletedCount
    (trajectory omega) n horizon x (by omega) (by omega)]
  exact hfixed.1

/-- On a fixed successful profile, the unique level-one excursion is
complete and its following return to level zero occurs before global exit. -/
theorem levelOne_return_le_horizon_of_fixedProfile
    {n horizon : ℕ} (hn : 1 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    profileGapExitTime (trajectory omega) n horizon x 1 0 ≤ horizon := by
  apply profileGapExitTime_le_of_globalExit hn (by omega) hn hexit hx
    (fun q ↦ Proposition13Assembly.adjacent_trajectory_succ omega q)
  apply profileInnerHitTime_le_horizon_of_lt_count
  rw [levelOne_profileCompletedCount_eq_one hfixed]
  omega

/-- The unbounded first level-one entrance is the literal finite completion
clock of the unique level-one excursion. -/
theorem firstLevelOneEntranceTime_eq_profileInnerHitTime
    {n horizon : ℕ} (hn : 1 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    firstLevelOneEntranceTime n x omega =
      profileInnerHitTime (trajectory omega) n horizon x 1 0 := by
  classical
  have hreturn := levelOne_return_le_horizon_of_fixedProfile hn hexit hx hfixed
  have houter : levelOneOuterBoundary n x = profileOuterBoundary n 1 x := by
    ext z
    simp [levelOneOuterBoundary, radialBoundary, profileOuterBoundary]
  have hinner : levelOneInnerBoundary n x = profileInnerBoundary n 1 x := by
    rfl
  rw [firstLevelOneEntranceTime, houter, hinner]
  change terminalEntranceTime zeroClock (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) 0 omega =
    excursionFinish (trajectory omega) (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) horizon 0
  exact terminalEntranceTime_eq_excursionFinish omega
    (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x)
    horizon 0 hreturn

/-- The unbounded following level-zero return is the literal finite return
clock of the unique level-one excursion. -/
theorem firstLevelZeroReturnTime_eq_profileGapExitTime
    {n horizon : ℕ} (hn : 1 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    firstLevelZeroReturnTime n x omega =
      profileGapExitTime (trajectory omega) n horizon x 1 0 := by
  classical
  have hreturn := levelOne_return_le_horizon_of_fixedProfile hn hexit hx hfixed
  have houter : levelOneOuterBoundary n x = profileOuterBoundary n 1 x := by
    ext z
    simp [levelOneOuterBoundary, radialBoundary, profileOuterBoundary]
  have hinner : levelOneInnerBoundary n x = profileInnerBoundary n 1 x := by
    rfl
  rw [firstLevelZeroReturnTime, houter, hinner]
  change terminalExitTime zeroClock (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) 0 omega =
    excursionStart (trajectory omega) (profileOuterBoundary n 1 x)
      (profileInnerBoundary n 1 x) horizon 1
  exact terminalExitTime_eq_excursionStart omega
    (profileOuterBoundary n 1 x) (profileInnerBoundary n 1 x)
    horizon 0 hreturn

/-- The random entrance point really lies on the level-one boundary on every
fixed successful path. -/
theorem stoppedPosition_firstLevelOneEntrance_mem
    {n horizon : ℕ} (hn : 1 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    stoppedPosition (firstLevelOneEntranceTime n x) omega ∈
      levelOneInnerBoundary n x := by
  have hclock := firstLevelOneEntranceTime_eq_profileInnerHitTime
    hn hexit hx hfixed
  have hinner : profileInnerHitTime (trajectory omega) n horizon x 1 0 ≤
      horizon :=
    (profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x 1 0).trans
      (levelOne_return_le_horizon_of_fixedProfile hn hexit hx hfixed)
  rw [stoppedPosition_eq_of_eq hclock]
  simpa [levelOneInnerBoundary, profileInnerBoundary, radialBoundary] using
    profileInnerHit_mem_of_le hinner

/-- After the first level-one entrance, the following level-zero return is
literally the first hit of level zero by the fresh post-stopping path. -/
theorem firstLevelOne_fresh_firstLevelZero
    {n horizon : ℕ} (hn : 1 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    ∃ duration : ℕ,
      AbsoluteBoundaryFirstAt (levelOneOuterBoundary n x)
        (stoppedPosition (firstLevelOneEntranceTime n x) omega)
        (postWithTopStoppingSteps (firstLevelOneEntranceTime n x) omega)
        duration := by
  classical
  let t := profileInnerHitTime (trajectory omega) n horizon x 1 0
  let u := profileGapExitTime (trajectory omega) n horizon x 1 0
  have ht : firstLevelOneEntranceTime n x omega = t :=
    firstLevelOneEntranceTime_eq_profileInnerHitTime hn hexit hx hfixed
  have hu : firstLevelZeroReturnTime n x omega = u :=
    firstLevelZeroReturnTime_eq_profileGapExitTime hn hexit hx hfixed
  have hfirstEq : firstHitSetAfter (firstLevelOneEntranceTime n x)
      (levelOneOuterBoundary n x) omega = u := by
    change firstHitSetAfter
      (terminalEntranceTime zeroClock (levelOneOuterBoundary n x)
        (levelOneInnerBoundary n x) 0)
      (levelOneOuterBoundary n x) omega = u
    rw [← terminalExitTime_eq_firstHitSetAfter
      (levelOneOuterBoundary n x) (levelOneInnerBoundary n x) 0]
    unfold firstLevelZeroReturnTime at hu
    exact hu
  have hfresh : AbsoluteBoundaryFirstAt (levelOneOuterBoundary n x)
      (stoppedPosition (firstLevelOneEntranceTime n x) omega)
      (postWithTopStoppingSteps (firstLevelOneEntranceTime n x) omega)
      (u - t) := by
    exact absoluteBoundaryFirstAt_post_firstHitSetAfter ht hfirstEq
  exact ⟨u - t, hfresh⟩

/-- Exact-duration form of `firstLevelOne_fresh_firstLevelZero`.  This is the
form consumed by the fixed-profile classifier, whose fresh profile is
measured through the literal first level-one gap length. -/
theorem firstLevelOne_fresh_firstLevelZero_profileGapLength
    {n horizon : ℕ} (hn : 1 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    {omega : StepPath}
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : FixedSuccessfulProfile n delta m
      (excursionProfile (trajectory omega) n horizon x)) :
    AbsoluteBoundaryFirstAt (levelOneOuterBoundary n x)
      (stoppedPosition (firstLevelOneEntranceTime n x) omega)
      (postWithTopStoppingSteps (firstLevelOneEntranceTime n x) omega)
      (AnnularProfileGapAtoms.profileGapLength omega n horizon x 1 0) := by
  classical
  let t := profileInnerHitTime (trajectory omega) n horizon x 1 0
  let u := profileGapExitTime (trajectory omega) n horizon x 1 0
  have ht : firstLevelOneEntranceTime n x omega = t :=
    firstLevelOneEntranceTime_eq_profileInnerHitTime hn hexit hx hfixed
  have hu : firstLevelZeroReturnTime n x omega = u :=
    firstLevelZeroReturnTime_eq_profileGapExitTime hn hexit hx hfixed
  have hfirstEq : firstHitSetAfter (firstLevelOneEntranceTime n x)
      (levelOneOuterBoundary n x) omega = u := by
    change firstHitSetAfter
      (terminalEntranceTime zeroClock (levelOneOuterBoundary n x)
        (levelOneInnerBoundary n x) 0)
      (levelOneOuterBoundary n x) omega = u
    rw [← terminalExitTime_eq_firstHitSetAfter
      (levelOneOuterBoundary n x) (levelOneInnerBoundary n x) 0]
    unfold firstLevelZeroReturnTime at hu
    exact hu
  have hfresh : AbsoluteBoundaryFirstAt (levelOneOuterBoundary n x)
      (stoppedPosition (firstLevelOneEntranceTime n x) omega)
      (postWithTopStoppingSteps (firstLevelOneEntranceTime n x) omega)
      (u - t) :=
    absoluteBoundaryFirstAt_post_firstHitSetAfter ht hfirstEq
  simpa [AnnularProfileGapAtoms.profileGapLength, t, u] using hfresh

/-! ## Structural facts about the fresh chronological scan -/

private theorem compressLabels_head?_eq_some
    {Label : Type*} [DecidableEq Label] (label : Label) (tail : List Label) :
    (compressLabels (label :: tail)).head? = some label := by
  simp [compressLabels, compressLabelsFrom]

/-- A chronological scan whose time-zero point lies on one radial boundary
starts with precisely that boundary label. -/
theorem chronologicalRadialLabels_head?_eq_of_start_mem
    {n horizon : ℕ} (hn : 2 ≤ n) {center start : Point}
    {label : Fin (n + 2)} {omega : StepPath}
    (hstart : start ∈ radialBoundary n center label) :
    (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).head? = some label := by
  have hzero : radialLabelsAt n center
      (trajectoryFrom start omega 0) = [label] := by
    simpa using radialLabelsAt_eq_singleton_of_mem hn center start label hstart
  unfold chronologicalRadialLabels observedRadialLabels
  rw [List.range_succ_eq_map]
  simp only [List.flatMap_cons, Nat.zero_eq, hzero, List.singleton_append]
  exact compressLabels_head?_eq_some label _

private theorem compressLabelsFrom_append_singleton_getLast?
    {Label : Type*} [DecidableEq Label] (final : Label) :
    ∀ (xs : List Label) (previous : Option Label),
      final ∉ xs → previous ≠ some final →
      (compressLabelsFrom previous (xs ++ [final])).getLast? = some final := by
  intro xs
  induction xs with
  | nil =>
      intro previous _ hprevious
      simp [compressLabelsFrom, hprevious]
  | cons label tail ih =>
      intro previous hnotmem hprevious
      have hlabel : label ≠ final := by
        intro heq
        apply hnotmem
        simp [heq]
      have htail : final ∉ tail := by
        intro hmem
        exact hnotmem (by simp [hmem])
      rw [List.cons_append, compressLabelsFrom]
      by_cases heq : previous = some label
      · rw [if_pos heq]
        exact ih previous htail hprevious
      · rw [if_neg heq]
        have hnext : (some label : Option Label) ≠ some final := by
          simpa using hlabel
        rw [List.getLast?_cons_of_ne_nil (by
          intro hempty
          have := ih (some label) htail hnext
          rw [hempty] at this
          simp at this)]
        exact ih (some label) htail hnext

/-- If `horizon` is the first hit of a radial boundary, the chronological
scan through `horizon` ends with the corresponding label. -/
theorem chronologicalRadialLabels_getLast?_eq_of_first
    {n horizon : ℕ} (hn : 2 ≤ n) {center start : Point}
    {label : Fin (n + 2)} {omega : StepPath}
    (hfirst : AbsoluteBoundaryFirstAt (radialBoundary n center label)
      start omega horizon) :
    (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).getLast? = some label := by
  have hfinal : radialLabelsAt n center
      (trajectoryFrom start omega horizon) = [label] := by
    apply radialLabelsAt_eq_singleton_of_mem hn
    exact hfirst.1
  let xs : List (Fin (n + 2)) :=
    (List.range horizon).flatMap
      (fun t ↦ radialLabelsAt n center (trajectoryFrom start omega t))
  have hlabelNot : label ∉ xs := by
    intro hmem
    obtain ⟨q, hqRange, hqLabel⟩ := List.mem_flatMap.mp hmem
    have hq : q < horizon := List.mem_range.mp hqRange
    exact hfirst.2 q hq (mem_radialLabelsAt.mp hqLabel)
  unfold chronologicalRadialLabels observedRadialLabels
  rw [List.range_succ, List.flatMap_append]
  simp only [List.flatMap_singleton, hfinal]
  change (compressLabels (xs ++ [label])).getLast? = some label
  unfold compressLabels
  exact compressLabelsFrom_append_singleton_getLast? label xs none
    hlabelNot (by simp)

private theorem compressLabelsFrom_head_ne_of_some
    {Label : Type*} [DecidableEq Label] (previous : Label) :
    ∀ (labels : List Label) (head : Label),
      (compressLabelsFrom (some previous) labels).head? = some head →
      head ≠ previous := by
  intro labels
  induction labels with
  | nil => simp [compressLabelsFrom]
  | cons label tail ih =>
      intro head hhead
      rw [compressLabelsFrom] at hhead
      by_cases heq : (some previous : Option Label) = some label
      · rw [if_pos heq] at hhead
        exact ih head hhead
      · rw [if_neg heq] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst head
        exact fun h ↦ heq (congrArg some h.symm)

private theorem compressLabelsFrom_isChain_ne
    {Label : Type*} [DecidableEq Label] :
    ∀ (previous : Option Label) (labels : List Label),
      (compressLabelsFrom previous labels).IsChain (fun left right ↦ left ≠ right) := by
  intro previous labels
  induction labels generalizing previous with
  | nil => simp [compressLabelsFrom]
  | cons label tail ih =>
      rw [compressLabelsFrom]
      by_cases heq : previous = some label
      · rw [if_pos heq]
        exact ih previous
      · rw [if_neg heq]
        have htailChain := ih (some label)
        cases hcompressed : compressLabelsFrom (some label) tail with
        | nil => simp
        | cons next rest =>
            rw [hcompressed] at htailChain
            apply List.isChain_cons_cons.mpr
            refine ⟨?_, htailChain⟩
            exact (compressLabelsFrom_head_ne_of_some label tail next (by
              rw [hcompressed]
              rfl)).symm

/-- Consecutive emitted labels in the chronological scan are distinct. -/
theorem chronologicalRadialLabels_isChain_ne
    (n : ℕ) (center : Point) (s : WalkPath) (horizon : ℕ) :
    (chronologicalRadialLabels n center s horizon).IsChain
      (fun left right ↦ left ≠ right) := by
  unfold chronologicalRadialLabels compressLabels
  exact compressLabelsFrom_isChain_ne none _

/-- The first different radial boundary hit from a positive label must be
one of its adjacent labels.  This is the geometric fact which turns the
compressed chronological scan into a nearest-neighbour label word. -/
theorem firstDifferentRadialLabel_adjacent
    {n t : ℕ} (hn : 2 ≤ n) {center start : Point}
    {source target : Fin (n + 2)} {omega : StepPath}
    (hsource : (source : ℕ) ≠ 0)
    (hstart : start ∈ radialBoundary n center source)
    (hfirst : AbsoluteBoundaryFirstAt
      (otherRadialBoundaries n center source) start omega t)
    (htarget : trajectoryFrom start omega t ∈
      radialBoundary n center target) :
    Nat.dist (source : ℕ) (target : ℕ) = 1 := by
  have htime := MarkedBoundaryVisitKernel.boundaryExitTime_eq_of_absoluteBoundaryFirstAt
    hfirst
  have hsourceBound : (source : ℕ) ≤ n + 1 := by omega
  by_cases hterminal : (source : ℕ) = n + 1
  · have hsourceTerminalEq : source = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      exact hterminal
    rw [hsourceTerminalEq] at htime
    have hclock : MarkedBoundaryVisitKernel.boundaryExitTime
        (radialBoundary n center ⟨n, by omega⟩) start omega = t := by
      rw [← boundaryExitTime_otherRadialBoundaries_terminal_eq
        hn center start (by simpa [radialBoundary, hterminal] using hstart)]
      exact htime
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (BoundaryVisitLaw.relativeBoundary
        (radialBoundary n center ⟨n, by omega⟩) start) omega t).mp hclock
    have hbarrier : trajectoryFrom start omega t ∈
        radialBoundary n center ⟨n, by omega⟩ := by
      simpa [BoundaryVisitLaw.relativeBoundary, trajectoryFrom] using hspec.2.1
    have htargetEq : target = ⟨n, by omega⟩ := by
      by_contra hne
      exact Set.disjoint_left.mp
        (radialBoundaries_disjoint_of_ne hn center hne)
          htarget hbarrier
    subst target
    change Nat.dist (source : ℕ) n = 1
    rw [hterminal]
    simp only [Nat.dist]
    omega
  · have hsourceLe : (source : ℕ) ≤ n := by omega
    let k : ℕ := source
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hsourceEq : source = ⟨k, by omega⟩ := by
      apply Fin.ext
      rfl
    have hstart' : start ∈ discBoundary center (scaleRadius n k) := by
      simpa [radialBoundary, hsourceEq] using hstart
    have hclock : MarkedBoundaryVisitKernel.boundaryExitTime
        (adjacentRadialBoundaries n k center) start omega = t := by
      rw [← boundaryExitTime_otherRadialBoundaries_eq_adjacent
        hn hk hsourceLe center start hstart']
      simpa [hsourceEq] using htime
    have hspec := (firstHitSetAfter_eq_coe_iff zeroClock
      (BoundaryVisitLaw.relativeBoundary
        (adjacentRadialBoundaries n k center) start) omega t).mp hclock
    have hbarrier : trajectoryFrom start omega t ∈
        adjacentRadialBoundaries n k center := by
      simpa [BoundaryVisitLaw.relativeBoundary, trajectoryFrom] using hspec.2.1
    rcases hbarrier with hinner | houter
    · have htargetEq : target = ⟨k + 1, by omega⟩ := by
        by_contra hne
        exact Set.disjoint_left.mp
          (radialBoundaries_disjoint_of_ne hn center hne)
            htarget (by simpa [adjacentRadialBoundaries, radialBoundary] using hinner)
      subst target
      change Nat.dist (source : ℕ) (k + 1) = 1
      dsimp [k]
      simp only [Nat.dist]
      omega
    · have htargetEq : target = ⟨k - 1, by omega⟩ := by
        by_contra hne
        exact Set.disjoint_left.mp
          (radialBoundaries_disjoint_of_ne hn center hne)
            htarget (by simpa [adjacentRadialBoundaries, radialBoundary] using houter)
      subst target
      change Nat.dist (source : ℕ) (k - 1) = 1
      dsimp [k]
      simp only [Nat.dist]
      omega

private theorem chronologicalRadialLabels_isChain_adjacent_aux
    {n horizon : ℕ} (hn : 2 ≤ n) {center start : Point}
    {source : Fin (n + 2)} {tail : List (Fin (n + 2))} {omega : StepPath}
    (hstart : start ∈ radialBoundary n center source)
    (htrace : chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon = source :: tail)
    (hbefore : ∀ i
      (hi : i < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length),
      i + 1 < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length →
      ((chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon)[i]'hi : ℕ) ≠ 0)
    : (source :: tail).IsChain
        (fun left right ↦ Nat.dist left.val right.val = 1) := by
  induction tail generalizing start source omega horizon with
  | nil => exact List.isChain_singleton source
  | cons target rest ih =>
      rw [htrace] at hbefore
      have hsourceNonzero : (source : ℕ) ≠ 0 := by
        exact hbefore 0 (by simp) (by simp)
      have hne : source ≠ target :=
        (List.isChain_cons_cons.mp
          (show (source :: target :: rest).IsChain
              (fun left right ↦ left ≠ right) from
            htrace ▸ chronologicalRadialLabels_isChain_ne n center
              (fun q ↦ trajectoryFrom start omega q) horizon)).1
      obtain ⟨t, ht, hfirst, htarget, htailTrace⟩ :=
        chronologicalRadialLabels_unsplice_firstDifferent
          hn center start source target omega rest hne hstart htrace
      have hadjacent := firstDifferentRadialLabel_adjacent hn hsourceNonzero
        hstart hfirst htarget
      apply List.isChain_cons_cons.mpr
      refine ⟨hadjacent, ?_⟩
      apply ih (start := trajectoryFrom start omega t)
        (omega := shiftSteps t omega) (horizon := horizon - t)
      · exact htarget
      · exact htailTrace
      · intro i hi hilast
        have hiTail : i < (target :: rest).length := by
          rw [← htailTrace]
          exact hi
        have hilastTail : i + 1 < (target :: rest).length := by
          rw [← htailTrace]
          exact hilast
        have hiSource : i + 1 < (source :: target :: rest).length := by
          simp only [List.length_cons]
          simp only [List.length_cons] at hiTail
          omega
        have hilastSource : (i + 1) + 1 <
            (source :: target :: rest).length := by
          simp only [List.length_cons]
          simp only [List.length_cons] at hilastTail
          omega
        have h := hbefore (i + 1) hiSource hilastSource
        have htailNonzero :
            (((target :: rest)[i]'hiTail : Fin (n + 2)) : ℕ) ≠ 0 := by
          simpa using h
        have hget := getElem_congr_coll htailTrace (i := i) (w := hi)
        rw [hget]
        exact htailNonzero

/-- Every consecutive pair in a chronological scan is adjacent, provided
zero occurs only as the last emitted label. -/
theorem chronologicalRadialLabels_isChain_adjacent
    {n horizon : ℕ} (hn : 2 ≤ n) {center start : Point}
    {source : Fin (n + 2)} {omega : StepPath}
    (hstart : start ∈ radialBoundary n center source)
    (hbefore : ∀ i
      (hi : i < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length),
      i + 1 < (chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon).length →
      ((chronologicalRadialLabels n center
        (fun q ↦ trajectoryFrom start omega q) horizon)[i]'hi : ℕ) ≠ 0)
    (hhead : (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).head? = some source) :
    (chronologicalRadialLabels n center
      (fun q ↦ trajectoryFrom start omega q) horizon).IsChain
        (fun left right ↦ Nat.dist left.val right.val = 1) := by
  obtain ⟨tail, htrace⟩ := List.head?_eq_some_iff.mp hhead
  rw [htrace]
  exact chronologicalRadialLabels_isChain_adjacent_aux hn hstart htrace hbefore

/-- Restart event with an arbitrary retained prefix and a fresh event chosen
from the random level-one entrance point. -/
def firstLevelOneRestartEvent
    (n : ℕ) (x : Point) (K : Point → Set StepPath) : Set StepPath :=
  {omega | firstLevelOneEntranceTime n x omega < ⊤ ∧
    postWithTopStoppingSteps (firstLevelOneEntranceTime n x) omega ∈
      K (stoppedPosition (firstLevelOneEntranceTime n x) omega)}

/-- Strong Markov at the actual first level-one entrance.  The whole prefix
is retained with mass at most one; only the fresh suffix pays `upper`. -/
theorem fairSteps_firstLevelOneRestartEvent_le
    {n : ℕ} {x : Point} {K : Point → Set StepPath} {upper : ℝ≥0∞}
    (hK : ∀ z, MeasurableSet (K z))
    (hupper : ∀ z ∈ levelOneInnerBoundary n x, fairSteps (K z) ≤ upper) :
    fairSteps (firstLevelOneRestartEvent n x K) ≤ upper := by
  let tau := firstLevelOneEntranceTime n x
  have hU : IsMeasurableAtWithTopStopping tau (Set.univ : Set StepPath) := by
    intro N
    simpa using (isStoppingTime_firstLevelOneEntranceTime n x).measurableSet_eq N
  have hsupport : ∀ omega, omega ∈ (Set.univ : Set StepPath) →
      tau omega < ⊤ → stoppedPosition tau omega ∈ levelOneInnerBoundary n x := by
    intro omega _homega hfinite
    have hne : tau omega ≠ ⊤ := ne_top_of_lt hfinite
    lift tau omega to ℕ using hne with N hN
    rw [stoppedPosition_eq_of_eq hN.symm]
    apply terminalEntranceTime_mem_inner_of_eq
    simpa [tau, firstLevelOneEntranceTime] using hN.symm
  have hmarkov := strongMarkov_withTop_stoppedPosition_bounds_on
    (isStoppingTime_firstLevelOneEntranceTime n x)
    hU
    (levelOneInnerBoundary n x)
    hsupport
    K hK 0 upper (fun z hz ↦ ⟨bot_le, hupper z hz⟩)
  have hevent : firstLevelOneRestartEvent n x K =
      {omega | omega ∈ (Set.univ : Set StepPath) ∧ tau omega < ⊤ ∧
        postWithTopStoppingSteps tau omega ∈ K (stoppedPosition tau omega)} := by
    ext omega
    simp [firstLevelOneRestartEvent, tau]
  rw [hevent]
  calc
    fairSteps _ ≤ fairSteps ((Set.univ : Set StepPath) ∩
        {omega | tau omega < ⊤}) * upper := hmarkov.2
    _ = upper * fairSteps ((Set.univ : Set StepPath) ∩
        {omega | tau omega < ⊤}) := mul_comm _ _
    _ ≤ upper * 1 := mul_le_mul_right prob_le_one upper
    _ = 1 * upper := mul_comm _ _
    _ = upper := one_mul upper

end

end Erdos1165.AnnularRadialUpperCover

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualHangingStage

/-!
# Split target components for equal auxiliary routes

An equal-index route ends at a ladder marker born at its source stage.
That marker is the initial vertex of a unique essential limiting component.
Split legality suffices for this continuation argument and for proving that
the component is hanging.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

variable {kappa : Cardinal.{u}}

private abbrev SplitTargetInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- The exact limiting component beginning at the target marker of a
split equal-index route. -/
structure SplitEqualTargetComponent
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (SplitTargetInput L hL).lambda
      (SplitTargetInput L hL).lambda.target)
    (p : FinitePath (SplitTargetInput L hL).lambda.graph)
    (hp : p ∈ ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths) where
  marker : (SplitTargetInput L hL).targetMarkers
  finish_eq : p.finish = .old marker.1
  sourceIndex : Ladder.Stage kappa
  sourceIndex_eq :
    (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start,
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
            hp⟩ = sourceIndex
  markerStage_eq : L.markerStage ⟨marker.1, marker.2.1⟩ = sourceIndex
  component : Gamma.DPath
  component_essential : component ∈ Gamma.essentialWarpPart L.limitWarp
  marker_mem_support : marker.1 ∈ component.support
  component_initial_eq : component.initial = marker.1
  component_hanging : PopularAuxiliary.IsHangingPath Gamma component
  ownerStage_eq :
    L.splitHangingComponentStage hL.legal component component_essential.1
        component_hanging = sourceIndex

/-- A split ladder marker is outside the original source. -/
theorem splitMarker_not_mem_source
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∉ Gamma.source := by
  intro hySource
  apply L.splitMarker_not_mem_roof_frontier hlegal hy
  rw [L.frontier_eq_essential_terminalFrontier
    hlegal.roofsSourceAtStages, Gamma.roof_essential]
  exact hlegal.roofsSourceAtStages (Ladder.Stage.toExtended a) hySource

/-- A marker lying on a final limiting component is its initial vertex,
under split legality. -/
theorem IsSplitLegal.initial_eq_of_splitMarker_mem_limitWarp_support
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp) (hyp : y ∈ p.support) :
    p.initial = y := by
  have htrivialSuccessor : Gamma.trivialPath y ∈ L.successorWarp a :=
    (hlegal.freshMarkers.2 a y hy).2
  have htrivialStage : Gamma.trivialPath y ∈
      L.warpAt (L.splitSuccessorStage hlegal a) := by
    simpa only [L.warpAt_splitSuccessorStage hlegal] using htrivialSuccessor
  have hmeet : ((Gamma.trivialPath y).support ∩ p.support).Nonempty :=
    ⟨y, by simp, hyp⟩
  have hext : Gamma.Extends (Gamma.trivialPath y) p :=
    hlegal.extends_limitWarp_of_stage_intersects htrivialStage hp hmeet
  have hinitial := Gamma.extends_initial hext
  simpa using hinitial.symm

/-- Target-marker specialization of the split marker continuation lemma. -/
theorem IsSplitLegal.initial_eq_of_splitTargetMarker_mem_limitWarp_support
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    {y : V} (hy : y ∈
      (L.splitPopularAuxiliaryInput hlegal).targetMarkers)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp) (hyp : y ∈ p.support) :
    p.initial = y := by
  obtain ⟨a, ha⟩ := hy.1
  exact hlegal.initial_eq_of_splitMarker_mem_limitWarp_support ha hp hyp

/-- An equal split route starts at a finite record or an infinite proxy and
ends at a marker having exactly the same stage. -/
theorem splitEqualSubwarp_path_sameStage
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (SplitTargetInput L hL).lambda
      (SplitTargetInput L hL).lambda.target)
    {p : FinitePath (SplitTargetInput L hL).lambda.graph}
    (hp : p ∈ ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths) :
    (∃ (x : L.finiteTerminalSet)
      (y : (SplitTargetInput L hL).targetMarkers),
      p.start = .old x.1 ∧ p.finish = .old y.1 ∧
      L.markerStage ⟨y.1, y.2.1⟩ = L.finiteTerminalStage x) ∨
    (∃ (i : L.splitInfiniteRecords)
      (y : (SplitTargetInput L hL).targetMarkers),
      p.start = .proxy i ∧ p.finish = .old y.1 ∧
      L.markerStage ⟨y.1, y.2.1⟩ = L.splitInfiniteStage i) := by
  let I := SplitTargetInput L hL
  let U := L.splitPopularAuxiliaryIndexed hL
  have hpSource : p.start ∈ I.lambda.source :=
    (U.equalSubwarp P).starts_in_source hp
  have hpTarget : p.finish ∈ I.lambda.target :=
    (U.equalSubwarp P).ends_in_target hp
  have hindex := U.equalSubwarp_index_eq P hp
  obtain ⟨y, hyTarget, hfinish⟩ := I.finish_of_mem_lambda_target p hpTarget
  let ys : I.targetMarkers := ⟨y, hyTarget⟩
  rcases I.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · left
    let xs : L.finiteTerminalSet := ⟨x, hxFinite⟩
    refine ⟨xs, ys, hstart, hfinish, ?_⟩
    have hs :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
          U.f ⟨.old x, (I.mem_lambda_source_old x).2 hxFinite⟩ := by
      apply congrArg U.f
      exact Subtype.ext hstart
    have ht :
        U.g ⟨p.finish, (U.equalSubwarp P).ends_in_target hp⟩ =
          U.g ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
      apply congrArg U.g
      exact Subtype.ext hfinish
    exact ht.symm.trans (hindex.trans hs)
  · right
    refine ⟨i, ys, hstart, hfinish, ?_⟩
    have hs :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
          U.f ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := by
      apply congrArg U.f
      exact Subtype.ext hstart
    have ht :
        U.g ⟨p.finish, (U.equalSubwarp P).ends_in_target hp⟩ =
          U.g ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
      apply congrArg U.g
      exact Subtype.ext hfinish
    exact ht.symm.trans (hindex.trans hs)

/-- Every equal split route canonically determines its essential hanging
target component. -/
theorem exists_splitEqualTargetComponent
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (SplitTargetInput L hL).lambda
      (SplitTargetInput L hL).lambda.target)
    (p : FinitePath (SplitTargetInput L hL).lambda.graph)
    (hp : p ∈ ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths) :
    Nonempty (L.SplitEqualTargetComponent hL P p hp) := by
  let I := SplitTargetInput L hL
  let U := L.splitPopularAuxiliaryIndexed hL
  rcases L.splitEqualSubwarp_path_sameStage hL P hp with
      ⟨x, y, _hstart, hfinish, hstage⟩ |
      ⟨i, y, _hstart, hfinish, hstage⟩
  · have hyVertex : y.1 ∈ Gamma.vertexSet I.essentialLadder := y.2.2
    obtain ⟨Y, hYessential, hyY⟩ := (Gamma.mem_vertexSet).1 hyVertex
    have hYessential' : Y ∈ Gamma.essentialWarpPart L.limitWarp := by
      simpa only [I, SplitTargetInput, KappaLadder.splitPopularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder] using hYessential
    have hYinitial : Y.initial = y.1 :=
      hL.legal.initial_eq_of_splitTargetMarker_mem_limitWarp_support
        y.2 hYessential'.1 hyY
    have hYhanging : PopularAuxiliary.IsHangingPath Gamma Y := by
      rw [PopularAuxiliary.IsHangingPath, hYinitial]
      exact L.splitMarker_not_mem_source hL.legal
        (L.markerStage_spec ⟨y.1, y.2.1⟩)
    let a := L.finiteTerminalStage x
    have hsource :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ = a := by
      have heq :
          (⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ :
              I.lambda.source) =
            ⟨.old x.1, (I.mem_lambda_source_old x.1).2 x.2⟩ :=
        Subtype.ext _hstart
      rw [heq]
      rfl
    have howner :
        L.splitHangingComponentStage hL.legal Y hYessential'.1 hYhanging =
          a := by
      apply hL.legal.markersInjective
      · exact L.marker_splitHangingComponentStage hL.legal Y
          hYessential'.1 hYhanging
      · change L.marker (L.finiteTerminalStage x) = some Y.initial
        rw [hYinitial, ← hstage]
        exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact ⟨{
      marker := y
      finish_eq := hfinish
      sourceIndex := a
      sourceIndex_eq := hsource
      markerStage_eq := hstage
      component := Y
      component_essential := hYessential'
      marker_mem_support := hyY
      component_initial_eq := hYinitial
      component_hanging := hYhanging
      ownerStage_eq := howner }⟩
  · have hyVertex : y.1 ∈ Gamma.vertexSet I.essentialLadder := y.2.2
    obtain ⟨Y, hYessential, hyY⟩ := (Gamma.mem_vertexSet).1 hyVertex
    have hYessential' : Y ∈ Gamma.essentialWarpPart L.limitWarp := by
      simpa only [I, SplitTargetInput, KappaLadder.splitPopularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder] using hYessential
    have hYinitial : Y.initial = y.1 :=
      hL.legal.initial_eq_of_splitTargetMarker_mem_limitWarp_support
        y.2 hYessential'.1 hyY
    have hYhanging : PopularAuxiliary.IsHangingPath Gamma Y := by
      rw [PopularAuxiliary.IsHangingPath, hYinitial]
      exact L.splitMarker_not_mem_source hL.legal
        (L.markerStage_spec ⟨y.1, y.2.1⟩)
    let a := L.splitInfiniteStage i
    have hsource :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ = a := by
      have heq :
          (⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ :
              I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
        Subtype.ext _hstart
      rw [heq]
      rfl
    have howner :
        L.splitHangingComponentStage hL.legal Y hYessential'.1 hYhanging =
          a := by
      apply hL.legal.markersInjective
      · exact L.marker_splitHangingComponentStage hL.legal Y
          hYessential'.1 hYhanging
      · change L.marker (L.splitInfiniteStage i) = some Y.initial
        rw [hYinitial, ← hstage]
        exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact ⟨{
      marker := y
      finish_eq := hfinish
      sourceIndex := a
      sourceIndex_eq := hsource
      markerStage_eq := hstage
      component := Y
      component_essential := hYessential'
      marker_mem_support := hyY
      component_initial_eq := hYinitial
      component_hanging := hYhanging
      ownerStage_eq := howner }⟩

end DWeb.KappaLadder
end Erdos599

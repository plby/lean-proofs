/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalRouteContact
import ErdosProblems.Erdos599.GroundingIndexDichotomy

/-!
# The limiting component owned by an equal-route target marker

Every target of the auxiliary web is a ladder marker which lies on the
essential part of the limiting ladder.  Marker continuation and final-warp
disjointness show that this marker is the initial vertex of the unique
limiting component containing it.  Freshness makes that initial vertex an
original non-source, so the component is genuinely hanging.  For an
equal-index route its owner stage is exactly the route's source index.

This is the sound ambient splice point for the equal branch.  It keeps the
limiting component geometry which is lost by reducing merely to the set of
exceptional stages.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The exact essential limiting component which starts at the target marker
of one member of an equal-index auxiliary subwarp. -/
structure EqualTargetComponent
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths) where
  marker : (L.popularAuxiliaryInput hL.legal).targetMarkers
  finish_eq : p.finish = .old marker.1
  sourceIndex : Stage kappa
  sourceIndex_eq :
    (L.popularAuxiliaryIndexed hL).f
        ⟨p.start,
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
            hp⟩ = sourceIndex
  markerStage_eq : L.markerStage ⟨marker.1, marker.2.1⟩ = sourceIndex
  component : Gamma.DPath
  component_essential : component ∈ Gamma.essentialWarpPart L.limitWarp
  marker_mem_support : marker.1 ∈ component.support
  component_initial_eq : component.initial = marker.1
  component_hanging : PopularAuxiliary.IsHangingPath Gamma component
  ownerStage_eq :
    L.hangingComponentStage hL.legal component component_essential.1
        component_hanging = sourceIndex

/-- A ladder marker is outside the original source.  Its stage frontier
roofs the source, while freshness places the marker outside that roof. -/
theorem marker_not_mem_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    {a : Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∉ Gamma.source := by
  intro hySource
  apply L.marker_not_mem_roof_frontier hL hy
  rw [L.frontier_eq_essential_terminalFrontier
    hL.roofsSourceAtStages, Gamma.roof_essential]
  exact hL.roofsSourceAtStages (Stage.toExtended a) hySource

/-- Every equal-index auxiliary route canonically determines its essential
hanging target component, with exactly the same ordinal owner as the route
source. -/
theorem exists_equalTargetComponent
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths) :
    Nonempty (L.EqualTargetComponent hL P p hp) := by
  let I := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  rcases L.equalSubwarp_path_sameStage hL P hp with
      ⟨x, y, _hstart, hfinish, hstage⟩ |
      ⟨i, y, _hstart, hfinish, hstage⟩
  · have hyVertex : y.1 ∈ Gamma.vertexSet I.essentialLadder := y.2.2
    obtain ⟨Y, hYessential, hyY⟩ := (Gamma.mem_vertexSet).1 hyVertex
    have hYessential' : Y ∈ Gamma.essentialWarpPart L.limitWarp := by
      simpa only [I, KappaLadder.popularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder] using hYessential
    have hYinitial : Y.initial = y.1 :=
      hL.legal.initial_eq_of_targetMarker_mem_limitWarp_support
        y.2 hYessential'.1 hyY
    have hYhanging : PopularAuxiliary.IsHangingPath Gamma Y := by
      rw [PopularAuxiliary.IsHangingPath, hYinitial]
      exact L.marker_not_mem_source hL.legal
        (L.markerStage_spec ⟨y.1, y.2.1⟩)
    let a := L.finiteTerminalIndex x
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
        L.hangingComponentStage hL.legal Y hYessential'.1 hYhanging = a := by
      apply hL.legal.markersInjective
      · exact L.marker_hangingComponentStage hL.legal Y
          hYessential'.1 hYhanging
      · change L.marker (L.finiteTerminalIndex x) = some Y.initial
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
      simpa only [I, KappaLadder.popularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder] using hYessential
    have hYinitial : Y.initial = y.1 :=
      hL.legal.initial_eq_of_targetMarker_mem_limitWarp_support
        y.2 hYessential'.1 hyY
    have hYhanging : PopularAuxiliary.IsHangingPath Gamma Y := by
      rw [PopularAuxiliary.IsHangingPath, hYinitial]
      exact L.marker_not_mem_source hL.legal
        (L.markerStage_spec ⟨y.1, y.2.1⟩)
    let a := L.groundedInfiniteStage i
    have hsource :
        U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ = a := by
      have heq :
          (⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ :
              I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := Subtype.ext _hstart
      rw [heq]
      rfl
    have howner :
        L.hangingComponentStage hL.legal Y hYessential'.1 hYhanging = a := by
      apply hL.legal.markersInjective
      · exact L.marker_hangingComponentStage hL.legal Y
          hYessential'.1 hYhanging
      · change L.marker (L.groundedInfiniteStage i) = some Y.initial
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

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.marker_not_mem_source
#print axioms Erdos599.DWeb.KappaLadder.exists_equalTargetComponent

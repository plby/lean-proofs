/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSliceComponentClosure
import ErdosProblems.Erdos599.RegularSliceOrdinaryInterval
import ErdosProblems.Erdos599.RegularSliceSurvivors
import ErdosProblems.Erdos599.SliceSpliceConstructor
import ErdosProblems.Erdos599.DeferredRegularGeometry

/-!
# Component replacement for a regular-cardinal slice

This file performs the cardinal and disjointness part of Assertion 9.10.
Starting with a tight linkage `T` between two ladder frontiers, retain the
alternating components which meet either a target-linking subfamily or a
source whose ladder component does not survive to the later stage.  The
retained part is smaller than `kappa`.  Every other source has a canonical
stage interval, and the two resulting path families are vertex-disjoint.

The two region hypotheses in the public theorem are precisely the remaining
ambient quotient geometry: the retained linkage and the canonical interval
family lie in the annulus between the two frontiers.  Everything else,
including the exceptional cardinal estimate and the stage-interval
provenance, is constructed here.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceComponentReplacement

open DirectedPath
open SliceSpliceSource

universe u

variable {V : Type u}

/-- The small set of vertices which seeds the exceptional alternating
components: all vertices of a small target-linking subfamily, together with
the earlier-frontier sources which do not survive to the later stage. -/
def exceptionalSeed
    (Gamma : DWeb V) {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (delta beta : Ladder.Stage kappa) (K : Set Gamma.DPath) : Set V :=
  Gamma.vertexSet K ∪
    RegularSliceSurvivors.nonsurvivorSources Gamma L delta beta

/-- The alternating-component closure used for component replacement. -/
def exceptionalClosure
    (Gamma : DWeb V) {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (delta beta : Ladder.Stage kappa)
    (T K : Set Gamma.DPath) : Set V :=
  RegularSliceComponentClosure.seededComponentClosure T
    (Gamma.essentialWarpPart (L.warpAt beta))
    (exceptionalSeed Gamma L delta beta K)

private theorem seed_subset_exceptionalClosure
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {T K : Set Gamma.DPath} :
    exceptionalSeed Gamma L delta beta K ⊆
      exceptionalClosure Gamma L delta beta T K := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx,
    AlternatingComponents.mem_component_self T
      (Gamma.essentialWarpPart (L.warpAt beta)) x⟩⟩

private theorem finite_left_path_support_subset_exceptionalClosure
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {T K : Set Gamma.DPath}
    {p : FinitePath Gamma.graph}
    (hpT : (Sum.inl p : Gamma.DPath) ∈ T)
    (hinitial : p.start ∈ exceptionalClosure Gamma L delta beta T K) :
    p.support ⊆ exceptionalClosure Gamma L delta beta T K := by
  intro x hxp
  simp only [exceptionalClosure,
    RegularSliceComponentClosure.seededComponentClosure,
    Set.mem_iUnion] at hinitial ⊢
  obtain ⟨root, hrootSeed, hstartRoot⟩ := hinitial
  exact ⟨root, hrootSeed,
    hstartRoot.trans
      (AlternatingComponents.finitePath_support_subset_component_left
        (Y := Gamma.essentialWarpPart (L.warpAt beta))
        hpT p.start_mem_support hxp)⟩

private theorem finite_right_path_support_subset_exceptionalClosure_of_meets
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {T K : Set Gamma.DPath}
    {p : FinitePath Gamma.graph} {x : V}
    (hpY : (Sum.inl p : Gamma.DPath) ∈
      Gamma.essentialWarpPart (L.warpAt beta))
    (hxP : x ∈ p.support)
    (hxD : x ∈ exceptionalClosure Gamma L delta beta T K) :
    p.support ⊆ exceptionalClosure Gamma L delta beta T K := by
  intro y hyp
  simp only [exceptionalClosure,
    RegularSliceComponentClosure.seededComponentClosure,
    Set.mem_iUnion] at hxD ⊢
  obtain ⟨root, hrootSeed, hxRoot⟩ := hxD
  exact ⟨root, hrootSeed,
    hxRoot.trans
      (AlternatingComponents.finitePath_support_subset_component_right
        (Z := T) hpY hxP hyp)⟩

/-- The component-replacement compiler.  It chooses a small subfamily
which links the request, closes its vertices together with all nonsurviving
sources under alternating components, retains precisely the old linkage
paths starting in that closure, and replaces every other path by its
canonical later-stage ladder interval. -/
theorem exists_annularSliceCandidate_of_replacement_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hL : SliceSpliceConstructor.SpliceLadderGeometry Gamma L)
    (huncountable : ℵ₀ < kappa)
    (hroof : L.RoofsSourceAtStages)
    (hnonSmall :
      #(RegularSliceSurvivors.nonsurvivorSources
        Gamma L delta beta) < kappa)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta))
    {T : Set Gamma.DPath}
    (hT : TightLinkageBetween Gamma
      (L.frontier delta) (L.frontier beta) T)
    (hlinks : LinksToTarget Gamma T (request delta gamma))
    (hrequest : #(request delta gamma) < kappa)
    (hTannular : Gamma.vertexSet T ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (hordinaryAnnular :
      ∀ (K : Set Gamma.DPath), K ⊆ T → #K < kappa →
        let D := exceptionalClosure Gamma L delta beta T K
        let S := L.frontier delta \ D
        let R := RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
          (L := L) (delta := delta) (beta := beta) (S := S)
          (by
            intro x hx
            by_contra hxNot
            exact hx.2 (seed_subset_exceptionalClosure
              (T := T) (K := K) (Or.inr ⟨hx.1, hxNot⟩)))
          hroof hL.warpStages hgrows
        Gamma.vertexSet
          (SliceSegmentCore.segmentFamily R.toSegmentRealization) ⊆
            L.lowerRegion delta ∩ L.upperRegion beta) :
    ∃ T', SliceCandidate.IsAnnularSliceCandidate
      Gamma L request delta beta gamma T' := by
  obtain ⟨K, hKT, hKlinks, hKsmall⟩ :=
    SliceCandidate.exists_targetLinkingSubfamily_mk_lt
      Gamma hlinks hrequest
  let seed := exceptionalSeed Gamma L delta beta K
  let D := exceptionalClosure Gamma L delta beta T K
  let S := L.frontier delta \ D
  let E := initialRestriction Gamma T (L.frontier delta ∩ D)
  have hKvertices : #(Gamma.vertexSet K) < kappa :=
    ControlledSlices.mk_vertexSet_exceptional_lt Gamma hL.regular hKT
      hKsmall hT.1.finiteCharacter
  have hseedSmall : #seed < kappa := by
    exact RegularCardinal.mk_union_lt hL.regular hKvertices hnonSmall
  have hDsmall : #D < kappa := by
    exact RegularSliceComponentClosure.mk_seededComponentClosure_lt
      hL.regular huncountable hT.1.isWarp
      ((hL.warpStages
        (Ladder.Stage.toExtended beta)).essentialWarpPart)
      hT.1.finiteCharacter
      (Gamma.hasFiniteCharacter_essentialWarpPart (L.warpAt beta))
      hseedSmall
  have hEsmall : #E < kappa := by
    exact RegularSliceComponentClosure.mk_initialRestriction_lt_of_isWarp
      hT.1.isWarp
      ((Cardinal.mk_subtype_mono Set.inter_subset_right).trans_lt hDsmall)
  have hSsurv : S ⊆
      RegularSliceSurvivors.survivorSources Gamma L delta beta := by
    intro x hx
    by_contra hxNot
    exact hx.2 (seed_subset_exceptionalClosure
      (T := T) (K := K) (Or.inr ⟨hx.1, hxNot⟩))
  let R := RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
    hSsurv hroof hL.warpStages hgrows
  have hEsub : E ⊆ T := fun _ hp ↦ hp.1
  have hERemainder : SliceSegmentCore.IsExceptionalRemainder Gamma
      (L.frontier delta) (L.frontier beta) E :=
    SliceCandidate.isExceptionalRemainder_of_linkage_subfamily
      Gamma hT.1 hEsub
  have hEinitial : Gamma.initialSet E = L.frontier delta ∩ D :=
    (isLinkageBetween_initialRestriction hT.1 Set.inter_subset_left).initialSet_eq
  have hcover : L.frontier delta = S ∪ Gamma.initialSet E := by
    rw [hEinitial]
    ext x
    simp only [S, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hKsubE : K ⊆ E := by
    intro p hpK
    refine ⟨hKT hpK, ?_, ?_⟩
    · rw [← hT.1.initialSet_eq]
      exact ⟨p, hKT hpK, rfl⟩
    · apply seed_subset_exceptionalClosure
      apply Or.inl
      exact ⟨p, hpK, p.initial_mem_support⟩
  have hElinks : LinksToTarget Gamma E (request delta gamma) :=
    SliceSegmentCore.linksToTarget_mono_family hKsubE hKlinks
  have hdisjoint : Disjoint
      (Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization))
      (Gamma.vertexSet E) := by
    rw [Set.disjoint_left]
    intro x hxO hxE
    obtain ⟨segment, hsegment, hxSegment⟩ := hxO
    obtain ⟨s, rfl⟩ := hsegment
    obtain ⟨p, hpE, hxP⟩ := hxE
    obtain ⟨finite, rfl⟩ := hT.1.finiteCharacter hpE.1
    have hinitialD : finite.start ∈ D := hpE.2.2
    have hxD : x ∈ D :=
      finite_left_path_support_subset_exceptionalClosure hpE.1
        hinitialD hxP
    have hxRight : x ∈ (R.rightPrefix s).support :=
      (R.toSegmentRealization.segment_subpath s).1 hxSegment
    have hrightD : (R.rightPrefix s).support ⊆ D :=
      finite_right_path_support_subset_exceptionalClosure_of_meets
        (R.right_mem s) hxRight hxD
    have hsD : s.1 ∈ D := by
      apply hrightD
      exact (R.toSegmentRealization.segment_subpath s).1
        (R.toSegmentRealization.segment_start s ▸
          (R.toSegmentRealization.segment s).start_mem_support)
    exact s.2.2 hsD
  have hEannular : Gamma.vertexSet E ⊆
      L.lowerRegion delta ∩ L.upperRegion beta :=
    (vertexSet_initialRestriction_subset Gamma T
      (L.frontier delta ∩ D)).trans hTannular
  have hRannular : Gamma.vertexSet
      (SliceSegmentCore.segmentFamily R.toSegmentRealization) ⊆
        L.lowerRegion delta ∩ L.upperRegion beta := by
    simpa only [R, S, D] using hordinaryAnnular K hKT hKsmall
  have hannular : Gamma.vertexSet
      (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E) ⊆
        L.lowerRegion delta ∩ L.upperRegion beta := by
    rw [DWeb.vertexSet_union]
    exact Set.union_subset hRannular hEannular
  have hEtight : SliceCandidate.RightBoundaryTight Gamma E
      (L.frontier beta) := by
    intro p hp
    exact hT.2 p hp.1
  have hRtight : SliceCandidate.RightBoundaryTight Gamma
      (SliceSegmentCore.segmentFamily R.toSegmentRealization)
      (L.frontier beta) := by
    intro p hp y hyp hyBeta
    obtain ⟨s, rfl⟩ := hp
    let Ext := RegularSliceSurvivors.essentialStageExtensionsOfSubset hSsurv
    have hy : y ∈ (Ext.segment s).support ∩ L.frontier beta := by
      change y ∈ (Ext.segment s).support at hyp
      exact ⟨hyp, hyBeta⟩
    rw [RegularSliceSurvivors.segment_frontier_beta_of_geometry
      Ext hroof hL.warpStages s] at hy
    change some (Ext.segment s).finish = some y
    exact congrArg some (Set.mem_singleton_iff.mp hy).symm
  have htight : SliceCandidate.RightBoundaryTight Gamma
      (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E)
      (L.frontier beta) :=
    SliceCandidate.RightBoundaryTight.union hRtight hEtight
  have hintervalE : SliceCandidate.HasStageIntervalSegments
      Gamma L E delta beta := by
    intro p hpE hpordinary
    exact SliceCandidate.isStageInterval_of_tightLinkage_fragment_of_geometry
      hroof hL.warpStages hgrows hT hpE.1 hpordinary
  refine ⟨_, SliceCandidate.isAnnularSliceCandidate_of_componentReplacement
    (hL.warpStages (Ladder.Stage.toExtended beta)) R hERemainder
      hcover hdisjoint hElinks hEsmall hannular htight hintervalE⟩

/-- Deferred-legality compatibility wrapper.  Deferred bookkeeping is used
only to bound the nonsurviving sources; component replacement itself runs on
the bookkeeping-free splice geometry. -/
theorem exists_annularSliceCandidate_of_replacement_deferredLegal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hbeta : beta ∉ DWeb.KappaLadder.Deferred.phi L)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta))
    {T : Set Gamma.DPath}
    (hT : TightLinkageBetween Gamma
      (L.frontier delta) (L.frontier beta) T)
    (hlinks : LinksToTarget Gamma T (request delta gamma))
    (hrequest : #(request delta gamma) < kappa)
    (hTannular : Gamma.vertexSet T ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (hordinaryAnnular :
      ∀ (K : Set Gamma.DPath), K ⊆ T → #K < kappa →
        let D := exceptionalClosure Gamma L delta beta T K
        let S := L.frontier delta \ D
        let R := RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
          (L := L) (delta := delta) (beta := beta) (S := S)
          (by
            intro x hx
            by_contra hxNot
            exact hx.2 (seed_subset_exceptionalClosure
              (T := T) (K := K) (Or.inr ⟨hx.1, hxNot⟩)))
          hL.roofsSourceAtStages hL.warpStages hgrows
        Gamma.vertexSet
          (SliceSegmentCore.segmentFamily R.toSegmentRealization) ⊆
            L.lowerRegion delta ∩ L.upperRegion beta) :
    ∃ T', SliceCandidate.IsAnnularSliceCandidate
      Gamma L request delta beta gamma T' := by
  apply exists_annularSliceCandidate_of_replacement_geometry
    ({ regular := hL.regular
       initialStage := hL.initialStage
       limitStages := hL.limitStages
       warpStages := hL.warpStages
       frontiersEssential := hL.frontiersEssential
       frontierChronology := hL.frontierChronology
       strictFrontierChronology := hL.strictFrontierChronology } :
      SliceSpliceConstructor.SpliceLadderGeometry Gamma L)
    hL.uncountable hL.roofsSourceAtStages
    ((RegularSliceSurvivors.mk_nonsurvivorSources_le_inessential
      hL.roofsSourceAtStages hL.warpStages hgrows).trans_lt
        (DWeb.KappaLadder.Deferred.mk_inessentialWarpAt_lt_of_not_mem_phi
          hL beta hbeta))
    hgrows hT hlinks hrequest hTannular
  exact hordinaryAnnular

end RegularSliceComponentReplacement
end CardinalInduction
end Erdos599

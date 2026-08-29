/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularLinkageGeometry
import ErdosProblems.Erdos599.SliceSegmentCore
import ErdosProblems.Erdos599.LadderFrontierInvariants
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# Lifting a tight regular slice out of a ladder stage

The half-way and auxiliary constructions run in the essential quotient
`L.stageWeb delta`.  This file transports their final tight linkage to the
ambient web.  Besides preserving paths, endpoints, and target-link witnesses,
the lift is automatically annular once the later frontier separates the stage
source.  The lower annular bound is the quotient's strict-roof deletion; the
upper bound is obtained by transporting the stage-web roof through the
essential-part restriction and then through the quotient.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceStageLift

open DirectedPath
open SliceSpliceSource

universe u

variable {V : Type u}

private theorem stageWalk_support_subset_compl_strictRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    {a b : V} (p : DirectedPath.Walk (L.stageWeb delta).graph a b)
    (ha : a ∉ Gamma.strictRoof
      (Gamma.terminalFrontier (L.warpAt delta))) :
    ∀ {x}, x ∈ p.support →
      x ∉ Gamma.strictRoof
        (Gamma.terminalFrontier (L.warpAt delta)) := by
  induction p with
  | nil =>
      intro x hxp
      simp only [DirectedPath.Walk.support_nil, List.mem_singleton] at hxp
      exact hxp ▸ ha
  | @cons a c b e p ih =>
      intro x hxp
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hxp
      rcases hxp with rfl | hxp
      · exact ha
      · apply ih
        · exact (Gamma.quotient_adj_endpoints
            ((Gamma.quotient
              (Gamma.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp
                e)).2.1
        · exact hxp

private theorem stageFinitePath_support_disjoint_strictRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    (hroof : L.RoofsSourceAtStages)
    (p : DirectedPath.FinitePath (L.stageWeb delta).graph)
    (hstart : p.start ∈ L.frontier delta) :
    Disjoint p.support (Gamma.strictRoof (L.frontier delta)) := by
  have hstartEssential : p.start ∈ Gamma.essential
      (Gamma.terminalFrontier (L.warpAt delta)) := by
    rw [← L.frontier_eq_essential_terminalFrontier hroof delta]
    exact hstart
  have hstartNot : p.start ∉ Gamma.strictRoof
      (Gamma.terminalFrontier (L.warpAt delta)) := fun h ↦
    Set.disjoint_left.1
      (Gamma.disjoint_strictRoof_essential
        (Gamma.terminalFrontier (L.warpAt delta))) h hstartEssential
  apply Set.disjoint_left.2
  intro x hxp hxStrict
  apply stageWalk_support_subset_compl_strictRoof p.walk hstartNot hxp
  rwa [L.frontier_eq_essential_terminalFrontier hroof delta,
    Gamma.strictRoof_essential] at hxStrict

private theorem essentialPart_roof_subset_roof
    (Q : DWeb V) {S : Set V} {x : V}
    (hxRoof : x ∈ Q.essentialPart.roof S) :
    x ∈ Q.roof S := by
  intro p hp
  have hreach : p.support ⊆ Q.reachableToTarget :=
    Q.finitePath_support_subset_reachableToTarget p hp.2
  let hrestrict : ∀ {u v : V}, Q.graph.Adj u v →
      u ∈ p.support → v ∈ p.support →
      Q.essentialPart.graph.Adj u v :=
    fun e hu hv ↦ ⟨e, hreach hu, hreach hv⟩
  let q : DirectedPath.FinitePath Q.essentialPart.graph :=
    p.restrictGraphOnSupport hrestrict
  have hq : Q.essentialPart.IsTargetPathFrom x q := by
    refine ⟨?_, ?_⟩
    · simpa only [q, DirectedPath.FinitePath.restrictGraphOnSupport]
        using hp.1
    · change q.finish ∈ Q.target
      simpa only [q, DirectedPath.FinitePath.restrictGraphOnSupport] using hp.2
  obtain ⟨y, hyq, hyS⟩ := hxRoof q hq
  have hyp : y ∈ p.support := by
    rw [← show q.support = p.support from
      DirectedPath.FinitePath.support_restrictGraphOnSupport p hrestrict]
    exact hyq
  exact ⟨y, hyp, hyS⟩

/-- A tight linkage in a ladder stage lifts to a tight ambient linkage with
the same two boundary sets. -/
theorem tightLinkageBetween_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    {A B : Set V} {T : Set (L.stageWeb delta).DPath}
    (hT : TightLinkageBetween (L.stageWeb delta) A B T) :
    TightLinkageBetween Gamma A B
      (SliceSegmentCore.liftStageFamily L delta T) := by
  refine ⟨⟨SliceSegmentCore.liftStageFamily_isWarp L delta hT.1.isWarp,
    SliceSegmentCore.liftStageFamily_finiteCharacter L delta
      hT.1.finiteCharacter, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [SliceSegmentCore.initialSet_liftStageFamily] using
      hT.1.initialSet_eq
  · simpa only [SliceSegmentCore.terminalFrontier_liftStageFamily] using
      hT.1.terminalFrontier_subset
  · rintro p ⟨q, hqT, rfl⟩
    obtain ⟨f, rfl, hends, hsource⟩ := hT.1.endpointPure q hqT
    refine ⟨SliceSegmentCore.liftStageFinitePath L delta f, rfl, ?_, ?_⟩
    · simpa only [SliceSegmentCore.liftStageFinitePath_support,
        SliceSegmentCore.liftStageFinitePath_start,
        SliceSegmentCore.liftStageFinitePath_finish] using hends
    · simpa only [SliceSegmentCore.liftStageFinitePath_support,
        SliceSegmentCore.liftStageFinitePath_start] using hsource
  · rintro p ⟨q, hqT, rfl⟩ x hx hxB
    simpa only [SliceSegmentCore.liftStagePath_terminal] using
      hT.2 q hqT x
        (by simpa only [SliceSegmentCore.liftStagePath_support] using hx) hxB

/-- The lift of a stage linkage avoids the strict roof of its source
frontier. -/
theorem liftStageFamily_vertexSet_subset_lowerRegion
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    (hroof : L.RoofsSourceAtStages)
    {B : Set V} {T : Set (L.stageWeb delta).DPath}
    (hT : IsLinkageBetween (L.stageWeb delta)
      (L.frontier delta) B T) :
    Gamma.vertexSet (SliceSegmentCore.liftStageFamily L delta T) ⊆
      L.lowerRegion delta := by
  rintro x ⟨p, ⟨q, hqT, rfl⟩, hxp⟩
  obtain ⟨f, rfl⟩ := hT.finiteCharacter hqT
  have hstart : f.start ∈ L.frontier delta := by
    rw [← hT.initialSet_eq]
    exact ⟨Sum.inl f, hqT, rfl⟩
  have hdis := stageFinitePath_support_disjoint_strictRoof hroof f hstart
  have hxf : x ∈ f.support := by
    simpa only [SliceSegmentCore.liftStagePath_finite,
      SliceSegmentCore.liftStageFinitePath_support,
      DirectedPath.Path.support] using hxp
  exact Set.disjoint_left.1 hdis hxf

/-- If the later frontier separates the stage source, every lifted path is
also below the later frontier in the ambient web. -/
theorem liftStageFamily_vertexSet_subset_upperRegion
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    (hroof : L.RoofsSourceAtStages)
    (hchron : L.HasFrontierChronology) (hdeltaBeta : delta < beta)
    {T : Set (L.stageWeb delta).DPath}
    (hT : TightLinkageBetween (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta) T)
    (hsep : IsSeparatorFrom (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta)) :
    Gamma.vertexSet (SliceSegmentCore.liftStageFamily L delta T) ⊆
      L.upperRegion beta := by
  have hstageRoof : (L.stageWeb delta).vertexSet T ⊆
      (L.stageWeb delta).roof (L.frontier beta) :=
    SingularContinuation.linkage_vertexSet_subset_roof
      (L.stageWeb delta) hT.1 hsep hT.2
  let raw := Gamma.terminalFrontier (L.warpAt delta)
  have hessential : Gamma.essential raw ⊆
      Gamma.roof (L.frontier beta) := by
    rw [← L.frontier_eq_essential_terminalFrontier hroof delta]
    exact hchron hdeltaBeta
  rintro x ⟨p, ⟨q, hqT, rfl⟩, hxp⟩
  obtain ⟨f, rfl⟩ := hT.1.finiteCharacter hqT
  have hstart : f.start ∈ L.frontier delta := by
    rw [← hT.1.initialSet_eq]
    exact ⟨Sum.inl f, hqT, rfl⟩
  have hxf : x ∈ f.support := by
    simpa only [SliceSegmentCore.liftStagePath_finite,
      SliceSegmentCore.liftStageFinitePath_support,
      DirectedPath.Path.support] using hxp
  have hxStage : x ∈ (L.stageWeb delta).vertexSet T :=
    ⟨Sum.inl f, hqT, hxf⟩
  have hxQuotientRoof : x ∈
      (Gamma.quotient raw).roof (L.frontier beta) :=
    essentialPart_roof_subset_roof
      (Gamma.quotient raw) (hstageRoof hxStage)
  have hxNotStrict : x ∉ Gamma.strictRoof raw := by
    have hdis := stageFinitePath_support_disjoint_strictRoof hroof f hstart
    have hxNot : x ∉ Gamma.strictRoof (L.frontier delta) :=
      Set.disjoint_left.1 hdis hxf
    rwa [L.frontier_eq_essential_terminalFrontier hroof delta,
      Gamma.strictRoof_essential] at hxNot
  exact Gamma.quotient_roof_subset_original_roof_of_essential
    raw (L.frontier beta) hessential ⟨hxQuotientRoof, hxNotStrict⟩

/-- Full stage-to-ambient compiler: tightness, target-linking, and both
annular bounds are preserved. -/
theorem tightAnnularLinkage_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    (hroof : L.RoofsSourceAtStages)
    (hchron : L.HasFrontierChronology) (hdeltaBeta : delta < beta)
    {T : Set (L.stageWeb delta).DPath} {U : Set V}
    (hT : TightLinkageBetween (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta) T)
    (hlinks : LinksToTarget (L.stageWeb delta) T U)
    (hsep : IsSeparatorFrom (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta)) :
    TightLinkageBetween Gamma (L.frontier delta) (L.frontier beta)
        (SliceSegmentCore.liftStageFamily L delta T) ∧
      LinksToTarget Gamma (SliceSegmentCore.liftStageFamily L delta T) U ∧
      Gamma.vertexSet (SliceSegmentCore.liftStageFamily L delta T) ⊆
        L.lowerRegion delta ∩ L.upperRegion beta := by
  refine ⟨tightLinkageBetween_liftStageFamily hT,
    SliceSegmentCore.linksToTarget_liftStageFamily L delta hlinks, ?_⟩
  exact fun x hx ↦
    ⟨liftStageFamily_vertexSet_subset_lowerRegion hroof
        hT.1 hx,
      liftStageFamily_vertexSet_subset_upperRegion hroof hchron hdeltaBeta
        hT hsep hx⟩

end RegularSliceStageLift
end CardinalInduction
end Erdos599

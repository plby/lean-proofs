/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice
import ErdosProblems.Erdos599.RegularWeakInstalledComparison
import ErdosProblems.Erdos599.RegularCandidateProvider
import ErdosProblems.Erdos599.SliceStageIntervalBridge

/-!
# Splitting a full target-linking annular row

A full stage-web linkage which links a small requested set may fail to be
right-tight only at requested sources already on the right boundary.  We
therefore install those boundary requests on the target track and cut the
complementary components at their first visit to the right boundary.  This
file packages that operation as the weak split candidate consumed by the
regular source-9.15 recursion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakFullRowSplit

open SliceSpliceSource
open RegularCompletedPendingSplice

universe u

variable {V : Type u}

/-- Split a full source row at the requested sources already lying on its
right boundary.  The complementary first-hit row still links every remaining
request, because those remaining requested sources avoid that boundary. -/
theorem exists_cleanTargetSlice_inter_right
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source) (hlinks : LinksToTarget Q W U) :
    let E := U ∩ C
    ∃ S : CleanTargetSlice Q Q.source C E,
      S.target = initialRestriction Q W E ∧
      S.clean = RegularBetaSelection.targetFirstHitFamily
        (isLinkageBetween_initialRestriction
          (A' := Q.source \ E) hW Set.sdiff_subset) ∧
      LinksToTarget Q S.clean (U \ E) ∧
      #(S.target) ≤ #E := by
  dsimp only
  let E := U ∩ C
  obtain ⟨S, htarget, hclean, htargetCard, _htargetCompleted⟩ :=
    RegularHalfwaySplit.exists_cleanTargetSlice_of_halfway
      hNorm hW ((Set.inter_subset_left).trans hUsource)
        (ControlledSlices.linksToTarget_mono Q W Set.inter_subset_left hlinks)
  let M := U \ E
  let P := initialRestriction Q W (Q.source \ E)
  let hP : IsLinkageBetween Q (Q.source \ E) C P :=
    isLinkageBetween_initialRestriction hW Set.sdiff_subset
  have hMsource : M ⊆ Q.source := Set.sdiff_subset.trans hUsource
  have hMsub : M ⊆ Q.source \ E := by
    intro x hx
    exact ⟨hMsource hx, hx.2⟩
  have hMlinksW : LinksToTarget Q W M :=
    ControlledSlices.linksToTarget_mono Q W Set.sdiff_subset hlinks
  have hMlinksP : LinksToTarget Q P M := by
    apply SliceSegmentCore.linksToTarget_mono_family
      (W := initialRestriction Q W M)
    · intro p hp
      exact ⟨hp.1, hMsub hp.2⟩
    · exact RegularHalfwaySplit.linksToTarget_initialRestriction
        hW hMsource hMlinksW
  have havoid : Disjoint (M \ Q.target) C := by
    apply Set.disjoint_left.2
    intro x hxM hxC
    exact hxM.1.2 ⟨hxM.1.1, hxC⟩
  have hcleanLinks : LinksToTarget Q
      (RegularBetaSelection.targetFirstHitFamily hP) M :=
    RegularBetaSelection.targetFirstHitFamily_linksToTarget_of_subsource
      hNorm hP hMsub hMlinksP havoid
  refine ⟨S, htarget, hclean, ?_, htargetCard⟩
  simpa only [M, P, hclean] using hcleanLinks

/-- The boundary requests selected by the full-row splitter. -/
def boundarySelected (U C : Set V) : Set V := U ∩ C

/-- The selected subfamily of a full row. -/
def fullRowTarget (Q : DWeb V) (W : Set Q.DPath) (U C : Set V) :
    Set Q.DPath :=
  initialRestriction Q W (boundarySelected U C)

/-- The complementary row, cut at its first visit to the right boundary. -/
def fullRowClean
    (Q : DWeb V) {C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W) (U : Set V) : Set Q.DPath :=
  RegularBetaSelection.targetFirstHitFamily
    (isLinkageBetween_initialRestriction
      (A' := Q.source \ boundarySelected U C) hW Set.sdiff_subset)

private theorem finitePath_eq_of_prefix_of_finish_eq
    {D : Digraph V} {p q : DirectedPath.FinitePath D}
    (hpq : p.IsPrefixOf q) (hfinish : p.finish = q.finish) : p = q := by
  have hstart : p.start = q.start := hpq.start_eq
  cases p with
  | mk ps pf pw ppath =>
      cases q with
      | mk qs qf qw qpath =>
          dsimp at hstart hfinish hpq ⊢
          subst qs
          subst qf
          have hs : pw.support = qw.support :=
            DirectedPath.FinitePath.IsPrefixOf.eq_support_of_finish_eq hpq rfl
          have hw : pw = qw := DirectedPath.Walk.eq_of_support_eq pw qw hs
          subst qw
          rfl

private theorem path_eq_of_extends_of_same_terminal
    {D : Digraph V} {p q : DirectedPath.Path D} {x : V}
    (hpq : DirectedPath.Path.Extends p q)
    (hp : p.terminal? = some x) (hq : q.terminal? = some x) : p = q := by
  rcases p with p | r <;> rcases q with q | s
  · congr 1
    apply finitePath_eq_of_prefix_of_finish_eq hpq
    exact Option.some.inj (hp.trans hq.symm)
  · simp at hq
  · exact hpq.elim
  · simp at hp

/-- If the full row was already right-tight, its canonical complementary
first-hit row consists literally of members of the full row. -/
theorem fullRowClean_subset_of_terminalClean
    (Q : DWeb V) {C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W) (U : Set V)
    (hclean : SingularContinuation.TerminalCleanAt Q W C) :
    fullRowClean Q hW U ⊆ W := by
  let P := initialRestriction Q W (Q.source \ boundarySelected U C)
  let hP : IsLinkageBetween Q
      (Q.source \ boundarySelected U C) C P :=
    isLinkageBetween_initialRestriction hW Set.sdiff_subset
  have hforward : Q.ForwardExtension
      (RegularBetaSelection.targetFirstHitFamily hP) P :=
    RegularBetaSelection.targetFirstHitFamily_forwardExtension hP
  intro p hp
  obtain ⟨q, hqP, hpq⟩ := hforward.1 p hp
  obtain ⟨f, rfl⟩ :=
    (RegularBetaSelection.targetFirstHitFamily_isLinkageBetween hP)
      |>.finiteCharacter hp
  have hfinishC : f.finish ∈ C := by
    apply (RegularBetaSelection.targetFirstHitFamily_isLinkageBetween hP)
      |>.terminalFrontier_subset
    exact ⟨Sum.inl f, hp, rfl⟩
  have hqFinish : Q.terminal? q = some f.finish := by
    apply hclean q hqP.1 f.finish
    · exact Q.support_mono_of_extends hpq f.finish_mem_support
    · exact hfinishC
  have hpFinish : Q.terminal? (Sum.inl f : Q.DPath) = some f.finish := rfl
  have hpqEq : (Sum.inl f : Q.DPath) = q :=
    path_eq_of_extends_of_same_terminal hpq hpFinish hqFinish
  exact hpqEq.symm ▸ hqP.1

/-- A full target-linking stage row yields a weak split candidate once the
literal split tracks have the annular carrier and maverick estimates.  The
stage-interval property is automatic from the resulting full ambient
frontier linkage, so it is not an additional premise.

This is the provider-facing one-full-row splitter: the source-9.10
construction may focus on building one target-linking row, while the only
selected components are the requested sources already on the later
frontier. -/
theorem exists_weakSplitAnnularCandidate_of_stageTargetLinking
    {kappa : Cardinal.{u}} {G : DWeb V} {L : G.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hL : L.IsSplitLegal) (hdeltaBeta : delta ≤ beta)
    (hNorm : (L.stageWeb delta).IsNormalized)
    {W : Set (L.stageWeb delta).DPath}
    (hW : IsLinkageBetween (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta) W)
    (hrequest : request delta gamma ⊆ L.frontier delta)
    (hlinks : LinksToTarget (L.stageWeb delta) W (request delta gamma))
    (hsmall : #(request delta gamma) < kappa)
    (hregion : G.vertexSet
        (SliceSegmentCore.liftStageFamily L delta
            (fullRowTarget (L.stageWeb delta) W
              (request delta gamma) (L.frontier beta)) ∪
          SliceSegmentCore.liftStageFamily L delta
            (fullRowClean (L.stageWeb delta) hW (request delta gamma))) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (hmavericks : #(ControlledSlices.sliceMavericks G (L.warpAt beta)
        (SliceSegmentCore.liftStageFamily L delta
          (fullRowClean (L.stageWeb delta) hW (request delta gamma)))) <
      kappa) :
    ∃ P : RegularWeakSplitCandidate.WeakSplitFamilies G,
      RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
        G L request delta beta gamma P := by
  let Q := L.stageWeb delta
  let U := request delta gamma
  let C := L.frontier beta
  have hQsource : U ⊆ Q.source := by
    change request delta gamma ⊆ L.frontier delta
    exact hrequest
  obtain ⟨Sstage, htarget, hclean, hcleanLinks, htargetCard⟩ :=
    exists_cleanTargetSlice_inter_right hNorm hW hQsource hlinks
  let S : CleanTargetSlice G (L.frontier delta) C (boundarySelected U C) :=
    RegularLiftCleanTargetSlice.liftStageSlice L delta Sstage
  have htargetDef : S.target =
      SliceSegmentCore.liftStageFamily L delta
        (fullRowTarget Q W U C) := by
    change SliceSegmentCore.liftStageFamily L delta Sstage.target = _
    rw [htarget]
    rfl
  have hcleanDef : S.clean =
      SliceSegmentCore.liftStageFamily L delta
        (fullRowClean Q hW U) := by
    change SliceSegmentCore.liftStageFamily L delta Sstage.clean = _
    rw [hclean]
    rfl
  have hselectedPersistent :
      RegularWeakSplitCandidate.stagePersistent G C U ⊆
        boundarySelected U C := by
    rintro x ⟨hxU, hxC⟩
    exact ⟨hxU.1, hxC⟩
  have hselectedRequest : boundarySelected U C ⊆ U :=
    Set.inter_subset_left
  have htargetStage : IsLinkageBetween Q (boundarySelected U C) C
      (fullRowTarget Q W U C) := by
    exact isLinkageBetween_initialRestriction hW
      (hselectedRequest.trans hQsource)
  have htargetAmbient : IsLinkageBetween G (boundarySelected U C) C
      S.target := by
    rw [htargetDef]
    exact SliceDeltaLift.IsLinkageBetween.liftStageFamily htargetStage
  have htargetRemainder : SliceSegmentCore.IsExceptionalRemainder G
      (L.frontier delta) C S.target := by
    rw [htargetDef]
    apply SliceSegmentCore.liftStageSubfamily_isExceptionalRemainder
      L delta hW
    intro p hp
    exact hp.1
  have hcleanLinksAmbient : LinksToTarget G S.clean
      (U \ boundarySelected U C) := by
    rw [hcleanDef]
    exact SliceSegmentCore.linksToTarget_liftStageFamily L delta (by
      simpa only [Q, U, C, fullRowClean, boundarySelected, hclean] using
        hcleanLinks)
  have htargetSmallStage : #(Sstage.target) < kappa :=
    htargetCard.trans_lt
      ((Cardinal.mk_subtype_mono hselectedRequest).trans_lt hsmall)
  have htargetSmall : #(S.target) < kappa := by
    change #(SliceSegmentCore.liftStageFamily L delta Sstage.target) < kappa
    exact (SliceSegmentCore.mk_liftStageFamily_le L delta Sstage.target).trans_lt
      htargetSmallStage
  have hfull : IsLinkageBetween G (L.frontier delta) C
      (S.target ∪ S.clean) :=
    RegularWeakInstalledComparison.CleanTargetSlice.union_isLinkageBetween
      S htargetRemainder.terminalFrontier_subset
        (fun p hp ↦ htargetRemainder.endpointPure p hp)
  have hintervals : SliceCandidate.HasStageIntervalSegments G L S.clean
      delta beta := by
    have hall := SliceCandidate.linkage_hasStageIntervalSegments
      hL hdeltaBeta hfull
    intro p hp hfragment
    exact hall p (Or.inr hp) hfragment
  refine ⟨⟨S.target, S.clean, S.target ∪ S.clean⟩, ?_⟩
  apply RegularWeakInstalledComparison.isWeakSplitAnnularCandidate_of_selectedInstalledUnion
    hselectedPersistent S hrequest
      htargetRemainder.terminalFrontier_subset
      (fun p hp ↦ htargetRemainder.endpointPure p hp)
      hcleanLinksAmbient htargetSmall
  · simpa only [htargetDef, hcleanDef, Q, U, C] using hregion
  · exact hintervals
  · simpa only [hcleanDef, Q, U, C] using hmavericks

/-- Terminal-clean specialization of the one-full-row splitter.  Here the
provider only has to control the original full row: both split tracks are
literal subfamilies, so annular carrier containment and the maverick bound
descend automatically. -/
theorem exists_weakSplitAnnularCandidate_of_terminalCleanStageRow
    {kappa : Cardinal.{u}} {G : DWeb V} {L : G.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hL : L.IsSplitLegal) (hdeltaBeta : delta ≤ beta)
    (hNorm : (L.stageWeb delta).IsNormalized)
    {W : Set (L.stageWeb delta).DPath}
    (hW : IsLinkageBetween (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta) W)
    (hterminalClean : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) W (L.frontier beta))
    (hrequest : request delta gamma ⊆ L.frontier delta)
    (hlinks : LinksToTarget (L.stageWeb delta) W (request delta gamma))
    (hsmall : #(request delta gamma) < kappa)
    (hregion : G.vertexSet
        (SliceSegmentCore.liftStageFamily L delta W) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (hmavericks : #(ControlledSlices.sliceMavericks G (L.warpAt beta)
        (SliceSegmentCore.liftStageFamily L delta W)) < kappa) :
    ∃ P : RegularWeakSplitCandidate.WeakSplitFamilies G,
      RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
        G L request delta beta gamma P := by
  let Q := L.stageWeb delta
  let U := request delta gamma
  let C := L.frontier beta
  have hcleanStage : fullRowClean Q hW U ⊆ W :=
    fullRowClean_subset_of_terminalClean Q hW U hterminalClean
  have htargetStage : fullRowTarget Q W U C ⊆ W := by
    intro p hp
    exact hp.1
  have htargetLift :
      SliceSegmentCore.liftStageFamily L delta
          (fullRowTarget Q W U C) ⊆
        SliceSegmentCore.liftStageFamily L delta W := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, htargetStage hp, rfl⟩
  have hcleanLift :
      SliceSegmentCore.liftStageFamily L delta (fullRowClean Q hW U) ⊆
        SliceSegmentCore.liftStageFamily L delta W := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hcleanStage hp, rfl⟩
  have htargetLift' :
      SliceSegmentCore.liftStageFamily L delta
          (fullRowTarget (L.stageWeb delta) W (request delta gamma)
            (L.frontier beta)) ⊆
        SliceSegmentCore.liftStageFamily L delta W := by
    simpa only [Q, U, C] using htargetLift
  have hcleanLift' :
      SliceSegmentCore.liftStageFamily L delta
          (fullRowClean (L.stageWeb delta) hW (request delta gamma)) ⊆
        SliceSegmentCore.liftStageFamily L delta W := by
    simpa only [Q, U] using hcleanLift
  apply exists_weakSplitAnnularCandidate_of_stageTargetLinking
    hL hdeltaBeta hNorm hW hrequest hlinks hsmall
  · rintro x ⟨p, hp, hxp⟩
    apply hregion
    exact ⟨p, hp.elim (fun h ↦ htargetLift' h)
      (fun h ↦ hcleanLift' h), hxp⟩
  · exact (Cardinal.mk_subtype_mono
      (ControlledSlices.sliceMavericks_mono_slice G (L.warpAt beta)
        hcleanLift)).trans_lt hmavericks

end RegularWeakFullRowSplit
end CardinalInduction
end Erdos599

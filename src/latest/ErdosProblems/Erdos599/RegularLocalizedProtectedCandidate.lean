/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LinkageUnion
import ErdosProblems.Erdos599.SliceGeometryHeight
import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice
import ErdosProblems.Erdos599.RegularLocalizedProtectedCleanSlice
import ErdosProblems.Erdos599.RegularProtectedAmbientMaverick
import ErdosProblems.Erdos599.RegularSliceStageCompletion
import ErdosProblems.Erdos599.RegularSliceStageLift
import ErdosProblems.Erdos599.RegularWeakSplitCandidate

/-!
# A regular weak candidate from localized protected half-way geometry

The completed target track is retained literally.  Its first-hit truncation
at the later frontier is used only in the comparison row, where it is united
with the protected clean continuation.  Thus the target track may continue
to the original target without violating right-boundary purity.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedCandidate

open DirectedPath SliceSpliceSource
open Blueprint.LinkageBlueprint.CardinalInduction

universe u
variable {V : Type u}

/-- The protected slice constructor with the ordinary-family maverick
estimate retained. -/
theorem LocalizedProtectedHalfwayGeometry.exists_advancedCleanTargetSlice_with_mavericks
    {Gamma : DWeb V} {A₀ : Set V} {rho kappa : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry Gamma A₀ rho)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hrho : rho < kappa)
    (hlower : RegularProtectedAmbientRebuild.ExtensionBelowFor Gamma kappa)
    (hNorm : Gamma.IsNormalized)
    {T E₀ : Set V} {Y₀ : Set Gamma.DPath}
    (hCroof : D.stopover ⊆ Gamma.roof T)
    (hTessential : Gamma.essential T = T)
    (hE₀small : #E₀ < kappa)
    (hY₀ : IsLinkageBetween Gamma (Gamma.source \ E₀) T Y₀)
    (hY₀tight : MeetsOnlyAtTerminal Gamma Y₀ T) :
    ∃ K : RegularProtectedAmbientRebuild.ProtectedAmbientCompletion
        Gamma (Gamma.vertexSet D.targetPaths) D.stopover T kappa,
      ∃ S : RegularCompletedPendingSplice.CleanTargetSlice
          Gamma Gamma.source T (Gamma.initialSet D.targetPaths),
        S.target = D.targetPaths ∧ S.clean = K.lifted ∧
          #(ControlledSlices.sliceMavericks Gamma Y₀ S.clean) < kappa := by
  let X := Gamma.vertexSet D.targetPaths
  let selected := Gamma.initialSet D.targetPaths
  let S₀ :=
    RegularLocalizedProtectedCleanSlice.LocalizedProtectedHalfwayGeometry.toCleanTargetSlice
      D hNorm
  have hsource : (Gamma.delete X).source = Gamma.source \ selected :=
    RegularLocalizedProtectedCleanSlice.LocalizedProtectedHalfwayGeometry.delete_targetCarrier_source
      D hNorm
  have hR : IsLinkageBetween Gamma (Gamma.delete X).source
      D.stopover D.remainder := by
    rw [hsource]
    exact RegularLocalizedProtectedCleanSlice.LocalizedProtectedHalfwayGeometry.remainder_isLinkageBetween D
  have hRavoid : Disjoint (Gamma.vertexSet D.remainder) X := by
    apply Set.disjoint_left.2
    rintro x hxR hxP
    obtain ⟨r, hr, hxr⟩ := hxR
    obtain ⟨p, hp, hxp⟩ := hxP
    exact Set.disjoint_left.1 (D.families_disjoint p hp r hr) hxp hxr
  obtain ⟨K, hmavericks⟩ :=
    RegularProtectedAmbientMaverick.exists_protectedAmbientCompletion_of_ambientRemainder_with_mavericks
      hregular huncountable Gamma hlower hNorm
        (RegularLocalizedProtectedCleanSlice.LocalizedProtectedHalfwayGeometry.targetCarrier_small
          D hNorm huncountable hrho)
        D.targetPaths_carrier_roof D.stopover_trimmed D.stopover_separator
        D.original_quotient_unhindered hCroof hTessential
        hR D.remainder_terminalClean hRavoid hE₀small hY₀ hY₀tight
  have hclean : TightLinkageBetween Gamma (Gamma.source \ selected) T
      K.lifted := by
    rw [← hsource]
    exact K.liftedTight
  have hdisjoint : Disjoint (Gamma.vertexSet S₀.target)
      (Gamma.vertexSet K.lifted) := by
    change Disjoint X (Gamma.vertexSet K.lifted)
    exact K.liftedAvoids.symm
  obtain ⟨S, hStarget, hSclean⟩ :=
    RegularWeakProtectedSelectedClean.CleanTargetSlice.advanceClean_of_vertexDisjoint
      S₀ hclean hdisjoint
  refine ⟨K, S, hStarget, hSclean, ?_⟩
  rw [hSclean]
  exact hmavericks

private theorem walk_edgeSet_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) {a b : V}
    (p : DirectedPath.Walk D a b) :
    (p.lift hDE).edgeSet = p.edgeSet := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp [DirectedPath.Walk.lift, DirectedPath.Walk.edgeSet_cons, ih]

@[simp] private theorem liftStageFinitePath_edgeSet
    {G : DWeb V} {kappa : Cardinal.{u}}
    (L : G.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    (SliceSegmentCore.liftStageFinitePath L alpha p).edgeSet = p.edgeSet := by
  let Q := G.quotient (G.terminalFrontier (L.warpAt alpha))
  let hEss : ∀ {x y : V}, (L.stageWeb alpha).graph.Adj x y →
      Q.graph.Adj x y := fun {_ _} h ↦ Q.essentialPart_adj_imp h
  let hQuot : ∀ {x y : V}, Q.graph.Adj x y → G.graph.Adj x y :=
    fun {_ _} h ↦ G.quotient_adj_imp h
  change ((p.lift hEss).lift hQuot).edgeSet = p.edgeSet
  exact (walk_edgeSet_lift hQuot (p.walk.lift hEss)).trans
    (walk_edgeSet_lift hEss p.walk)

private theorem liftStagePath_isLadderFragment_of_ordinary
    {G : DWeb V} {kappa : Cardinal.{u}}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    {p : (L.stageWeb delta).DPath}
    (hpFinite : ∃ f : DirectedPath.FinitePath (L.stageWeb delta).graph,
      p = .inl f)
    (hp : ControlledSlices.IsLadderFragment (L.stageWeb delta)
      (SliceCandidate.ordinaryStageFamily hL hdeltaBeta) p) :
    ControlledSlices.IsLadderFragment G (L.warpAt beta)
      (L.liftStagePath delta p) := by
  obtain ⟨f, rfl⟩ := hpFinite
  obtain ⟨q, hqY, hfq⟩ := hp
  obtain ⟨g, hqg⟩ :=
    (SliceCandidate.ordinaryStageFamily_isLinkageBetween hL hdeltaBeta)
      |>.finiteCharacter hqY
  subst q
  have hgLift : L.liftStagePath delta
      (.inl g : (L.stageWeb delta).DPath) ∈
        SliceSegmentCore.liftStageFamily L delta
          (SliceCandidate.ordinaryStageFamily hL hdeltaBeta) :=
    ⟨.inl g, hqY, rfl⟩
  rw [SliceCandidate.liftStageFamily_ordinaryStageFamily hL hdeltaBeta] at hgLift
  obtain ⟨owner, howner, hgOwner⟩ :=
    SliceSegmentCore.segmentFamily_isLadderFragment
      (SliceCandidate.ordinaryStageIntervalRealization hL hdeltaBeta
        |>.toSegmentRealization) _ hgLift
  refine ⟨owner, howner, ?_⟩
  have hfLiftG :
      (SliceSegmentCore.liftStageFinitePath L delta f).IsSubpathOf
        (L.liftStagePath delta (.inl g : (L.stageWeb delta).DPath)) := by
    constructor
    · change (SliceSegmentCore.liftStageFinitePath L delta f).support ⊆
        (SliceSegmentCore.liftStageFinitePath L delta g).support
      rw [SliceSegmentCore.liftStageFinitePath_support,
        SliceSegmentCore.liftStageFinitePath_support]
      simpa only [DirectedPath.Path.support] using hfq.1
    · change (SliceSegmentCore.liftStageFinitePath L delta f).edgeSet ⊆
        (SliceSegmentCore.liftStageFinitePath L delta g).edgeSet
      rw [liftStageFinitePath_edgeSet, liftStageFinitePath_edgeSet]
      simpa only [DirectedPath.Path.edgeSet_finite] using hfq.2
  exact ⟨hfLiftG.1.trans hgOwner.1, hfLiftG.2.trans hgOwner.2⟩

/-- Stage lifting does not create more mavericks than were already present
against the ordinary stage family. -/
theorem mk_ambientMavericks_liftStageFamily_le
    {G : DWeb V} {kappa : Cardinal.{u}}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    {W : Set (L.stageWeb delta).DPath}
    (hWfinite : (L.stageWeb delta).HasFiniteCharacter W) :
    #(ControlledSlices.sliceMavericks G (L.warpAt beta)
        (SliceSegmentCore.liftStageFamily L delta W)) ≤
      #(ControlledSlices.sliceMavericks (L.stageWeb delta)
        (SliceCandidate.ordinaryStageFamily hL hdeltaBeta) W) := by
  have hsub : ControlledSlices.sliceMavericks G (L.warpAt beta)
      (SliceSegmentCore.liftStageFamily L delta W) ⊆
        SliceSegmentCore.liftStageFamily L delta
          (ControlledSlices.sliceMavericks (L.stageWeb delta)
            (SliceCandidate.ordinaryStageFamily hL hdeltaBeta) W) := by
    rintro _ ⟨⟨p, hpW, rfl⟩, hpNot⟩
    refine ⟨p, ⟨hpW, ?_⟩, rfl⟩
    intro hpOrdinary
    apply hpNot
    exact liftStagePath_isLadderFragment_of_ordinary hL hdeltaBeta
      (hWfinite hpW) hpOrdinary
  exact (Cardinal.mk_subtype_mono hsub).trans
    (SliceSegmentCore.mk_liftStageFamily_le L delta _)

/-- Retype a finite exact linkage to its literal terminal frontier. -/
theorem linkageBetween_terminalFrontier
    {Q : DWeb V} {A B : Set V} {P : Set Q.DPath}
    (hP : IsLinkageBetween Q A B P) :
    IsLinkageBetween Q A (Q.terminalFrontier P) P := by
  refine ⟨hP.isWarp, hP.finiteCharacter, hP.initialSet_eq,
    Set.Subset.rfl, ?_⟩
  intro p hp
  obtain ⟨f, rfl, hends, hsource⟩ := hP.endpointPure p hp
  have hfinish : f.finish ∈ Q.terminalFrontier P :=
    ⟨.inl f, hp, rfl⟩
  refine ⟨f, rfl, ?_, hsource⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxf, hxA | hxTerminal⟩
    · have hx : x ∈ f.support ∩ (A ∪ B) := ⟨hxf, Or.inl hxA⟩
      rw [hends] at hx
      exact hx
    · obtain ⟨q, hqP, hqx⟩ := hxTerminal
      have hqp : q = (.inl f : Q.DPath) := by
        by_contra hne
        exact Set.disjoint_left.1 (hP.isWarp hqP hp hne)
          (Q.terminal_mem_support hqx) hxf
      subst q
      change some f.finish = some x at hqx
      exact Set.mem_insert_iff.2
        (Or.inr (Set.mem_singleton_iff.2 (Option.some.inj hqx).symm))
  · rintro x (hxStart | hxFinish)
    · have hx : x = f.start := hxStart
      subst x
      have hstartA : f.start ∈ A := by
        rw [← hP.initialSet_eq]
        exact ⟨.inl f, hp, rfl⟩
      exact ⟨f.start_mem_support, Or.inl hstartA⟩
    · have hx : x = f.finish := Set.mem_singleton_iff.1 hxFinish
      subst x
      exact ⟨f.finish_mem_support, Or.inr hfinish⟩

private theorem firstHitPrefix_terminalClean
    {Q : DWeb V} {A C T : Set V} {P : Set Q.DPath}
    (hP : IsLinkageBetween Q A C P)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C T) :
    MeetsOnlyAtTerminal Q (SliceCandidate.firstHitPrefixFamily hP hsep) T := by
  rintro _ ⟨a, rfl⟩ x hx hxT
  have hx' : x ∈ (SliceCandidate.linkageFirstHitAt hP hsep a).support ∩ T :=
    ⟨hx, hxT⟩
  rw [SliceCandidate.linkageFirstHitAt_targetPure hP hsep a] at hx'
  exact congrArg some (Set.mem_singleton_iff.1 hx').symm

private theorem firstHitPrefix_vertexSet_subset
    {Q : DWeb V} {A C T : Set V} {P : Set Q.DPath}
    (hP : IsLinkageBetween Q A C P)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C T) :
    Q.vertexSet (SliceCandidate.firstHitPrefixFamily hP hsep) ⊆
      Q.vertexSet P := by
  rintro x ⟨_, ⟨a, rfl⟩, hx⟩
  exact ⟨SliceCandidate.linkageMemberAt hP a |>.1,
    SliceCandidate.linkageMemberAt hP a |>.2, by
      rw [SliceCandidate.linkageMemberAt_eq_finite]
      exact SliceCandidate.linkageFirstHitAt_support_subset hP hsep a hx⟩

private theorem terminalFrontier_subset_of_targetCarrier_roof
    {G Q : DWeb V} {A T : Set V} {P : Set Q.DPath}
    (hP : IsLinkageBetween Q A Q.target P)
    (hTarget : Q.target = G.target)
    (hroof : Q.vertexSet P ⊆ G.roof T) :
    Q.terminalFrontier P ⊆ T := by
  rintro b hb
  have hbTargetG : b ∈ G.target := hTarget ▸ hP.terminalFrontier_subset hb
  obtain ⟨p, hpP, hpb⟩ := hb
  exact SliceSpliceConstructor.target_mem_of_mem_roof hbTargetG
    (hroof ⟨p, hpP, Q.terminal_mem_support hpb⟩)

/-- The large-source protected branch yields a genuine weak split
candidate.  Every requested coordinate lies on the selected target track,
so the comparison links the empty complementary request. -/
theorem exists_weakSplitAnnularCandidate_of_localizedProtected
    {kappa : Cardinal.{u}} {G : DWeb V} {L : G.KappaLadder kappa}
    (hL : L.SliceGeometry)
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hdeltaBeta : delta < beta) (hbeta : beta ∉ L.phi)
    (hNorm : G.IsNormalized)
    {A₀ : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry (L.stageWeb delta) A₀ rho)
    (hrho : rho < kappa)
    (hrequest : request delta gamma ⊆ A₀)
    (hlower : RegularProtectedAmbientRebuild.ExtensionBelowFor
      (L.stageWeb delta) kappa)
    (hCroof : D.stopover ⊆
      (L.stageWeb delta).roof (L.frontier beta))
    (htargetRoof : (L.stageWeb delta).vertexSet D.targetPaths ⊆
      G.roof (L.frontier beta)) :
    ∃ C : RegularWeakSplitCandidate.WeakSplitFamilies G,
      RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
        G L request delta beta gamma C := by
  let Q := L.stageWeb delta
  let U := request delta gamma
  let T := L.frontier beta
  let selected := Q.initialSet D.targetPaths
  let E₀ := SliceCandidate.inessentialExtensionSources hL hdeltaBeta.le
  let Y₀ := SliceCandidate.ordinaryStageFamily hL hdeltaBeta.le
  have hNormQ : Q.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized hNorm L delta
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hTessential : Q.essential T = T :=
    hL.stageWeb_laterFrontier_isEssential hNoEnter hdeltaBeta
  have hE₀small : #E₀ < kappa :=
    SliceCandidate.mk_inessentialExtensionSources_lt_of_not_mem_phi
      hL hdeltaBeta.le hbeta
  have hY₀ : IsLinkageBetween Q (Q.source \ E₀) T Y₀ := by
    simpa only [Q, T, E₀, Y₀, DWeb.KappaLadder.frontier] using
      (SliceCandidate.ordinaryStageFamily_isLinkageBetween hL hdeltaBeta.le)
  have hY₀tight : MeetsOnlyAtTerminal Q Y₀ T :=
    SliceCandidate.ordinaryStageFamily_meetsOnlyAtTerminal hL hdeltaBeta.le
  obtain ⟨K, Sstage, hStarget, hSclean, hmavericksStage⟩ :=
    LocalizedProtectedHalfwayGeometry.exists_advancedCleanTargetSlice_with_mavericks
      D hL.regular hL.uncountable hrho hlower hNormQ hCroof hTessential
        hE₀small hY₀ hY₀tight
  have hUselected : U ⊆ selected :=
    hrequest.trans D.designated_initial
  have hselectedSource : selected ⊆ Q.source :=
    D.targetPaths_initial_subset_source
  have hP : IsLinkageBetween Q selected Q.target D.targetPaths :=
    RegularLocalizedProtectedCleanSlice.LocalizedProtectedHalfwayGeometry.targetPaths_isLinkageBetween
      D hNormQ
  have hterminal : Q.terminalFrontier D.targetPaths ⊆ T :=
    terminalFrontier_subset_of_targetCarrier_roof
      (G := G) (Q := Q) hP rfl htargetRoof
  have hPterminal : IsLinkageBetween Q selected
      (Q.terminalFrontier D.targetPaths) D.targetPaths :=
    linkageBetween_terminalFrontier hP
  have hsepP : RelationalRoof.Separates Q.graph.Adj selected
      (Q.terminalFrontier D.targetPaths) T := by
    intro _ t p _ ht
    exact ⟨t, p.end_mem_support, hterminal ht⟩
  let Pprefix := SliceCandidate.firstHitPrefixFamily hPterminal hsepP
  have hprefix : IsLinkageBetween Q selected T Pprefix :=
    SliceCandidate.firstHitPrefixFamily_isLinkageBetween hPterminal hsepP
  have hprefixTight : MeetsOnlyAtTerminal Q Pprefix T :=
    firstHitPrefix_terminalClean hPterminal hsepP
  have hclean : IsLinkageBetween Q (Q.source \ selected) T Sstage.clean :=
    RegularLiftCleanTargetSlice.clean_isLinkageBetween Sstage
  have hprefixCarrier : Q.vertexSet Pprefix ⊆ Q.vertexSet D.targetPaths :=
    firstHitPrefix_vertexSet_subset hPterminal hsepP
  have htargetCleanDisjoint : Disjoint (Q.vertexSet D.targetPaths)
      (Q.vertexSet Sstage.clean) := by
    rw [hSclean]
    exact K.liftedAvoids.symm
  have hprefixCleanDisjoint : Disjoint (Q.vertexSet Pprefix)
      (Q.vertexSet Sstage.clean) :=
    htargetCleanDisjoint.mono hprefixCarrier Set.Subset.rfl
  have hcomparisonRaw : IsLinkageBetween Q
      (selected ∪ (Q.source \ selected)) T (Pprefix ∪ Sstage.clean) :=
    SingularRetargetedRow.linkageBetween_union_of_vertexSet_disjoint
      Q hprefix hclean hprefixCleanDisjoint
  have hcomparison : IsLinkageBetween Q Q.source T
      (Pprefix ∪ Sstage.clean) := by
    rw [Set.union_sdiff_cancel hselectedSource] at hcomparisonRaw
    exact hcomparisonRaw
  have hcomparisonTight : TightLinkageBetween Q Q.source T
      (Pprefix ∪ Sstage.clean) := by
    refine ⟨hcomparison, ?_⟩
    intro p hp
    exact hp.elim (hprefixTight p) (Sstage.clean_terminal_only p)
  have hremainingLinks : LinksToTarget Q (Pprefix ∪ Sstage.clean)
      (U \ selected) := by
    intro x hx
    exact (hx.2 (hUselected hx.1)).elim
  have hseparator : IsSeparatorFrom Q Q.source T := by
    simpa only [Q, T, DWeb.KappaLadder.frontier] using
      (RegularSliceStageCompletion.later_frontier_separates_stageWeb
        hL.frontierChronology hdeltaBeta)
  obtain ⟨hcomparisonAmbient, hcomparisonLinks, hcomparisonRegion⟩ :=
    RegularSliceStageLift.tightAnnularLinkage_liftStageFamily
      hL.roofsSourceAtStages hL.frontierChronology hdeltaBeta
        hcomparisonTight hremainingLinks hseparator
  let S := RegularLiftCleanTargetSlice.liftStageSlice L delta Sstage
  let comparison := SliceSegmentCore.liftStageFamily L delta
    (Pprefix ∪ Sstage.clean)
  have hannular : SliceSplice.IsAnnularSlice G L comparison delta beta
      (U \ selected) :=
    ⟨⟨hcomparisonAmbient.1, hcomparisonLinks⟩, hcomparisonRegion⟩
  have hcleanSubset : S.clean ⊆ comparison := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, Or.inr hp, rfl⟩
  have htargetSmallStage : #D.targetPaths < kappa :=
    D.targetPaths_card.trans_lt hrho
  have htargetSmall : #S.target < kappa :=
    by
      change #(SliceSegmentCore.liftStageFamily L delta Sstage.target) < kappa
      rw [hStarget]
      exact (SliceSegmentCore.mk_liftStageFamily_le L delta D.targetPaths).trans_lt
        htargetSmallStage
  have hcleanLinks : LinksToTarget G S.clean (U \ selected) := by
    intro x hx
    exact (hx.2 (hUselected hx.1)).elim
  have hintervals : SliceCandidate.HasStageIntervalSegments G L S.clean
      delta beta := by
    have hall := SliceCandidate.linkage_hasStageIntervalSegments
      hL hdeltaBeta.le hcomparisonAmbient.1
    intro p hp hfragment
    exact hall p (hcleanSubset hp) hfragment
  have hmavericks : #(ControlledSlices.sliceMavericks G (L.warpAt beta)
      S.clean) < kappa := by
    change #(ControlledSlices.sliceMavericks G (L.warpAt beta)
      (SliceSegmentCore.liftStageFamily L delta Sstage.clean)) < kappa
    exact (mk_ambientMavericks_liftStageFamily_le hL hdeltaBeta.le
      (fun {_} hp ↦ Sstage.finiteCharacter (Or.inr hp))).trans_lt
        hmavericksStage
  have htargetRoofAmbient : G.vertexSet S.target ⊆ G.roof T := by
    rw [RegularLiftCleanTargetSlice.liftStageSlice.target_vertexSet]
    rw [hStarget]
    exact htargetRoof
  refine ⟨⟨S.target, S.clean, comparison⟩, ?_⟩
  unfold RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
  dsimp only [U, T]
  refine ⟨selected, ?_, S, rfl, rfl, hannular, hcleanSubset,
    htargetRoofAmbient, htargetSmall, hcleanLinks, hintervals, hmavericks⟩
  exact RegularWeakSplitCandidate.stagePersistent_subset_request
    G (L.frontier beta) (request delta gamma) |>.trans hUselected

#print axioms LocalizedProtectedHalfwayGeometry.exists_advancedCleanTargetSlice_with_mavericks
#print axioms exists_weakSplitAnnularCandidate_of_localizedProtected

end RegularLocalizedProtectedCandidate
end CardinalInduction
end Erdos599

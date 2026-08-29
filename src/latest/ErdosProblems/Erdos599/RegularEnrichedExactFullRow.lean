/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularFixedStageTargetLinkingAnnular
import ErdosProblems.Erdos599.RegularStarMaverickBound
import ErdosProblems.Erdos599.RegularWeakFullRowSplit
import ErdosProblems.Erdos599.HalfwayScheduledSafePathTransaction
import ErdosProblems.Erdos599.SliceSuffixFromAux

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularEnrichedExactFullRow

open SliceCandidate SliceSpliceSource

universe u

variable {V : Type u}

private theorem liftNormalizedPath_normalizedRestrictedPath
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : MeetsOnlyAtTerminal Q F T) (p : F) :
    SliceDeltaLift.liftNormalizedPath Q C D T F
        (SliceDeltaLift.normalizedRestrictedPath Q C D T
          hF hsource htarget p) = p.1 := by
  obtain ⟨f, hpf⟩ := hF.finiteCharacter p.2
  have hfiniteMember :
      Q.finiteMemberPath F hF.finiteCharacter p = f := by
    apply Sum.inl.inj
    exact (Q.finiteMemberPath_eq F hF.finiteCharacter p).symm.trans hpf
  rw [hpf]
  apply congrArg Sum.inl
  let q := SliceDeltaLift.normalizedRestrictedFiniteMember Q C D T
    hF hsource htarget p
  let lifted := q.lift
    (fun {_ _} (e : (SliceRestrictedDelta.normalizedDelta
      Q C D T F).graph.Adj _ _) => e.1.1)
  change lifted = f
  have hstart : lifted.start = f.start := by
    change q.start = f.start
    rw [SliceDeltaLift.start_normalizedRestrictedFiniteMember,
      hpf]
    rfl
  have hfinish : lifted.finish = f.finish := by
    change q.finish = f.finish
    apply Option.some.inj
    rw [SliceDeltaLift.finish_normalizedRestrictedFiniteMember, hpf]
    rfl
  have hsupport : lifted.walk.support = f.walk.support := by
    rw [show lifted.walk.support = q.walk.support by
      exact DirectedPath.Walk.support_lift _ q.walk]
    dsimp only [q, SliceDeltaLift.normalizedRestrictedFiniteMember,
      SliceRestrictedDelta.normalizedDelta]
    change ((SliceRestrictedDelta.delta Q C D T F).normalizeWalk
      (SliceDeltaLift.restrictedFiniteMember Q C D T hF p).walk _ _).support =
        f.walk.support
    rw [(SliceRestrictedDelta.delta Q C D T F).support_normalizeWalk]
    dsimp only [SliceDeltaLift.restrictedFiniteMember]
    change ((Q.finiteMemberPath F hF.finiteCharacter p).walk
      |>.restrictGraphOnSupport _).support = f.walk.support
    rw [DirectedPath.Walk.support_restrictGraphOnSupport, hfiniteMember]
  rcases lifted with ⟨a, b, w, hw⟩
  rcases f with ⟨c, d, z, hz⟩
  dsimp only at hstart hfinish hsupport ⊢
  subst c
  subst d
  have hwz : w = z := Erdos599.DirectedPath.Walk.eq_of_support_eq w z hsupport
  subst z
  rfl

theorem star_wholeExchange_suffix_isLadderFragment
    (Q : DWeb V) {A C T E : Set V} {W Y R : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (hEsub : E ⊆ A)
    (hRwarp : Q.IsWarp R)
    (hcompat : Q.StarCompatible
      (SliceCandidate.wholeComponentMixedFamily Q W
        (SliceCandidate.firstHitPrefixFamily hY hsep) Y E) R)
    (p : SliceCandidate.wholeComponentMixedFamily Q W
      (SliceCandidate.firstHitPrefixFamily hY hsep) Y E)
    (q : Q.DPath)
    (hqR : q ∈ R)
    (hq : q ∈ SliceCandidate.selectedSuffixFamily hY hsep
      (SliceCandidate.wholeNonexceptionalPrefixSources hY hsep W))
    (hpq : Q.terminal? p.1 = some q.initial) :
    ControlledSlices.IsLadderFragment Q Y
      (Q.starPath hcompat p) := by
  classical
  let D := SliceCandidate.exceptionalComponentVertices Q W Y E
  let P := SliceCandidate.firstHitPrefixFamily hY hsep
  let W' := SliceCandidate.wholeComponentMixedFamily Q W P Y E
  let S := SliceCandidate.wholeNonexceptionalPrefixSources hY hsep W
  let F := SliceCandidate.selectedSuffixFamily hY hsep S
  change q ∈ F at hq
  obtain ⟨a, hqa⟩ := hq
  have hqEq : q =
      (.inl (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1) :
        Q.DPath) := hqa.symm
  subst q
  rcases p.2 with hpOld | hpPrefix
  · have hpD : p.1.support ⊆ D :=
      SliceCandidate.path_support_subset_exceptionalComponents_left
        hW.finiteCharacter hpOld.1 p.1.initial_mem_support hpOld.2
    have hxP :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          p.1.support := by
      apply Q.terminal_mem_support
      change Q.terminal? p.1 = some
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start at hpq
      exact hpq
    have hwholeY :
        (.inl (SliceCandidate.linkageFiniteAt hY a.1) : Q.DPath) ∈ Y := by
      rw [← SliceCandidate.linkageMemberAt_eq_finite]
      exact (SliceCandidate.linkageMemberAt hY a.1).2
    have hxWhole :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          (SliceCandidate.linkageFiniteAt hY a.1).support :=
      SliceCandidate.linkageSuffixAtFirstHit_support_subset hY hsep a.1
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start_mem_support
    have hwholeD : (SliceCandidate.linkageFiniteAt hY a.1).support ⊆ D :=
      SliceCandidate.path_support_subset_exceptionalComponents_right
        hY.finiteCharacter hwholeY hxWhole (hpD hxP)
    exact False.elim <| a.2 <| by
      change a.1.1 ∈ D
      rw [← SliceCandidate.linkageFiniteAt_start hY a.1]
      exact hwholeD
        (SliceCandidate.linkageFiniteAt hY a.1).start_mem_support
  · obtain ⟨b, hpb⟩ := hpPrefix.1
    have hpEq : p.1 =
        (.inl (SliceCandidate.linkageFirstHitAt hY hsep b) : Q.DPath) :=
      hpb.symm
    have hxP :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          (SliceCandidate.linkageFirstHitAt hY hsep b).support := by
      have hxP' :
          (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
            p.1.support := by
        apply Q.terminal_mem_support
        change Q.terminal? p.1 = some
          (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start at hpq
        exact hpq
      rw [hpEq] at hxP'
      exact hxP'
    have hxWholeA :
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start ∈
          (SliceCandidate.linkageFiniteAt hY a.1).support :=
      SliceCandidate.linkageSuffixAtFirstHit_support_subset hY hsep a.1
        (SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1).start_mem_support
    have hba : b = a.1 := by
      by_contra hne
      have hm : (SliceCandidate.linkageMemberAt hY b).1 ≠
          (SliceCandidate.linkageMemberAt hY a.1).1 := by
        intro heq
        apply hne
        apply SliceCandidate.linkageMemberAt_injective hY
        exact Subtype.ext heq
      exact False.elim <| Set.disjoint_left.1
        (hY.isWarp (SliceCandidate.linkageMemberAt hY b).2
          (SliceCandidate.linkageMemberAt hY a.1).2 hm)
        (by
          rw [SliceCandidate.linkageMemberAt_eq_finite]
          exact SliceCandidate.linkageFirstHitAt_support_subset hY hsep b hxP)
        (by
          rw [SliceCandidate.linkageMemberAt_eq_finite]
          exact hxWholeA)
    subst b
    let first := SliceCandidate.linkageFirstHitAt hY hsep a.1
    let suffix := SliceCandidate.linkageSuffixAtFirstHit hY hsep a.1
    let whole := SliceCandidate.linkageFiniteAt hY a.1
    have hpPrefix' : (.inl first : Q.DPath) ∈
        SliceCandidate.initialPart Q P Dᶜ := by
      change (.inl (SliceCandidate.linkageFirstHitAt hY hsep a.1) :
          Q.DPath) ∈ SliceCandidate.initialPart Q
            (SliceCandidate.firstHitPrefixFamily hY hsep)
            (SliceCandidate.exceptionalComponentVertices Q W Y E)ᶜ
      rw [← hpEq]
      exact hpPrefix
    let p' : W' := ⟨(.inl first : Q.DPath), Or.inr hpPrefix'⟩
    have hpp' : p = p' := Subtype.ext hpEq
    rw [hpp']
    change ControlledSlices.IsLadderFragment Q Y
      (Q.starPath hcompat p')
    have hmatch : ∃ r ∈ R, r.initial = first.finish := by
      exact ⟨.inl suffix, hqR, by
        change suffix.start = first.finish
        exact SliceCandidate.linkageSuffixAtFirstHit_start hY hsep a.1⟩
    dsimp only [p', DWeb.starPath]
    rw [dif_pos hmatch]
    let r := Classical.choose hmatch
    have hrR : r ∈ R := (Classical.choose_spec hmatch).1
    have hrStart : r.initial = first.finish :=
      (Classical.choose_spec hmatch).2
    have hsuffixStart :
        DirectedPath.Path.initial (.inl suffix : Q.DPath) = first.finish := by
      change suffix.start = first.finish
      exact SliceCandidate.linkageSuffixAtFirstHit_start hY hsep a.1
    have hrEq : r = (.inl suffix : Q.DPath) := by
      by_contra hne
      exact Set.disjoint_left.1
        (hRwarp hrR hqR hne)
        r.initial_mem_support
        (hrStart.trans hsuffixStart.symm ▸
          (show DirectedPath.Path.initial (.inl suffix : Q.DPath) ∈
            DirectedPath.Path.support (.inl suffix : Q.DPath) from
              DirectedPath.Path.initial_mem_support
                (.inl suffix : Q.DPath)))
    change Classical.choose hmatch = (.inl suffix : Q.DPath) at hrEq
    simp only [hrEq]
    have hinter : first.support ∩ suffix.support ⊆ {first.finish} := by
      intro x hx
      exact (hcompat (.inl first) (Or.inr hpPrefix')
        (.inl suffix) hqR x hx.1 hx.2).1 |> fun h ↦
          Set.mem_singleton_iff.2 (Option.some.inj h).symm
    refine ⟨.inl whole, ?_, ?_⟩
    · rw [← SliceCandidate.linkageMemberAt_eq_finite]
      exact (SliceCandidate.linkageMemberAt hY a.1).2
    · change DirectedPath.Path.IsSubpathOf
        (.inl (first.appendFinite suffix (by
          simpa only [first, suffix,
            SliceCandidate.linkageSuffixAtFirstHit_start]) hinter))
        (.inl whole)
      have hfirstSub : first.IsSubpathOf (.inl whole : Q.DPath) :=
        ⟨SliceCandidate.linkageFirstHitAt_support_subset hY hsep a.1,
          SliceCandidate.linkageFirstHitAt_edgeSet_subset hY hsep a.1⟩
      have hsuffixSub : suffix.IsSubpathOf (.inl whole : Q.DPath) := by
        dsimp only [suffix, whole, SliceCandidate.linkageSuffixAtFirstHit]
        exact DirectedPath.FinitePath.suffixFrom_isSubpathOf _ _ _
      constructor
      · change (first.appendFinite suffix _ hinter).support ⊆ whole.support
        rw [DirectedPath.FinitePath.support_appendFinite_eq_union]
        exact Set.union_subset hfirstSub.1 hsuffixSub.1
      · change (first.appendFinite suffix _ hinter).edgeSet ⊆ whole.edgeSet
        rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
        exact Set.union_subset hfirstSub.2 hsuffixSub.2

private theorem mk_liftNormalizedFamily_sdiff_le
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {R Good : Set (SliceRestrictedDelta.normalizedDelta Q C D T F).DPath} :
    #(↥(Set.diff (SliceDeltaLift.liftNormalizedFamily Q C D T F R)
        (SliceDeltaLift.liftNormalizedFamily Q C D T F Good))) ≤
      #(↥(R \ Good)) := by
  let badLift := SliceDeltaLift.liftNormalizedFamily Q C D T F (R \ Good)
  have hsub : Set.diff (SliceDeltaLift.liftNormalizedFamily Q C D T F R)
      (SliceDeltaLift.liftNormalizedFamily Q C D T F Good) ⊆ badLift := by
    rintro q ⟨hqR, hqGood⟩
    obtain ⟨p, rfl⟩ := hqR
    refine ⟨⟨p.1, p.2, ?_⟩, rfl⟩
    intro hp
    exact hqGood ⟨⟨p.1, hp⟩, rfl⟩
  exact (Cardinal.mk_subtype_mono hsub).trans Cardinal.mk_range_le

@[simp] private theorem liftStageFinitePath_edgeSet
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (p : DirectedPath.FinitePath (L.stageWeb alpha).graph) :
    (SliceSegmentCore.liftStageFinitePath L alpha p).edgeSet = p.edgeSet := by
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt alpha))
  let hEss : ∀ {x y : V}, (L.stageWeb alpha).graph.Adj x y →
      Q.graph.Adj x y := fun {_ _} h ↦ Q.essentialPart_adj_imp h
  let hQuot : ∀ {x y : V}, Q.graph.Adj x y →
      Gamma.graph.Adj x y := fun {_ _} h ↦ Gamma.quotient_adj_imp h
  have walk_edgeSet_lift_local {D E : Digraph V}
      (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) :
      ∀ {a b : V} (w : DirectedPath.Walk D a b),
        (w.lift hDE).edgeSet = w.edgeSet := by
    intro a b w
    induction w with
    | nil => rfl
    | cons h w ih =>
        simp [DirectedPath.Walk.lift, DirectedPath.Walk.edgeSet_cons, ih]
  change ((p.lift hEss).lift hQuot).edgeSet = p.edgeSet
  exact (walk_edgeSet_lift_local hQuot (p.walk.lift hEss)).trans
    (walk_edgeSet_lift_local hEss p.walk)

private theorem liftStagePath_isLadderFragment_of_ordinary
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    {p : (L.stageWeb delta).DPath}
    (hpFinite : ∃ f : DirectedPath.FinitePath (L.stageWeb delta).graph,
      p = .inl f)
    (hp : ControlledSlices.IsLadderFragment (L.stageWeb delta)
      (SliceCandidate.ordinaryStageFamily hL hdeltaBeta) p) :
    ControlledSlices.IsLadderFragment Gamma (L.warpAt beta)
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
        |>.toSegmentRealization)
      _ hgLift
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
  constructor
  · exact hfLiftG.1.trans hgOwner.1
  · exact hfLiftG.2.trans hgOwner.2

private theorem mk_ambientMavericks_liftStageFamily_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    {W : Set (L.stageWeb delta).DPath}
    (hWfinite : (L.stageWeb delta).HasFiniteCharacter W) :
    #(ControlledSlices.sliceMavericks Gamma (L.warpAt beta)
        (SliceSegmentCore.liftStageFamily L delta W)) ≤
      #(ControlledSlices.sliceMavericks (L.stageWeb delta)
        (SliceCandidate.ordinaryStageFamily hL hdeltaBeta) W) := by
  have hsub : ControlledSlices.sliceMavericks Gamma (L.warpAt beta)
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

/-- The exact-frontier half-way row produces the complete annular datum
needed by the source-9.15 table: a tight full row preserving every request,
whose ambient lift lies in the displayed annulus and has fewer than
`kappa` mavericks.  The proof keeps the whole-component suffix provenance
through the normalized-Delta fill; this is the information forgotten by
the earlier target-link-only wrapper. -/
theorem HalfwayPayload.exists_enrichedTargetLinkingAnnular_of_exactFrontier
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) {U : Set V}
    (D : HalfwayPayload L delta U)
    (hUfrontier : U ⊆ L.frontier delta) (hUsmall : #U < kappa)
    (hCroof : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hexact : (L.stageWeb delta).terminalFrontier D.W = D.C) :
    ∃ W : Set (L.stageWeb delta).DPath,
      TightLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U ∧
        Gamma.vertexSet (SliceSegmentCore.liftStageFamily L delta W) ⊆
          L.lowerRegion delta ∩ L.upperRegion beta ∧
        #(ControlledSlices.sliceMavericks Gamma (L.warpAt beta)
          (SliceSegmentCore.liftStageFamily L delta W)) < kappa := by
  let Q := L.stageWeb delta
  let E₀ := SliceCandidate.inessentialExtensionSources hL hdeltaBeta.le
  let E := U ∪ E₀
  let Y₀ := SliceCandidate.ordinaryStageFamily hL hdeltaBeta.le
  let Y := initialRestriction Q Y₀ (Q.source \ E)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNormQ : Q.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized hNorm L delta
  have hY₀ : IsLinkageBetween Q (L.frontier delta \ E₀)
      (L.frontier beta) Y₀ :=
    SliceCandidate.ordinaryStageFamily_isLinkageBetween hL hdeltaBeta.le
  have hQsource : Q.source = L.frontier delta := rfl
  have hYsource : Q.source \ E ⊆ L.frontier delta \ E₀ := by
    rintro x ⟨hxSource, hxE⟩
    refine ⟨hQsource ▸ hxSource, ?_⟩
    intro hxE₀
    exact hxE (Or.inr hxE₀)
  have hY : IsLinkageBetween Q (Q.source \ E)
      (L.frontier beta) Y :=
    isLinkageBetween_initialRestriction hY₀ hYsource
  have hYtight : MeetsOnlyAtTerminal Q Y (L.frontier beta) := by
    intro p hp
    exact SliceCandidate.ordinaryStageFamily_meetsOnlyAtTerminal
      hL hdeltaBeta.le p hp.1
  have hTessential : Q.essential (L.frontier beta) = L.frontier beta :=
    RegularCandidateProvider.stageWeb_laterFrontier_isEssential
      hL hNoEnter hdeltaBeta
  have hsepFull : RelationalRoof.Separates Q.graph.Adj
      Q.source (L.frontier beta) D.C :=
    SliceSegmentCore.separates_between_of_roofed Q
      hTessential D.separator hCroof
  have hsep : RelationalRoof.Separates Q.graph.Adj
      (Q.source \ E) (L.frontier beta) D.C := by
    intro a t p ha ht
    exact hsepFull p ha.1 ht
  have hEsub : E ⊆ Q.source := by
    intro x hx
    rcases hx with hxU | hxE₀
    · rw [hQsource]
      exact hUfrontier hxU
    · rw [hQsource]
      exact hxE₀.1
  have hEsmall : #E < kappa := by
    apply (Cardinal.mk_union_le U E₀).trans_lt
    exact Cardinal.add_lt_of_lt hregular.aleph0_le hUsmall
      (SliceCandidate.mk_inessentialExtensionSources_lt_of_not_mem_phi
        hL hdeltaBeta.le hbeta)
  have hclean : SingularContinuation.TerminalCleanAt Q D.W D.C := by
    have hcleanFrontier : SingularContinuation.TerminalCleanAt Q D.W
        (Q.terminalFrontier D.W) :=
      SingularExtension.terminalCleanAt_terminalFrontier_of_isWarp
        D.linkage.isWarp
    simpa only [Q, hexact] using hcleanFrontier
  let P := SliceCandidate.firstHitPrefixFamily hY hsep
  let W' := SliceCandidate.wholeComponentMixedFamily Q D.W P Y E
  let E' := SliceCandidate.wholeExchangeExceptionalTerminals Q D.W Y E
  let S := SliceCandidate.wholeNonexceptionalPrefixSources hY hsep D.W
  let F := SliceCandidate.selectedSuffixFamily hY hsep S
  have hW' : IsLinkageBetween Q Q.source D.C W' :=
    SliceCandidate.wholeComponentMixedFamily_isLinkageBetween
      Q D.linkage hY hsep hEsub
  have hlinks' : LinksToTarget Q W' U :=
    SliceCandidate.wholeComponentMixedFamily_linksToTarget Q
      D.linkage.finiteCharacter Set.subset_union_left D.links
  have hW'clean : SingularContinuation.TerminalCleanAt Q W' D.C :=
    RegularCleanExchange.wholeComponentMixedFamily_terminalClean
      hclean hY hsep
  have hE'sub : E' ⊆ Q.terminalFrontier W' := by
    intro x hx
    change x ∈ Q.terminalFrontier
      (SliceCandidate.initialPart Q D.W
        (SliceCandidate.exceptionalComponentVertices Q D.W Y E)) at hx
    change x ∈ Q.terminalFrontier
      (SliceCandidate.initialPart Q D.W
          (SliceCandidate.exceptionalComponentVertices Q D.W Y E) ∪
        SliceCandidate.initialPart Q P
          (SliceCandidate.exceptionalComponentVertices Q D.W Y E)ᶜ)
    rw [DWeb.terminalFrontier_union]
    exact Or.inl hx
  have hE'small : #E' < kappa :=
    SliceCandidate.wholeExchangeExceptionalTerminals_small Q hregular
      huncountable D.linkage.isWarp hY.isWarp D.linkage.finiteCharacter
        hY.finiteCharacter hEsmall
  have hsource : Q.terminalFrontier W' \ E' =
      SliceCandidate.selectedSuffixStartSet hY hsep S := by
    exact (SliceCandidate.terminalFrontier_wholeMixed_sdiff_exceptional_eq
      Q D.linkage hY hsep).trans
        (SliceCandidate.terminalFrontier_wholeNonexceptionalPrefix_eq_suffixStartSet
          hY hsep)
  have hF : IsLinkageBetween Q (Q.terminalFrontier W' \ E')
      (L.frontier beta) F := by
    rw [hsource]
    exact SliceCandidate.selectedSuffixFamily_isLinkageBetween hY hsep S
  have hFtight : MeetsOnlyAtTerminal Q F (L.frontier beta) :=
    SliceCandidate.selectedSuffixFamily_meetsOnlyAtTerminal
      hY hYtight hsep S
  have hWF : Q.StarCompatible W' F :=
    SliceCandidate.wholeComponentExchange_starCompatible
      Q D.linkage hY hsep
  have hCsource : (Q.quotient D.C).source = D.C :=
    SingularContinuation.quotient_source_eq_stopover Q
      D.separator D.trimmed
  obtain ⟨R, hcompat, hR, hresult, hRsmall⟩ :=
    RegularCandidateProvider.exists_tightNormalizedCleanContinuation
      hlower hregular huncountable Q hNormQ
        (by simpa only [Q, hQsource] using
          (Set.Subset.rfl : L.frontier delta ⊆ L.frontier delta))
        hW' D.separator hW'clean rfl hW'.terminalFrontier_subset
          D.trimmed hCsource hCroof D.quotientUnhindered hTessential
            hE'sub hE'small hF hFtight hWF
  let hsourcePure : ∀ p ∈ F,
      p.support ∩ Q.terminalFrontier W' ⊆ {p.initial} :=
    SliceDeltaLift.sourcePure_of_starCompatible Q Set.Subset.rfl hWF
  let Fdelta := SliceDeltaLift.normalizedRestrictedFamily Q D.C
    (Q.terminalFrontier W') (L.frontier beta) hF hsourcePure hFtight
  let GoodDelta := R ∩ Fdelta
  let Rlift := SliceDeltaLift.liftNormalizedFamily Q D.C
    (Q.terminalFrontier W') (L.frontier beta) F R
  let Good := SliceDeltaLift.liftNormalizedFamily Q D.C
    (Q.terminalFrontier W') (L.frontier beta) F GoodDelta
  have hRlift : IsLinkageBetween Q (Q.terminalFrontier W')
      (L.frontier beta) Rlift :=
    SliceDeltaLift.IsLinkageBetween.liftNormalizedDelta Q D.C
      (Q.terminalFrontier W') (L.frontier beta) F hR
  have hGood : Good ⊆ Rlift := by
    rintro _ ⟨r, rfl⟩
    exact ⟨⟨r.1, r.2.1⟩, rfl⟩
  have hbadDelta : #(↥(R \ GoodDelta)) < kappa := by
    simpa only [GoodDelta, Fdelta, Set.sdiff_self_inter]
      using hRsmall
  have hbad : #(↥(Rlift \ Good)) < kappa :=
    (mk_liftNormalizedFamily_sdiff_le Q D.C
      (Q.terminalFrontier W') (L.frontier beta) F).trans_lt hbadDelta
  have hordinary : ∀ (p : W') (q : Q.DPath), q ∈ Good →
      Q.terminal? p.1 = some q.initial →
        ControlledSlices.IsLadderFragment Q Y₀
          (Q.starPath hcompat p) := by
    intro p q hqGood hpq
    have hqRlift : q ∈ Rlift := hGood hqGood
    obtain ⟨r, hqr⟩ := hqGood
    have hrFdelta : r.1 ∈ Fdelta := r.2.2
    obtain ⟨f, hfr⟩ := hrFdelta
    have hliftEq : SliceDeltaLift.liftNormalizedPath Q D.C
        (Q.terminalFrontier W') (L.frontier beta) F r.1 = f.1 := by
      rw [← hfr]
      exact liftNormalizedPath_normalizedRestrictedPath Q D.C
        (Q.terminalFrontier W') (L.frontier beta) hF hsourcePure
          hFtight f
    have hqEq : q = f.1 := hqr.symm.trans hliftEq
    have hpq' : Q.terminal? p.1 = some f.1.initial := by
      rw [← hqEq]
      exact hpq
    have hfRlift : f.1 ∈ Rlift := by
      rw [← hqEq]
      exact hqRlift
    obtain ⟨owner, hownerY, hfragment⟩ :=
      star_wholeExchange_suffix_isLadderFragment Q D.linkage hY
        hsep hEsub hRlift.isWarp hcompat p f.1 hfRlift f.2 hpq'
    exact ⟨owner, hownerY.1, hfragment⟩
  have hW'exact : IsLinkageBetween Q Q.source
      (Q.terminalFrontier W') W' :=
    SingularFirstHitCleanPrefix.isLinkageBetween_terminalFrontier_of_finite_full
      hW'.isWarp hW'.finiteCharacter hW'.initialSet_eq
  have hmavericksStage :
      #(ControlledSlices.sliceMavericks Q Y₀ (Q.star hcompat)) <
        kappa :=
    RegularStarMaverickBound.mk_sliceMavericks_star_lt hW'exact hRlift
      hcompat hGood hbad hordinary
  have hmavericksAmbient :
      #(ControlledSlices.sliceMavericks Gamma (L.warpAt beta)
        (SliceSegmentCore.liftStageFamily L delta (Q.star hcompat))) <
          kappa :=
    (mk_ambientMavericks_liftStageFamily_le hL hdeltaBeta.le
      hresult.1.finiteCharacter).trans_lt hmavericksStage
  have hlowerRegion : Gamma.vertexSet
      (SliceSegmentCore.liftStageFamily L delta (Q.star hcompat)) ⊆
        L.lowerRegion delta :=
    RegularCandidateProvider.liftStageFamily_vertexSet_subset_lowerRegion
      hL hresult.1 (by
        simpa only [Q, hQsource] using
          (Set.Subset.rfl : L.frontier delta ⊆ L.frontier delta))
  have hresultAmbient : IsLinkageBetween Gamma (L.frontier delta)
      (L.frontier beta)
      (SliceSegmentCore.liftStageFamily L delta (Q.star hcompat)) :=
    SliceDeltaLift.IsLinkageBetween.liftStageFamily hresult.1
  have hresultAmbientTight : MeetsOnlyAtTerminal Gamma
      (SliceSegmentCore.liftStageFamily L delta (Q.star hcompat))
      (L.frontier beta) :=
    SliceDeltaLift.meetsOnlyAtTerminal_liftStageFamily hresult.2
  have hupperRegion : Gamma.vertexSet
      (SliceSegmentCore.liftStageFamily L delta (Q.star hcompat)) ⊆
        L.upperRegion beta := by
    exact SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial
      Gamma hresultAmbient (hL.frontierChronology hdeltaBeta)
        hresultAmbientTight
  have hlinksResult : LinksToTarget Q (Q.star hcompat) U := by
    have hforward : Q.ForwardExtension W' (Q.star hcompat) :=
      Q.forwardExtension_star hcompat
    exact SingularExtension.linksToTarget_of_forwardExtension hNormQ
      (Set.subset_union_left.trans hEsub) hlinks' hforward
        hresult.1.finiteCharacter
  refine ⟨Q.star hcompat, ?_, hlinksResult, ?_, hmavericksAmbient⟩
  · simpa only [Q, hQsource] using hresult
  · exact fun x hx ↦ ⟨hlowerRegion hx, hupperRegion hx⟩

end RegularEnrichedExactFullRow
end CardinalInduction
end Erdos599

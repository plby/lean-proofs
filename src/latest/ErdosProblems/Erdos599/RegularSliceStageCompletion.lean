/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSliceStageLift
import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SingularExtension

/-!
# Completing the half-way linkage at a later regular frontier

The half-way clause supplies a source--stop-over linkage `W`.  Once its
stop-over is roofed by a later stage boundary, the lower extension clause
completes an ordinary linkage in the quotient by that stop-over.  This file
joins the two linkages and, crucially, retains the original target-link
certificates.  The latter follows because source star is a finite-character
forward extension in a normalized stage web.

The final theorem combines this stage-local completion with
`RegularSliceStageLift`: its output is the tight annular ambient linkage
consumed by component replacement.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceStageCompletion

open DirectedPath
open SliceSpliceSource

universe u

variable {V : Type u}

/-- Essential restriction preserves normalization.  This is stated locally
because the regular construction only needs it for a ladder stage. -/
private theorem isNormalized_essentialPart
    {Q : DWeb V} (hQ : Q.IsNormalized) : Q.essentialPart.IsNormalized := by
  intro x y hxy
  have hxyQ : Q.graph.Adj x y := Q.essentialPart_adj_imp hxy
  exact ⟨fun hySource ↦ (hQ hxyQ).1 hySource.1,
    fun hxTarget ↦ (hQ hxyQ).2 hxTarget⟩

/-- Every stage web of a normalized ambient web is normalized. -/
theorem stageWeb_isNormalized
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hGamma : Gamma.IsNormalized)
    (delta : Ladder.Stage kappa) : (L.stageWeb delta).IsNormalized := by
  exact isNormalized_essentialPart
    (SingularExtension.DWeb.IsNormalized.quotient hGamma
      (Gamma.terminalFrontier (L.warpAt delta)))

/-- Roofing only gets easier after quotienting: every quotient target path
lifts, with unchanged vertices and endpoints, to an original target path. -/
theorem roof_subset_quotient_roof
    (Q : DWeb V) (C T : Set V) :
    Q.roof T ⊆ (Q.quotient C).roof T := by
  intro x hx p hp
  let q : DirectedPath.FinitePath Q.graph :=
    p.lift (fun {_ _} e ↦ Q.quotient_adj_imp e)
  have hq : Q.IsTargetPathFrom x q := by
    refine ⟨?_, ?_⟩
    · simpa only [q, DirectedPath.FinitePath.lift] using hp.1
    · simpa only [q, DirectedPath.FinitePath.lift,
        DWeb.quotient_target] using hp.2
  obtain ⟨y, hyq, hyT⟩ := hx q hq
  refine ⟨y, ?_, hyT⟩
  simpa only [q, DirectedPath.FinitePath.support_lift] using hyq

/-- Roofing only gets easier after restricting a web to its target-reachable
essential part.  Every target path in the restriction lifts, with unchanged
support and endpoints, to a target path in the original web. -/
theorem roof_subset_essentialPart_roof
    (Q : DWeb V) (T : Set V) :
    Q.roof T ⊆ Q.essentialPart.roof T := by
  intro x hx p hp
  let q : DirectedPath.FinitePath Q.graph :=
    p.lift (fun {_ _} e ↦ Q.essentialPart_adj_imp e)
  have hq : Q.IsTargetPathFrom x q := by
    refine ⟨?_, ?_⟩
    · simpa only [q, DirectedPath.FinitePath.lift] using hp.1
    · simpa only [q, DirectedPath.FinitePath.lift,
        Q.essentialPart_target] using hp.2
  obtain ⟨y, hyq, hyT⟩ := hx q hq
  refine ⟨y, ?_, hyT⟩
  simpa only [q, DirectedPath.FinitePath.support_lift] using hyq

/-- Every ambient roof remains a roof in a ladder stage web.  This is the
transport seam from the ambient club-capture theorem (9.5) to the
stage-local quotient-wave comparison (9.9). -/
theorem roof_subset_stageWeb_roof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta : Ladder.Stage kappa)
    (T : Set V) :
    Gamma.roof T ⊆ (L.stageWeb delta).roof T := by
  exact (roof_subset_quotient_roof Gamma
    (Gamma.terminalFrontier (L.warpAt delta)) T).trans
      (roof_subset_essentialPart_roof
        (Gamma.quotient (Gamma.terminalFrontier (L.warpAt delta))) T)

/-- A later ladder frontier remains essential in the earlier essential
quotient stage.  The ambient essential witness survives the old quotient:
ordinary chronology roofs the old commitment by the later frontier, while
strict chronology keeps its initial vertex out of the deleted strict roof.
-/
theorem later_frontier_essential_in_stageWeb
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    (hroof : L.RoofsSourceAtStages)
    (hchron : L.HasFrontierChronology)
    (hstrict : L.HasStrictFrontierChronology) (hdeltaBeta : delta < beta) :
    (L.stageWeb delta).essential (L.frontier beta) = L.frontier beta := by
  apply Set.Subset.antisymm
  · exact (L.stageWeb delta).essential_subset _
  · intro x hx
    refine ⟨hx, ?_⟩
    have hxAmbient : x ∈ Gamma.essential (L.frontier beta) := by
      rw [L.frontiersAreEssential_of_roofsSourceAtStages hroof beta]
      exact hx
    obtain ⟨p, hpTarget, hpAvoid⟩ :=
      (Gamma.not_mem_roof_iff (L.frontier beta \ {x}) x).1 hxAmbient.2
    let raw := Gamma.terminalFrontier (L.warpAt delta)
    have hrawRoof : Gamma.roof raw ⊆
        Gamma.roof (L.frontier beta) := by
      rw [← Gamma.roof_essential raw,
        ← L.frontier_eq_essential_terminalFrontier hroof delta]
      exact Gamma.roof_cut (hchron hdeltaBeta)
    have hxNotStrict : x ∉ Gamma.strictRoof raw := by
      intro hxStrict
      have hxStrict' : x ∈ Gamma.strictRoof (L.frontier delta) := by
        rwa [L.frontier_eq_essential_terminalFrontier hroof delta,
          Gamma.strictRoof_essential]
      exact Set.disjoint_left.1 (hstrict hdeltaBeta) hxStrict' hx
    have hpAvoidRel : RelationalRoof.Avoids Gamma.graph.Adj p
        (L.frontier beta \ {p.start}) := by
      intro y hyp hy
      apply Set.disjoint_left.1 hpAvoid hyp
      simpa only [hpTarget.1] using hy
    have hstrictPath : ∀ {y}, y ∈ p.walk.support →
        y ∉ Gamma.strictRoof raw := by
      intro y hyp hyStrict
      rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        Gamma.graph.Adj p.walk).1 hyp with hyeq | hytail
      · exact hxNotStrict (hpTarget.1 ▸ hyeq ▸ hyStrict)
      · have hyne : y ≠ p.start := by
          intro h
          exact p.isPath.rel_head_tail hytail
            (p.walk.head_support.trans h.symm)
        exact (RelationalRoof.not_mem_roof_of_later_mem_targetPath
          Gamma.graph.Adj Gamma.target p hpTarget hpAvoidRel hyp hyne)
            (hrawRoof hyStrict.1)
    have hcommitPath : ∀ {y}, y ∈ p.walk.support.tail → y ∉ raw := by
      intro y hyp hyRaw
      have hyne : y ≠ p.start := by
        intro h
        exact p.isPath.rel_head_tail hyp (p.walk.head_support.trans h.symm)
      have hyNotRoof := RelationalRoof.not_mem_roof_of_later_mem_targetPath
        Gamma.graph.Adj Gamma.target p hpTarget hpAvoidRel
          (List.mem_of_mem_tail hyp) hyne
      apply hyNotRoof
      exact hrawRoof (Gamma.subset_roof raw hyRaw)
    let q := Gamma.restrictFinitePathToQuotient raw p hstrictPath hcommitPath
    have hqTarget : (Gamma.quotient raw).IsTargetPathFrom x q := by
      exact ⟨hpTarget.1, hpTarget.2⟩
    have hqReach : q.support ⊆ (Gamma.quotient raw).reachableToTarget :=
      (Gamma.quotient raw).finitePath_support_subset_reachableToTarget
        q hpTarget.2
    let hrestrict : ∀ {u v : V}, (Gamma.quotient raw).graph.Adj u v →
        u ∈ q.support → v ∈ q.support →
          (Gamma.quotient raw).essentialPart.graph.Adj u v :=
      fun e hu hv ↦ ⟨e, hqReach hu, hqReach hv⟩
    let r : FinitePath (Gamma.quotient raw).essentialPart.graph :=
      q.restrictGraphOnSupport hrestrict
    apply ((Gamma.quotient raw).essentialPart.not_mem_roof_iff
      (L.frontier beta \ {x}) x).2
    refine ⟨r, ⟨?_, ?_⟩, ?_⟩
    · simpa only [r, FinitePath.restrictGraphOnSupport] using hqTarget.1
    · change r.finish ∈ (Gamma.quotient raw).target
      simpa only [r, FinitePath.restrictGraphOnSupport] using hqTarget.2
    · apply Set.disjoint_left.2
      intro y hyr hyBeta
      apply Set.disjoint_left.1 hpAvoid
      · have hyrq : y ∈ q.support := by
          rw [← FinitePath.support_restrictGraphOnSupport q hrestrict]
          exact hyr
        simpa only [q, Gamma.support_restrictFinitePathToQuotient] using hyrq
      · exact hyBeta

/-- A later ladder frontier separates the earlier stage source.  Every
stage target path lifts through the essential part and the old quotient,
so ambient frontier chronology supplies its required later-frontier hit.
-/
theorem later_frontier_separates_stageWeb
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    (hchron : L.HasFrontierChronology) (hdeltaBeta : delta < beta) :
    IsSeparatorFrom (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta) := by
  intro x hx p hp
  let raw := Gamma.terminalFrontier (L.warpAt delta)
  let q : FinitePath (Gamma.quotient raw).graph :=
    p.lift (fun {_ _} e ↦ (Gamma.quotient raw).essentialPart_adj_imp e)
  let r : FinitePath Gamma.graph :=
    q.lift (fun {_ _} e ↦ Gamma.quotient_adj_imp e)
  have hr : Gamma.IsTargetPathFrom x r := by
    refine ⟨?_, ?_⟩
    · simpa only [r, q, FinitePath.lift] using hp.1
    · have hpfinish : p.finish ∈ (Gamma.quotient raw).target := by
        exact hp.2
      simpa only [r, q, FinitePath.lift, DWeb.quotient_target]
        using hpfinish
  obtain ⟨y, hyr, hyBeta⟩ := hchron hdeltaBeta hx r hr
  refine ⟨y, ?_, hyBeta⟩
  have hyrq : y ∈ q.support := by
    simpa only [r, FinitePath.support_lift] using hyr
  have hsupport : q.support = p.support := by
    exact FinitePath.support_lift
      (fun {_ _} e ↦ (Gamma.quotient raw).essentialPart_adj_imp e) p
  rw [hsupport] at hyrq
  exact hyrq

/-- View a full linkage in the retargeted auxiliary web as a linkage in the
underlying quotient. -/
theorem isLinkageBetween_quotient_of_auxiliary
    (Q : DWeb V) {C T : Set V}
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    {R : Set (SliceAuxiliaryCore.auxiliaryWeb Q C T).DPath}
    (hR : IsLinkageBetween (SliceAuxiliaryCore.auxiliaryWeb Q C T)
      (SliceAuxiliaryCore.auxiliaryWeb Q C T).source
      (SliceAuxiliaryCore.auxiliaryWeb Q C T).target R) :
    IsLinkageBetween (Q.quotient C) C T R := by
  refine ⟨hR.isWarp, hR.finiteCharacter, ?_, ?_, ?_⟩
  · have hi := hR.initialSet_eq
    change DirectedPath.Path.initial '' R = (Q.quotient C).source at hi
    rw [SingularContinuation.quotient_source_eq_stopover Q hsep htrim]
      at hi
    exact hi
  · have ht := hR.terminalFrontier_subset
    change {x | ∃ p ∈ R, DirectedPath.Path.terminal? p = some x} ⊆ T
      at ht ⊢
    exact ht
  · intro p hp
    have hpure := hR.endpointPure p hp
    unfold IsPathBetween at hpure ⊢
    simp only [SliceAuxiliaryCore.auxiliaryWeb_source,
      SliceAuxiliaryCore.auxiliaryWeb_target,
      SingularContinuation.quotient_source_eq_stopover Q hsep htrim]
      at hpure
    exact hpure

/-- The later essential boundary is disjoint from the strict roof of the
stop-over whenever the stop-over is roofed by that boundary. -/
theorem disjoint_strictRoof_of_stopover_roof
    (Q : DWeb V) {C T : Set V}
    (hCT : C ⊆ Q.roof T) (hTessential : Q.essential T = T) :
    Disjoint (Q.strictRoof C) T := by
  have hessential : Q.essential (C ∪ T) = T := by
    calc
      Q.essential (C ∪ T) = Q.essential (T ∪ C) := by
        rw [Set.union_comm]
      _ = Q.essential T :=
        RelationalRoof.essential_union_eq_of_subset_roof
          Q.graph.Adj Q.target hCT
      _ = T := hTessential
  have hdis := Q.disjoint_essential_union_strictRoof_left C T
  rw [hessential] at hdis
  exact hdis.symm

/-- Join a terminal-exact half-way linkage to a full auxiliary linkage.
The result is tight at the later boundary and still links the original
request to the web target. -/
theorem exists_tightStageLinkage_of_fullAuxiliary
    (Q : DWeb V) (hQ : Q.IsNormalized)
    {U C T : Set V} (hU : U ⊆ Q.source)
    {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hfrontier : Q.terminalFrontier W = C)
    (hlinks : LinksToTarget Q W U)
    (hCT : C ⊆ Q.roof T)
    (hTessential : Q.essential T = T)
    {R : Set (SliceAuxiliaryCore.auxiliaryWeb Q C T).DPath}
    (hR : IsLinkageBetween (SliceAuxiliaryCore.auxiliaryWeb Q C T)
      (SliceAuxiliaryCore.auxiliaryWeb Q C T).source
      (SliceAuxiliaryCore.auxiliaryWeb Q C T).target R) :
    ∃ E : Set Q.DPath,
      TightLinkageBetween Q Q.source T E ∧ LinksToTarget Q E U := by
  have hclean : MeetsOnlyAtTerminal Q W C :=
    SingularContinuation.terminalCleanAt_of_linkage_terminalFrontier_eq
      Q hW hfrontier
  have hWtight : TightLinkageBetween Q Q.source C W := ⟨hW, hclean⟩
  have hWroof : Q.vertexSet W ⊆ Q.roof C :=
    SingularContinuation.linkage_vertexSet_subset_roof Q hW hsep hclean
  have hdisjoint : Disjoint (Q.strictRoof C) T :=
    disjoint_strictRoof_of_stopover_roof Q hCT hTessential
  have hWT : MeetsOnlyAtTerminal Q W T :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      htrim hWroof hclean hdisjoint
  have hR' : IsLinkageBetween (Q.quotient C) C T R :=
    isLinkageBetween_quotient_of_auxiliary Q hsep htrim hR
  obtain ⟨hcompat, hE⟩ :=
    SliceAuxiliaryCore.tightLinkageBetween_star_fullAuxiliary
      Q hQ hWtight hsep htrim hWT hR'
  refine ⟨Q.star hcompat, hE, ?_⟩
  exact SingularExtension.linksToTarget_of_forwardExtension hQ hU hlinks
    (Q.forwardExtension_star hcompat) hE.1.finiteCharacter

/-- Apply the lower extension clause to a small exceptional part of the
auxiliary source, and then perform the target-link-preserving join. -/
theorem exists_tightStageLinkage_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) (hQ : Q.IsNormalized)
    {U C T E : Set V} (hU : U ⊆ Q.source)
    {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hquotient : (Q.quotient C).IsUnhindered)
    (hfrontier : Q.terminalFrontier W = C)
    (hlinks : LinksToTarget Q W U)
    (hCT : C ⊆ Q.roof T)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ C) (hE : #E < kappa)
    {F : Set (SliceAuxiliaryCore.auxiliaryWeb Q C T).DPath}
    (hF : IsLinkageBetween (SliceAuxiliaryCore.auxiliaryWeb Q C T)
      ((SliceAuxiliaryCore.auxiliaryWeb Q C T).source \ E)
      (SliceAuxiliaryCore.auxiliaryWeb Q C T).target F) :
    ∃ P : Set Q.DPath,
      TightLinkageBetween Q Q.source T P ∧ LinksToTarget Q P U := by
  have hquotientRoof : C ⊆ (Q.quotient C).roof T :=
    hCT.trans (roof_subset_quotient_roof Q C T)
  obtain ⟨R, hR⟩ := SliceAuxiliaryCore.exists_fullAuxiliaryLinkage_of_lower
    hlower Q hsep htrim hquotient hquotientRoof hEsub hE hF
  exact exists_tightStageLinkage_of_fullAuxiliary Q hQ hU hW hsep htrim
    hfrontier hlinks hCT hTessential hR

/-- Complete after the source-faithful component replacement of Assertion
9.10.  The replacement has terminal frontier `C'`, but the second linkage
still lives in the quotient by the original trimmed half-way stopover `C`.
Thus the lower extension clause is applied to the source subweb on `C'`;
no (generally false) assertion that `C'` is itself a separator is needed. -/
theorem exists_tightStageLinkage_of_replaced_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) (hQ : Q.IsNormalized)
    {U C C' T E : Set V} (hU : U ⊆ Q.source)
    {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C' W)
    (hsep : IsSeparatorFrom Q Q.source C)
    (htrim : IsTrimmedSeparator Q C)
    (hquotient : (Q.quotient C).IsUnhindered)
    (hfrontier : Q.terminalFrontier W = C')
    (hC'sub : C' ⊆ C)
    (hcleanC : MeetsOnlyAtTerminal Q W C)
    (hlinks : LinksToTarget Q W U)
    (hCT : C ⊆ Q.roof T)
    (hTessential : Q.essential T = T)
    (hEsub : E ⊆ C') (hE : #E < kappa)
    {F : Set ((SliceAuxiliaryCore.auxiliaryWeb Q C T).sourceSubweb C').DPath}
    (hF : IsLinkageBetween
      ((SliceAuxiliaryCore.auxiliaryWeb Q C T).sourceSubweb C')
      (((SliceAuxiliaryCore.auxiliaryWeb Q C T).sourceSubweb C').source \ E)
      ((SliceAuxiliaryCore.auxiliaryWeb Q C T).sourceSubweb C').target F) :
    ∃ P : Set Q.DPath,
      TightLinkageBetween Q Q.source T P ∧ LinksToTarget Q P U := by
  let Delta :=
    (SliceAuxiliaryCore.auxiliaryWeb Q C T).sourceSubweb C'
  have hquotientRoof : C ⊆ (Q.quotient C).roof T :=
    hCT.trans (roof_subset_quotient_roof Q C T)
  have haux : (SliceAuxiliaryCore.auxiliaryWeb Q C T).IsUnhindered :=
    SliceAuxiliaryCore.auxiliaryWeb_isUnhindered_of_stopover
      Q hsep htrim hquotient hquotientRoof
  have hauxNoEnter :
      (SliceAuxiliaryCore.auxiliaryWeb Q C T).NoEdgeEnters
        (SliceAuxiliaryCore.auxiliaryWeb Q C T).source := by
    intro x y hxy hy
    exact ((SingularExtension.DWeb.IsNormalized.quotient hQ C) hxy).1 hy
  have hC'source :
      C' ⊆ (SliceAuxiliaryCore.auxiliaryWeb Q C T).source := by
    rw [SliceAuxiliaryCore.auxiliaryWeb_source_eq_stopover
      Q hsep htrim]
    exact hC'sub
  have hDelta : Delta.IsUnhindered :=
    haux.sourceSubweb (SliceAuxiliaryCore.auxiliaryWeb Q C T)
      hauxNoEnter hC'source
  obtain ⟨R, hR⟩ := SliceAuxiliaryCore.exists_auxiliaryLinkage_of_lower
    hlower Delta hDelta E hEsub hE hF
  have hRquot : IsLinkageBetween (Q.quotient C) C' T R := by
    change IsLinkageBetween Delta C' T R at hR
    exact hR
  let Rtight := SliceAuxiliaryCore.rightTightenedFamily hRquot
  have hRtight : TightLinkageBetween (Q.quotient C) C' T Rtight :=
    SliceAuxiliaryCore.tightLinkageBetween_rightTightenedFamily hRquot
  let Rlift := Q.liftQuotientFamily C Rtight
  have hRlift : TightLinkageBetween Q C' T Rlift :=
    SliceAuxiliaryCore.tightLinkageBetween_liftQuotientFamily Q C hRtight
  have hcleanC' : MeetsOnlyAtTerminal Q W C' :=
    SingularContinuation.terminalCleanAt_of_linkage_terminalFrontier_eq
      Q hW hfrontier
  have hWtightC' : TightLinkageBetween Q Q.source C' W :=
    ⟨hW, hcleanC'⟩
  have hWtightC : TightLinkageBetween Q Q.source C W :=
    SliceSpliceSource.tightLinkageBetween_of_structural hQ Set.Subset.rfl
      hW.isWarp hW.finiteCharacter hW.initialSet_eq
      (hW.terminalFrontier_subset.trans hC'sub) hcleanC
  have hWroof : Q.vertexSet W ⊆ Q.roof C :=
    SingularContinuation.linkage_vertexSet_subset_roof
      Q hWtightC.1 hsep hcleanC
  have hdisjoint : Disjoint (Q.strictRoof C) T :=
    disjoint_strictRoof_of_stopover_roof Q hCT hTessential
  have hWT : MeetsOnlyAtTerminal Q W T :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      htrim hWroof hcleanC hdisjoint
  have hRstart : (Q.quotient C).initialSet Rtight ⊆ C := by
    rw [hRtight.1.initialSet_eq]
    exact hC'sub
  let hcompat : Q.StarCompatible W Rlift :=
    SingularContinuation.starCompatible_liftQuotientFamily_of_roof
      Q hWroof htrim hcleanC hRstart
  have hP : TightLinkageBetween Q Q.source T (Q.star hcompat) :=
    SliceSpliceSource.tightLinkageBetween_star hQ Set.Subset.rfl
      hWtightC' hRlift hWT hcompat
  refine ⟨Q.star hcompat, hP, ?_⟩
  exact SingularExtension.linksToTarget_of_forwardExtension hQ hU hlinks
    (Q.forwardExtension_star hcompat) hP.1.finiteCharacter

/-- Payload-specialized stage completion.  This is the direct interface
between the pre-chosen half-way table and the ordinary auxiliary linkage. -/
theorem exists_tightStageLinkage_of_halfwayPayload_lower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} {delta : Ladder.Stage kappa}
    {U E T : Set V} (D : SliceCandidate.HalfwayPayload L delta U)
    (hQ : (L.stageWeb delta).IsNormalized)
    (hU : U ⊆ L.frontier delta)
    (hCT : D.C ⊆ (L.stageWeb delta).roof T)
    (hTessential : (L.stageWeb delta).essential T = T)
    (hEsub : E ⊆ D.C) (hE : #E < kappa)
    {F : Set (SliceAuxiliaryCore.auxiliaryWeb
      (L.stageWeb delta) D.C T).DPath}
    (hF : IsLinkageBetween
      (SliceAuxiliaryCore.auxiliaryWeb (L.stageWeb delta) D.C T)
      ((SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C T).source \ E)
      (SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C T).target F) :
    ∃ P : Set (L.stageWeb delta).DPath,
      TightLinkageBetween (L.stageWeb delta)
        (L.frontier delta) T P ∧
      LinksToTarget (L.stageWeb delta) P U := by
  exact RegularSliceStageCompletion.exists_tightStageLinkage_of_lower
    hlower (L.stageWeb delta) hQ hU
    D.linkage D.separator D.trimmed D.quotientUnhindered
    D.terminalFrontier_eq D.links hCT hTessential hEsub hE hF

/-- Complete a half-way payload at a later ladder frontier and lift it to
the ambient annulus.  This produces exactly the retained-linkage input of
the component-replacement compiler. -/
theorem exists_tightAnnularAmbientLinkage_of_halfwayPayload_lower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {U E : Set V} (D : SliceCandidate.HalfwayPayload L delta U)
    (hGamma : Gamma.IsNormalized)
    (hroof : L.RoofsSourceAtStages)
    (hchron : L.HasFrontierChronology) (hdeltaBeta : delta < beta)
    (hU : U ⊆ L.frontier delta)
    (hCT : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hbetaEssential : (L.stageWeb delta).essential
      (L.frontier beta) = L.frontier beta)
    (hbetaSeparator : IsSeparatorFrom (L.stageWeb delta)
      (L.frontier delta) (L.frontier beta))
    (hEsub : E ⊆ D.C) (hE : #E < kappa)
    {F : Set (SliceAuxiliaryCore.auxiliaryWeb
      (L.stageWeb delta) D.C (L.frontier beta)).DPath}
    (hF : IsLinkageBetween
      (SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta))
      ((SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).source \ E)
      (SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).target F) :
    ∃ P : Set Gamma.DPath,
      TightLinkageBetween Gamma (L.frontier delta) (L.frontier beta) P ∧
      LinksToTarget Gamma P U ∧
      Gamma.vertexSet P ⊆ L.lowerRegion delta ∩ L.upperRegion beta := by
  obtain ⟨T, hT, hlinks⟩ :=
    exists_tightStageLinkage_of_halfwayPayload_lower hlower D
      (stageWeb_isNormalized hGamma delta) hU hCT hbetaEssential
        hEsub hE hF
  refine ⟨SliceSegmentCore.liftStageFamily L delta T, ?_⟩
  exact RegularSliceStageLift.tightAnnularLinkage_liftStageFamily
    hroof hchron hdeltaBeta hT hlinks hbetaSeparator

/-- Stage completion with the two later-frontier facts synthesized from
the ladder chronology laws.  The remaining hypotheses are precisely the
later roofing of the half-way stop-over and the ordinary auxiliary linkage
off its small exceptional set. -/
theorem exists_tightAnnularAmbientLinkage_of_halfwayPayload_lower_of_chronology
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {U E : Set V} (D : SliceCandidate.HalfwayPayload L delta U)
    (hGamma : Gamma.IsNormalized)
    (hroof : L.RoofsSourceAtStages)
    (hchron : L.HasFrontierChronology)
    (hstrict : L.HasStrictFrontierChronology) (hdeltaBeta : delta < beta)
    (hU : U ⊆ L.frontier delta)
    (hCT : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hEsub : E ⊆ D.C) (hE : #E < kappa)
    {F : Set (SliceAuxiliaryCore.auxiliaryWeb
      (L.stageWeb delta) D.C (L.frontier beta)).DPath}
    (hF : IsLinkageBetween
      (SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta))
      ((SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).source \ E)
      (SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).target F) :
    ∃ P : Set Gamma.DPath,
      TightLinkageBetween Gamma (L.frontier delta) (L.frontier beta) P ∧
      LinksToTarget Gamma P U ∧
      Gamma.vertexSet P ⊆ L.lowerRegion delta ∩ L.upperRegion beta := by
  exact exists_tightAnnularAmbientLinkage_of_halfwayPayload_lower
    hlower D hGamma hroof hchron hdeltaBeta hU hCT
      (later_frontier_essential_in_stageWeb
        hroof hchron hstrict hdeltaBeta)
      (later_frontier_separates_stageWeb hchron hdeltaBeta)
      hEsub hE hF

/-- Source-faithful 9.10 completion after component replacement.  The
original half-way payload supplies the trimmed separator `D.C` and its
unhindered quotient, while `W'` exposes the smaller actual terminal set
`C'`.  The lower step is performed in the corresponding auxiliary source
subweb and the result is lifted to the ambient ladder annulus. -/
theorem exists_tightAnnularAmbientLinkage_of_replaced_halfway_lower_of_chronology
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {U : Set V} (D : SliceCandidate.HalfwayPayload L delta U)
    (hGamma : Gamma.IsNormalized)
    (hroof : L.RoofsSourceAtStages)
    (hchron : L.HasFrontierChronology)
    (hstrict : L.HasStrictFrontierChronology) (hdeltaBeta : delta < beta)
    (hU : U ⊆ L.frontier delta)
    {C' E : Set V} {W' : Set (L.stageWeb delta).DPath}
    (hW' : IsLinkageBetween (L.stageWeb delta)
      (L.frontier delta) C' W')
    (hfrontier : (L.stageWeb delta).terminalFrontier W' = C')
    (hC'sub : C' ⊆ D.C)
    (hcleanC : MeetsOnlyAtTerminal (L.stageWeb delta) W' D.C)
    (hlinks : LinksToTarget (L.stageWeb delta) W' U)
    (hCT : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hEsub : E ⊆ C') (hE : #E < kappa)
    {F : Set ((SliceAuxiliaryCore.auxiliaryWeb
      (L.stageWeb delta) D.C (L.frontier beta)).sourceSubweb C').DPath}
    (hF : IsLinkageBetween
      ((SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).sourceSubweb C')
      (((SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).sourceSubweb C').source \ E)
      ((SliceAuxiliaryCore.auxiliaryWeb
        (L.stageWeb delta) D.C (L.frontier beta)).sourceSubweb C').target F) :
    ∃ P : Set Gamma.DPath,
      TightLinkageBetween Gamma (L.frontier delta) (L.frontier beta) P ∧
      LinksToTarget Gamma P U ∧
      Gamma.vertexSet P ⊆ L.lowerRegion delta ∩ L.upperRegion beta := by
  obtain ⟨T, hT, hTlinks⟩ :=
    exists_tightStageLinkage_of_replaced_lower hlower
      (L.stageWeb delta) (stageWeb_isNormalized hGamma delta) hU hW'
      D.separator D.trimmed D.quotientUnhindered hfrontier hC'sub
      hcleanC hlinks hCT
      (later_frontier_essential_in_stageWeb
        hroof hchron hstrict hdeltaBeta)
      hEsub hE hF
  refine ⟨SliceSegmentCore.liftStageFamily L delta T, ?_⟩
  exact RegularSliceStageLift.tightAnnularLinkage_liftStageFamily
    hroof hchron hdeltaBeta hT hTlinks
      (later_frontier_separates_stageWeb hchron hdeltaBeta)

end RegularSliceStageCompletion
end CardinalInduction
end Erdos599

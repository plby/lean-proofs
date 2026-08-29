/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSelectedObstruction
import ErdosProblems.Erdos599.RegularFixedStageTargetLinkingAnnular
import ErdosProblems.Erdos599.RegularCandidateProvider
import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice

/-!
# Weak half-way payload preparation for a selected regular slice

This file performs the part of the weak selected-coordinate construction
which is independent of the false exact-frontier strengthening.  Requested
non-target sources which already lie on the half-way stop-over, together
with the requests persistent on the later frontier, are put on the selected
target track.  The complementary first-hit track is terminal-clean and is
advanced to the later frontier by the ordinary interval and normalized
Delta construction.

The output intentionally does not claim that the selected target track is
disjoint from the newly completed clean track.  That is the genuinely
history-sensitive protected-selection obligation; it cannot be recovered
from the two independently constructed families.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakPayloadPreparation

open SliceCandidate SliceSpliceSource

universe u

variable {V : Type u}

/-- Partial-source form of the fixed-stage target-linking construction.
The old clean row may start on any `A ⊆ frontier delta`; the ordinary
interval family fills the complement after removing the requested sources
and the small inessential-extension set. -/
theorem exists_partialTargetLinkingAnnularCore
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) {A U C : Set V}
    {W : Set (L.stageWeb delta).DPath}
    (hA : A ⊆ L.frontier delta)
    (hU : U ⊆ A) (hUsmall : #U < kappa)
    (hW : IsLinkageBetween (L.stageWeb delta) A C W)
    (hWclean : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) W C)
    (hseparator : IsSeparatorFrom (L.stageWeb delta)
      (L.frontier delta) C)
    (htrimmed : IsTrimmedSeparator (L.stageWeb delta) C)
    (hquotient : ((L.stageWeb delta).quotient C).IsUnhindered)
    (hlinks : LinksToTarget (L.stageWeb delta) W U)
    (hCroof : C ⊆ (L.stageWeb delta).roof (L.frontier beta)) :
    ∃ result : Set (L.stageWeb delta).DPath,
      TightLinkageBetween (L.stageWeb delta) A (L.frontier beta) result ∧
        LinksToTarget (L.stageWeb delta) result U := by
  let Q := L.stageWeb delta
  let E₀ := SliceCandidate.inessentialExtensionSources hL.sliceGeometry hdeltaBeta.le
  let E := U ∪ (A ∩ E₀)
  let Y₀ := SliceCandidate.ordinaryStageFamily hL.sliceGeometry hdeltaBeta.le
  let Y := initialRestriction Q Y₀ (A \ E)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hNormQ : Q.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized hNorm L delta
  have hY₀ : IsLinkageBetween Q (L.frontier delta \ E₀)
      (L.frontier beta) Y₀ :=
    SliceCandidate.ordinaryStageFamily_isLinkageBetween hL hdeltaBeta.le
  have hYsource : A \ E ⊆ L.frontier delta \ E₀ := by
    rintro x ⟨hxA, hxE⟩
    refine ⟨hA hxA, ?_⟩
    intro hxE₀
    exact hxE (Or.inr ⟨hxA, hxE₀⟩)
  have hY : IsLinkageBetween Q (A \ E) (L.frontier beta) Y :=
    isLinkageBetween_initialRestriction hY₀ hYsource
  have hYtight : MeetsOnlyAtTerminal Q Y (L.frontier beta) := by
    intro p hp
    exact SliceCandidate.ordinaryStageFamily_meetsOnlyAtTerminal
      hL hdeltaBeta.le p hp.1
  have hTessential : Q.essential (L.frontier beta) = L.frontier beta :=
    RegularCandidateProvider.stageWeb_laterFrontier_isEssential
      hL hNoEnter hdeltaBeta
  have hsepFull : RelationalRoof.Separates Q.graph.Adj
      (L.frontier delta) (L.frontier beta) C :=
    SliceSegmentCore.separates_between_of_roofed Q
      hTessential hseparator hCroof
  have hsep : RelationalRoof.Separates Q.graph.Adj
      (A \ E) (L.frontier beta) C := by
    intro a t p ha ht
    exact hsepFull p (hA ha.1) ht
  have hEsub : E ⊆ A := by
    intro x hx
    exact hx.elim (fun hxU ↦ hU hxU) (fun hxA ↦ hxA.1)
  have hEsmall : #E < kappa := by
    apply (Cardinal.mk_union_le U (A ∩ E₀)).trans_lt
    exact Cardinal.add_lt_of_lt hregular.aleph0_le hUsmall
      ((Cardinal.mk_subtype_mono Set.inter_subset_right).trans_lt
        (SliceCandidate.mk_inessentialExtensionSources_lt_of_not_mem_phi
          hL hdeltaBeta.le hbeta))
  obtain ⟨W', E', F, hW', hlinks', hW'clean, hE'sub, hE'small,
      hF, hWF, hFtight⟩ :=
    RegularFixedStageTargetLinkingAnnular.exists_cleanWholeTerminalExchange_with_links
      Q hW hWclean hY hYtight hsep hEsub hregular huncountable
        hEsmall Set.subset_union_left hlinks
  have hCsource : (Q.quotient C).source = C :=
    SingularContinuation.quotient_source_eq_stopover Q
      hseparator htrimmed
  obtain ⟨R, hcompat, _hR, hresult, _hsmall⟩ :=
    RegularCandidateProvider.exists_tightNormalizedCleanContinuation
      hlower hregular huncountable Q hNormQ hA hW' hseparator hW'clean
        rfl hW'.terminalFrontier_subset htrimmed hCsource hCroof
          hquotient hTessential hE'sub hE'small hF hFtight hWF
  let result := Q.star hcompat
  have hforward : Q.ForwardExtension W' result :=
    Q.forwardExtension_star hcompat
  have hUsource : U ⊆ Q.source := by
    change U ⊆ L.frontier delta
    exact hU.trans hA
  have hlinksResult : LinksToTarget Q result U :=
    SingularExtension.linksToTarget_of_forwardExtension hNormQ
      hUsource hlinks' hforward hresult.1.finiteCharacter
  exact ⟨result, hresult, hlinksResult⟩

/-- Concrete selected/clean preparation obtained from an ordinary half-way
payload.  It records a genuine small selected target slice at the stop-over
and a tight target-linking annular continuation for all remaining requests.
No use is made of `HalfwayPayload.terminalFrontier_eq`. -/
theorem HalfwayPayload.exists_selectedCleanAnnularPreparation
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) {U : Set V}
    (D : HalfwayPayload L delta U)
    (hUfrontier : U ⊆ L.frontier delta) (hUsmall : #U < kappa)
    (hCroof : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta)) :
    let selected := RegularWeakSelectedObstruction.selectedObstruction
      (L.stageWeb delta) (L.frontier beta) D.C U
    ∃ S : RegularCompletedPendingSplice.CleanTargetSlice
        (L.stageWeb delta) (L.frontier delta) D.C selected,
      RegularWeakSplitCandidate.stagePersistent Gamma
          (L.frontier beta) U ⊆ selected ∧
        selected ⊆ U ∧
        #S.target < kappa ∧
        S.target ⊆ SingularExtension.completedPart
          (L.stageWeb delta) D.W ∧
        ∃ cleanResult : Set (L.stageWeb delta).DPath,
          TightLinkageBetween (L.stageWeb delta)
              (L.frontier delta \ selected) (L.frontier beta)
              cleanResult ∧
            LinksToTarget (L.stageWeb delta) cleanResult
              (U \ selected) := by
  dsimp only
  let Q := L.stageWeb delta
  let selected := RegularWeakSelectedObstruction.selectedObstruction
    Q (L.frontier beta) D.C U
  have hUsource : U ⊆ Q.source := by
    change U ⊆ L.frontier delta
    exact hUfrontier
  obtain ⟨S, hScleanLinks, hStargetSmall, hStargetPayload⟩ :=
    RegularWeakSelectedObstruction.exists_cleanTargetSlice_selectedObstruction
      (RegularCandidateProvider.stageWeb_isNormalized hNorm L delta)
        D.linkage hUsource D.links hUsmall (L.frontier beta)
  have hselectedPersistent : RegularWeakSplitCandidate.stagePersistent
      Gamma (L.frontier beta) U ⊆ selected := by
    intro x hx
    exact RegularWeakSelectedObstruction.stagePersistent_subset_selectedObstruction
      Q (L.frontier beta) D.C U hx
  have hselectedRequest : selected ⊆ U :=
    RegularWeakSelectedObstruction.selectedObstruction_subset_request
      Q (L.frontier beta) D.C U
  have hcleanLinkage : IsLinkageBetween Q
      (Q.source \ selected) D.C S.clean :=
    RegularLiftCleanTargetSlice.clean_isLinkageBetween S
  have hremaining : U \ selected ⊆ Q.source \ selected := by
    intro x hx
    exact ⟨hUsource hx.1, hx.2⟩
  obtain ⟨cleanResult, hcleanResult, hcleanLinks⟩ :=
    exists_partialTargetLinkingAnnularCore hlower hregular huncountable
      hL hNorm hdeltaBeta hbeta
        (A := Q.source \ selected) (U := U \ selected)
        (C := D.C) (W := S.clean)
        (by
          change Q.source \ selected ⊆ Q.source
          exact Set.sdiff_subset)
        hremaining
        ((Cardinal.mk_subtype_mono Set.sdiff_subset).trans_lt hUsmall)
        hcleanLinkage S.clean_terminal_only D.separator D.trimmed
          D.quotientUnhindered hScleanLinks hCroof
  refine ⟨S, hselectedPersistent, hselectedRequest,
    hStargetSmall, hStargetPayload, cleanResult, ?_, hcleanLinks⟩
  change TightLinkageBetween Q (Q.source \ selected)
    (L.frontier beta) cleanResult
  exact hcleanResult

end RegularWeakPayloadPreparation
end CardinalInduction
end Erdos599

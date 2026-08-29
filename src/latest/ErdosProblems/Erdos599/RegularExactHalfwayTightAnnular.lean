/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularFixedStageTargetLinkingAnnular

/-!
# Tight annular completion of an exact half-way payload

The terminal-clean fixed-stage construction already produces a tight
linkage internally.  Its original public wrapper intentionally forgets
that certificate.  This file exposes the tight form needed by the ambient
stage lift, using the exact terminal-frontier field now carried by every
half-way payload.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExactHalfwayTightAnnular

open SliceCandidate SliceSpliceSource

universe u

variable {V : Type u}

/-- Exact half-way data, ordinary first-hit component replacement, and the
normalized-Delta lower fill produce a tight later-frontier linkage while
preserving every requested target link. -/
theorem HalfwayPayload.exists_tightTargetLinkingAnnular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) {U : Set V}
    (D : HalfwayPayload L delta U)
    (hUfrontier : U ⊆ L.frontier delta) (hUsmall : #U < kappa)
    (hCroof : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta)) :
    ∃ W : Set (L.stageWeb delta).DPath,
      TightLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U := by
  let Q := L.stageWeb delta
  have hcleanFrontier : SingularContinuation.TerminalCleanAt
      Q D.W (Q.terminalFrontier D.W) :=
    SingularExtension.terminalCleanAt_terminalFrontier_of_isWarp
      D.linkage.isWarp
  have hclean : SingularContinuation.TerminalCleanAt Q D.W D.C := by
    simpa only [D.terminalFrontier_eq] using hcleanFrontier
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
      exact hxE₀.choose
  have hEsmall : #E < kappa := by
    apply (Cardinal.mk_union_le U E₀).trans_lt
    exact Cardinal.add_lt_of_lt hregular.aleph0_le hUsmall
      (SliceCandidate.mk_inessentialExtensionSources_lt_of_not_mem_phi
        hL hdeltaBeta.le hbeta)
  obtain ⟨W', E', F, hW', hlinks', hW'clean, hE'sub, hE'small,
      hF, hWF, hFtight⟩ :=
    RegularFixedStageTargetLinkingAnnular.exists_cleanWholeTerminalExchange_with_links
      Q D.linkage hclean hY hYtight hsep hEsub hregular huncountable
        hEsmall Set.subset_union_left D.links
  have hCsource : (Q.quotient D.C).source = D.C :=
    SingularContinuation.quotient_source_eq_stopover Q
      D.separator D.trimmed
  obtain ⟨R, hcompat, _hR, hresult, _hsmall⟩ :=
    RegularCandidateProvider.exists_tightNormalizedCleanContinuation
      hlower hregular huncountable Q hNormQ
        (by simpa only [Q, hQsource] using
          (Set.Subset.rfl : L.frontier delta ⊆ L.frontier delta))
        hW' D.separator hW'clean rfl hW'.terminalFrontier_subset
          D.trimmed hCsource hCroof D.quotientUnhindered hTessential
            hE'sub hE'small hF hFtight hWF
  let result := Q.star hcompat
  have hforward : Q.ForwardExtension W' result :=
    Q.forwardExtension_star hcompat
  have hlinksResult : LinksToTarget Q result U :=
    SingularExtension.linksToTarget_of_forwardExtension hNormQ
      (Set.subset_union_left.trans hEsub) hlinks' hforward
        hresult.1.finiteCharacter
  refine ⟨result, ?_, hlinksResult⟩
  simpa only [Q, hQsource] using hresult

end RegularExactHalfwayTightAnnular
end CardinalInduction
end Erdos599

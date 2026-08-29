/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCandidateProvider
import ErdosProblems.Erdos599.RegularBetaSelection

/-!
# Fixed-stage target-linking annular rows

This file isolates the target-link preservation calculation in Assertion
9.15.  Whole alternating components rooted at the requested set are kept
during the ordinary-stage exchange.  The resulting stopped row therefore
still links the request to the ambient target.  When the stopped row is
terminal-clean, the normalized-Delta fill is a forward extension, so those
target links survive in the final annular row.

The terminal-clean hypothesis in the final theorem is intentional.  A
general half-way row can start at its stop-over, and such a component need
not be terminal-clean.  The persistent-track construction handles precisely
those components separately.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularFixedStageTargetLinkingAnnular

open SliceCandidate SliceSpliceSource

universe u

variable {V : Type u}

/-- Clean whole-component exchange with the target-link certificate retained.
This is the common strengthening of the two existing exchange packages:
`RegularCleanExchange` supplies cleanliness and `SliceCandidate` supplies
target-link preservation. -/
theorem exists_cleanWholeTerminalExchange_with_links
    {kappa : Cardinal.{u}} (Q : DWeb V) {A C T E U : Set V}
    {W : Set Q.DPath} (hW : IsLinkageBetween Q A C W)
    (hWclean : SingularContinuation.TerminalCleanAt Q W C)
    {Y : Set Q.DPath} (hY : IsLinkageBetween Q (A \ E) T Y)
    (hYtight : MeetsOnlyAtTerminal Q Y T)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (hEsub : E ⊆ A) (hregular : kappa.IsRegular)
    (huncountable : aleph0 < kappa) (hEsmall : #E < kappa)
    (hUE : U ⊆ E) (hlinks : LinksToTarget Q W U) :
    ∃ (W' : Set Q.DPath) (E' : Set V) (F : Set Q.DPath),
      IsLinkageBetween Q A C W' ∧ LinksToTarget Q W' U ∧
      SingularContinuation.TerminalCleanAt Q W' C ∧
      E' ⊆ Q.terminalFrontier W' ∧ #E' < kappa ∧
      IsLinkageBetween Q (Q.terminalFrontier W' \ E') T F ∧
      Q.StarCompatible W' F ∧ MeetsOnlyAtTerminal Q F T := by
  let P := firstHitPrefixFamily hY hsep
  let W' := wholeComponentMixedFamily Q W P Y E
  let E' := wholeExchangeExceptionalTerminals Q W Y E
  let S := wholeNonexceptionalPrefixSources hY hsep W
  let F := selectedSuffixFamily hY hsep S
  have hW' : IsLinkageBetween Q A C W' :=
    wholeComponentMixedFamily_isLinkageBetween Q hW hY hsep hEsub
  have hlinks' : LinksToTarget Q W' U :=
    wholeComponentMixedFamily_linksToTarget Q hW.finiteCharacter hUE hlinks
  have hW'clean : SingularContinuation.TerminalCleanAt Q W' C :=
    RegularCleanExchange.wholeComponentMixedFamily_terminalClean
      hWclean hY hsep
  have hE'sub : E' ⊆ Q.terminalFrontier W' := by
    intro x hx
    change x ∈ Q.terminalFrontier
      (initialPart Q W (exceptionalComponentVertices Q W Y E)) at hx
    change x ∈ Q.terminalFrontier
      (initialPart Q W (exceptionalComponentVertices Q W Y E) ∪
        initialPart Q P (exceptionalComponentVertices Q W Y E)ᶜ)
    rw [DWeb.terminalFrontier_union]
    exact Or.inl hx
  have hE'small : #E' < kappa :=
    wholeExchangeExceptionalTerminals_small Q hregular huncountable
      hW.isWarp hY.isWarp hW.finiteCharacter hY.finiteCharacter hEsmall
  have hsource : Q.terminalFrontier W' \ E' =
      selectedSuffixStartSet hY hsep S := by
    rw [terminalFrontier_wholeMixed_sdiff_exceptional_eq Q hW hY hsep]
    exact terminalFrontier_wholeNonexceptionalPrefix_eq_suffixStartSet hY hsep
  have hF : IsLinkageBetween Q
      (selectedSuffixStartSet hY hsep S) T F :=
    selectedSuffixFamily_isLinkageBetween hY hsep S
  have hFtight : MeetsOnlyAtTerminal Q F T :=
    selectedSuffixFamily_meetsOnlyAtTerminal hY hYtight hsep S
  exact ⟨W', E', F, hW', hlinks', hW'clean, hE'sub, hE'small,
    hsource.symm ▸ hF,
    wholeComponentExchange_starCompatible Q hW hY hsep, hFtight⟩

/-- A terminal-clean half-way payload gives the fixed-stage target-linking
annular row used in Assertion 9.15.  The exceptional set is the union of
the request and the inessential ordinary-stage sources, hence is still
strictly smaller than `kappa`. -/
theorem exists_targetLinkingAnnularCore_of_terminalClean
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) {U C : Set V}
    {W : Set (L.stageWeb delta).DPath}
    (hW : IsLinkageBetween (L.stageWeb delta)
      (L.stageWeb delta).source C W)
    (hseparator : IsSeparatorFrom (L.stageWeb delta)
      (L.stageWeb delta).source C)
    (htrimmed : IsTrimmedSeparator (L.stageWeb delta) C)
    (hquotient : ((L.stageWeb delta).quotient C).IsUnhindered)
    (hlinks : LinksToTarget (L.stageWeb delta) W U)
    (hUfrontier : U ⊆ L.frontier delta) (hUsmall : #U < kappa)
    (hCroof : C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hclean : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) W C) :
    ∃ W : Set (L.stageWeb delta).DPath,
      IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U := by
  let Q := L.stageWeb delta
  let E₀ := SliceCandidate.inessentialExtensionSources hL.sliceGeometry hdeltaBeta.le
  let E := U ∪ E₀
  let Y₀ := SliceCandidate.ordinaryStageFamily hL.sliceGeometry hdeltaBeta.le
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
      Q.source (L.frontier beta) C :=
    SliceSegmentCore.separates_between_of_roofed Q
      hTessential hseparator hCroof
  have hsep : RelationalRoof.Separates Q.graph.Adj
      (Q.source \ E) (L.frontier beta) C := by
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
  obtain ⟨W', E', F, hW', hlinks', hW'clean, hE'sub, hE'small,
      hF, hWF, hFtight⟩ :=
    exists_cleanWholeTerminalExchange_with_links Q hW hclean hY
      hYtight hsep hEsub hregular huncountable hEsmall
        Set.subset_union_left hlinks
  have hCsource : (Q.quotient C).source = C :=
    SingularContinuation.quotient_source_eq_stopover Q
      hseparator htrimmed
  obtain ⟨R, hcompat, _hR, hresult, _hsmall⟩ :=
    RegularCandidateProvider.exists_tightNormalizedCleanContinuation
      hlower hregular huncountable Q hNormQ
        (by simpa only [Q, hQsource] using
          (Set.Subset.rfl : L.frontier delta ⊆ L.frontier delta))
        hW' hseparator hW'clean rfl hW'.terminalFrontier_subset
          htrimmed hCsource hCroof hquotient hTessential
            hE'sub hE'small hF hFtight hWF
  let result := Q.star hcompat
  have hforward : Q.ForwardExtension W' result :=
    Q.forwardExtension_star hcompat
  have hlinksResult : LinksToTarget Q result U :=
    SingularExtension.linksToTarget_of_forwardExtension hNormQ
      (Set.subset_union_left.trans hEsub) hlinks' hforward
        hresult.1.finiteCharacter
  exact ⟨result, by simpa only [Q, hQsource] using hresult.1,
    hlinksResult⟩

/-- A terminal-clean half-way payload supplies the data of the core
fixed-stage construction. -/
theorem HalfwayPayload.exists_targetLinkingAnnular_of_terminalClean
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
    (hclean : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) D.W D.C) :
    ∃ W : Set (L.stageWeb delta).DPath,
      IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U := by
  exact exists_targetLinkingAnnularCore_of_terminalClean hlower hregular
    huncountable hL hNorm hdeltaBeta hbeta D.linkage D.separator
      D.trimmed D.quotientUnhindered D.links hUfrontier hUsmall
        hCroof hclean

/-- If the designated non-target sources avoid the stop-over, first-hit
normalization supplies the terminal-clean premise automatically.  This is
the movable-request branch of the fixed-stage construction. -/
theorem HalfwayPayload.exists_targetLinkingAnnular_of_avoid
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
    (havoid : Disjoint (U \ (L.stageWeb delta).target) D.C) :
    ∃ W : Set (L.stageWeb delta).DPath,
      IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U := by
  let Q := L.stageWeb delta
  have hNormQ : Q.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized hNorm L delta
  obtain ⟨W', hW', hlinks', hclean, _hforward⟩ :=
    RegularBetaSelection.exists_clean_firstHitPayload hNormQ D.linkage
      (by change U ⊆ L.frontier delta; exact hUfrontier) D.links havoid
  exact exists_targetLinkingAnnularCore_of_terminalClean hlower hregular
    huncountable hL hNorm hdeltaBeta hbeta hW' D.separator D.trimmed
      D.quotientUnhindered hlinks' hUfrontier hUsmall hCroof hclean

end RegularFixedStageTargetLinkingAnnular
end CardinalInduction
end Erdos599

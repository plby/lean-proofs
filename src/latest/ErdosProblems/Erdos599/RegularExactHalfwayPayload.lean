/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExactFrontierInduction
import ErdosProblems.Erdos599.RegularFixedStageTargetLinkingAnnular

/-!
# Exact-frontier half-way payloads for the regular slice

The source-faithful lower half-way clause retains the equality between the
chosen stop-over and the terminal frontier of its linkage.  Consequently
the linkage is terminal-clean at that stop-over.  This removes the local
selected/clean collision from the regular fixed-stage construction: the
existing terminal-clean exchange produces one joint annular linkage which
still links every requested coordinate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExactHalfwayPayload

open SliceCandidate SliceSpliceSource

universe u

variable {V : Type u}

/-- A concrete half-way payload whose stored stop-over is its exact terminal
frontier is already terminal-clean there.  This is the pointwise adapter used
after the causal exact registration has recovered its chosen payload. -/
theorem HalfwayPayload.exists_targetLinkingAnnular_of_exactFrontier
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) {U : Set V}
    (D : HalfwayPayload L delta U)
    (hUfrontier : U ⊆ L.frontier delta) (hUsmall : #U < kappa)
    (hCroof : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hexact : (L.stageWeb delta).terminalFrontier D.W = D.C) :
    ∃ W : Set (L.stageWeb delta).DPath,
      IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U := by
  have hcleanFrontier : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) D.W
      ((L.stageWeb delta).terminalFrontier D.W) :=
    SingularExtension.terminalCleanAt_terminalFrontier_of_isWarp
      D.linkage.isWarp
  have hclean : SingularContinuation.TerminalCleanAt
      (L.stageWeb delta) D.W D.C := by
    simpa only [hexact] using hcleanFrontier
  exact
    RegularFixedStageTargetLinkingAnnular.HalfwayPayload.exists_targetLinkingAnnular_of_terminalClean
      hlower hregular huncountable hL hNorm hdeltaBeta hbeta D
        hUfrontier hUsmall hCroof hclean

/-- The exact lower half-way clause, with the usual countable padding for a
finite request, produces a standard causal payload whose displayed linkage
has *exactly* the stored stop-over as terminal frontier. -/
theorem exists_payload_of_exactLower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (hstage : (L.stageWeb alpha).IsUnhindered)
    {U : Set V} (hUsub : U ⊆ L.frontier alpha)
    (hU : #U < kappa) (hfrontierInfinite : aleph0 ≤ #(L.frontier alpha)) :
    ∃ D : HalfwayPayload L alpha U,
      (L.stageWeb alpha).terminalFrontier D.W = D.C ∧
        SingularContinuation.TerminalCleanAt
          (L.stageWeb alpha) D.W D.C := by
  obtain ⟨U', hUU', hU'sub, hU'infinite, hU'card⟩ :=
    exists_infinite_enlargement hUsub hfrontierInfinite
  have hmax : max (#U) aleph0 < kappa :=
    max_lt_iff.mpr ⟨hU, huncountable⟩
  have hU'lt : #U' < kappa := hU'card.trans_lt hmax
  obtain ⟨W, C, hC, hfrontier, hlinks, hheight⟩ :=
    hlower.exactHalfway hU'lt (L.stageWeb alpha) hstage hU'infinite
      U' (by simpa only [DWeb.KappaLadder.frontier] using hU'sub) rfl
  obtain ⟨X, ⟨hXsource, R, hR, hroof⟩, hXcard⟩ := hheight
  have hXsmall : #X < kappa := hXcard.trans_lt hU'lt
  let D : HalfwayPayload L alpha U :=
    { W := W
      C := C
      X := X
      R := R
      linkage := by
        simpa only [DWeb.KappaLadder.frontier] using hC.linkage
      separator := by
        simpa only [DWeb.KappaLadder.frontier] using hC.separator
      trimmed := hC.minimal
      quotientUnhindered := hC.quotient_unhindered
      links := ControlledSlices.linksToTarget_mono
        (L.stageWeb alpha) W hUU' hlinks
      heightAwayFromSource := by
        simpa only [DWeb.KappaLadder.frontier] using hXsource
      heightWave := hR
      stopoverRoof := hroof
      heightSmall := hXsmall }
  have hcleanFrontier : SingularContinuation.TerminalCleanAt
      (L.stageWeb alpha) W
      ((L.stageWeb alpha).terminalFrontier W) :=
    SingularExtension.terminalCleanAt_terminalFrontier_of_isWarp
      hC.linkage.isWarp
  refine ⟨D, hfrontier, ?_⟩
  simpa only [D] using hfrontier ▸ hcleanFrontier

/-- Exact lower half-way data feeds the existing terminal-clean fixed-stage
exchange and returns one full annular linkage which preserves all request
links.  No selected/clean post-hoc collision repair is used. -/
theorem exists_targetLinkingAnnular_of_exactLower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    (hNorm : Gamma.IsNormalized)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi) (hstage : (L.stageWeb delta).IsUnhindered)
    {U : Set V} (hUfrontier : U ⊆ L.frontier delta)
    (hUsmall : #U < kappa)
    (hfrontierInfinite : aleph0 ≤ #(L.frontier delta))
    (hCroof : ∀ D : HalfwayPayload L delta U,
      (L.stageWeb delta).terminalFrontier D.W = D.C →
        D.C ⊆ (L.stageWeb delta).roof (L.frontier beta)) :
    ∃ W : Set (L.stageWeb delta).DPath,
      IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
          (L.frontier beta) W ∧
        LinksToTarget (L.stageWeb delta) W U := by
  obtain ⟨D, hfrontier, hclean⟩ :=
    exists_payload_of_exactLower hlower huncountable L delta hstage
      hUfrontier hUsmall hfrontierInfinite
  exact
    RegularFixedStageTargetLinkingAnnular.HalfwayPayload.exists_targetLinkingAnnular_of_terminalClean
    hlower.toUniversalCardinalInductionBelow hregular huncountable hL
      hNorm hdeltaBeta hbeta D hUfrontier hUsmall (hCroof D hfrontier)
        hclean

end RegularExactHalfwayPayload
end CardinalInduction
end Erdos599

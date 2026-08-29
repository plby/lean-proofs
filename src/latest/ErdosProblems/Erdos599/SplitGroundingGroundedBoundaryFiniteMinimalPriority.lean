/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFinitePriorityRelation
import ErdosProblems.Erdos599.SplitGroundingGroundedMinimalFrontier
import ErdosProblems.Erdos599.GroundingFinitePriorityGeneralPrivateBoundary

/-!
# Minimal-frontier normalization of the grounded private finite exchange

The private blocker--finite route must be inserted against a separating
frontier, not against the whole bookkeeping boundary.  We choose an
inclusion-minimal separator `T ⊆ BB`, insert the genuine decoded finite trace
with priority, and classify a failure to root its retained endpoint by the
private ambient path supplied by minimality.

The boundary-stop alternative is absent from the resulting last-deleted
data.  What remains is the concrete input for the owner/rank descent: a base
switch deletion, a private backward edge, or a conflict with a private
forward edge.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingErasedDecode GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev MinimalPriorityInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev MinimalPriorityIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Genuine private insertion at a minimal separator.  If the retained
finite boundary point loses all allowed roots, its private ambient path is
either rooted at the reserved source itself, or gives exact non-boundary
last-deleted data for the genuine private trace. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_minimalFrontier_privatePriorityData
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ T : Set V,
      T ⊆ GroundingCut.BB
        (MinimalPriorityInput (L := L) (hL := hL)) S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T ∧
      ∃ (q : FinitePath
            (MinimalPriorityInput (L := L) (hL := hL)).lambda.graph)
          (Q : Alternating.FiniteTrace Gamma.graph) (y : V),
        ∃ hqPrivate : q.support ∩ S.cut =
            {(.old O.later :
              (MinimalPriorityInput (L := L) (hL := hL)).LV)},
        q.start = .old O.later ∧
        q.finish ∈ (MinimalPriorityInput (L := L) (hL := hL)).lambda.target ∧
        (Alternating.AltPath.finite Q).initial = O.later ∧
        (Alternating.AltPath.finite Q).terminal? = some y ∧
        y ∈ (MinimalPriorityInput (L := L) (hL := hL)).targetMarkers ∧
        Alternating.BackwardLinksOn L.limitWarp (.finite Q) ∧
        let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
          (by
            obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
              hlaterFinite, _hlaterCut⟩ := hcase
            exact hlaterFinite)
          q hqPrivate
        let E := erasedSelectedSwitchedEdgesAt
          (MinimalPriorityIndexed (L := L) (hL := hL)
            (hground := hground)) S Kq ∅
        let F := GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T
        F ⊆ {e | Gamma.graph.Adj e.1 e.2} ∧
        Relator.BiUnique (fun x z ↦ (x, z) ∈ F) ∧
        IsReachabilityAntichain F T ∧
        (O.later ∈ T →
          (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen (fun x z ↦ (x, z) ∈ F)
              a O.later) →
          (∃ p : FinitePath Gamma.graph,
              Gamma.IsTargetPathFrom R.record.initial p ∧
              p.support ∩ T = {O.later}) ∨
            Nonempty
              (GroundingFinitePriorityGeneralPrivateBoundary.PrivatePathDeletedData
                E Q T R.record.initial O.later)) := by
  obtain ⟨T, hTsub, hTsep, hTmin, hprivate⟩ :=
    L.exists_splitGroundedMinimalFrontier_with_privatePaths hL hground S
  obtain ⟨q, Q, y, hqPrivate, hqStart, hqTarget, hQInitial,
      hQTerminal, hyTarget, hback, hgeometry⟩ :=
    hcase.exists_privatePriorityRelation
  refine ⟨T, hTsub, hTsep, hTmin, q, Q, y, hqPrivate,
    hqStart, hqTarget, hQInitial, hQTerminal, hyTarget, hback, ?_⟩
  dsimp only
  let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
    (by
      have hcopy := hcase
      obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
        hlaterFinite, _hlaterCut⟩ := hcopy
      exact hlaterFinite)
    q hqPrivate
  let E := erasedSelectedSwitchedEdgesAt
    (MinimalPriorityIndexed (L := L) (hL := hL)
      (hground := hground)) S Kq ∅
  let F := GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T
  have hfacts := hgeometry T
  refine ⟨hfacts.1, hfacts.2.1, hfacts.2.2, ?_⟩
  intro hlaterT hunrooted
  obtain ⟨a, haSource, p, hpTarget, hpT⟩ := hprivate O.later hlaterT
  by_cases ha : a = R.record.initial
  · left
    subst a
    exact ⟨p, hpTarget, hpT⟩
  · right
    exact
      GroundingFinitePriorityGeneralPrivateBoundary.exists_privatePathDeletedData
        E Q T R.record.initial O.later a haSource ha p hpTarget hpT
          hunrooted

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_minimalFrontier_privatePriorityData

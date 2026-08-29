/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFinitePriorityRelation
import ErdosProblems.Erdos599.GroundingFinitePriorityPrivateBoundary

/-!
# Ambient normalization of a grounded finite-priority boundary defect

An unrooted boundary point is normalized with the ambient separator, not by
incorrectly treating switched reachability as separation.  Either the point
can be removed while preserving separation, or there is a private ambient
source--target path through it.  The private path starts at the deliberately
deleted source, or its last deleted edge has no boundary-stop alternative.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev PriorityOutcomeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev PriorityOutcomeIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Total ambient normal form of the private-parent priority exchange. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_parentPriorityOutput_or_privateBoundary
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (PriorityOutcomeInput (L := L) (hL := hL)) S.cut) ∨
      ∃ (q : FinitePath
            (PriorityOutcomeInput (L := L) (hL := hL)).lambda.graph)
          (Q : Alternating.FiniteTrace Gamma.graph) (u b : V),
        ∃ hqPrivate : q.support ∩ S.cut =
            {(.old O.later :
              (PriorityOutcomeInput (L := L) (hL := hL)).LV)},
        q.start = .old O.later ∧
        (Alternating.AltPath.finite Q).directionEdges .forward = ∅ ∧
        u ∈ Gamma.source ∧
        let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
          (by
            obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
              hlaterFinite, _hlaterCut⟩ := hcase
            exact hlaterFinite)
          q hqPrivate
        let E := erasedSelectedSwitchedEdgesAt
          (PriorityOutcomeIndexed (L := L) (hL := hL)
            (hground := hground)) S Kq ∅
        let B := GroundingCut.BB
          (PriorityOutcomeInput (L := L) (hL := hL)) S.cut
        b ∈ B ∧
          (Popular.IsSeparator Gamma (B \ {b}) ∨
            (∃ p : FinitePath Gamma.graph,
              Gamma.IsTargetPathFrom u p ∧ p.support ∩ B = {b}) ∨
            Nonempty
              (GroundingFinitePriorityPrivateBoundary.PrivatePathDeletedData
                E Q B u b)) := by
  obtain ⟨q, Q, u, hqPrivate, hqStart, hforwardEmpty, huSource,
      houtput | hroot⟩ :=
    hcase.exists_parentPriorityOutput_or_rootObstruction
  · exact Or.inl houtput
  · right
    obtain ⟨b, hb, hbPriority, _hbaseClassification⟩ := hroot
    refine ⟨q, Q, u, b, hqPrivate, hqStart, hforwardEmpty,
      huSource, ?_⟩
    dsimp only
    let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
      (by
        have hcopy := hcase
        obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
          hlaterFinite, _hlaterCut⟩ := hcopy
        exact hlaterFinite)
      q hqPrivate
    let E := erasedSelectedSwitchedEdgesAt
      (PriorityOutcomeIndexed (L := L) (hL := hL)
        (hground := hground)) S Kq ∅
    let B := GroundingCut.BB
      (PriorityOutcomeInput (L := L) (hL := hL)) S.cut
    refine ⟨hb, ?_⟩
    have hBseparator : Popular.IsSeparator Gamma B :=
      L.splitGroundedAssertion8_18 hL.legal S.cut S.separates
    rcases
        GroundingSeparatorPointRemoval.separator_diff_singleton_or_privatePath
          B hBseparator hb with hremove | hprivate
    · exact Or.inl hremove
    · obtain ⟨a, haSource, p, hpTarget, hpBoundary⟩ := hprivate
      by_cases hau : a = u
      · subst a
        exact Or.inr (Or.inl ⟨p, hpTarget, hpBoundary⟩)
      · exact Or.inr (Or.inr <|
          GroundingFinitePriorityPrivateBoundary.exists_privatePathDeletedData
            E Q B u b a hforwardEmpty haSource hau p hpTarget hpBoundary
            hbPriority)

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_parentPriorityOutput_or_privateBoundary

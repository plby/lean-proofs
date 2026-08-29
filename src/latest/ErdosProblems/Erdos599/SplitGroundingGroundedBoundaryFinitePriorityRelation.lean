/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFinitePriorityControls
import ErdosProblems.Erdos599.GroundingFinitePriorityRelation
import ErdosProblems.Erdos599.GroundingAssertion822Output
import ErdosProblems.Erdos599.GroundingFinitePriorityRootObstruction

/-!
# The grounded private finite-priority relation

At a blocking--finite boundary duplicate, the private auxiliary route is
first used to reselect every ordinary request away from its literal support.
Its decoded ambient trace is then inserted with priority: all of its backward
edges and all incidence-conflicting ordinary edges are deleted before its
forward edges are inserted.  Stopping at a boundary may delete a forward edge
whose tail is the displayed finite point, but the backward deletion remains;
this is the precise operation which cuts the duplicated grounded parent.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingErasedDecode GroundingErasedForwardConflict
  GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev PriorityInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev PriorityIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- The exact private route together with the globally usable relation
obtained by inserting its ambient decode ahead of the reselected ordinary
switch. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_privatePriorityRelation
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (q : FinitePath (PriorityInput (L := L) (hL := hL)).lambda.graph)
        (Q : Alternating.FiniteTrace Gamma.graph) (y : V),
      ∃ hqPrivate : q.support ∩ S.cut =
          {(.old O.later : (PriorityInput (L := L) (hL := hL)).LV)},
      q.start = .old O.later ∧
      q.finish ∈ (PriorityInput (L := L) (hL := hL)).lambda.target ∧
      (Alternating.AltPath.finite Q).initial = O.later ∧
      (Alternating.AltPath.finite Q).terminal? = some y ∧
      y ∈ (PriorityInput (L := L) (hL := hL)).targetMarkers ∧
      Alternating.BackwardLinksOn L.limitWarp (.finite Q) ∧
      let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
        (by
          obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
            hlaterFinite, _hlaterCut⟩ := hcase
          exact hlaterFinite)
        q hqPrivate
      let E := erasedSelectedSwitchedEdgesAt
        (PriorityIndexed (L := L) (hL := hL) (hground := hground))
        S Kq ∅
      ∀ T : Set V,
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T ⊆
            {e | Gamma.graph.Adj e.1 e.2} ∧
        Relator.BiUnique (fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T) ∧
        IsReachabilityAntichain
      (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T) T := by
  have hcase' := hcase
  obtain ⟨P0, _hP0G0, _hP0block, _hP0point, _hP0terminal,
      hlaterFinite, _hlaterCut⟩ := hcase'
  obtain ⟨P, q, Q, y, _hPG0, _hPterminal, hqStart, hqTarget,
      _hqAvoid, hqPrivate, _hqPure, hQInitial, hQTerminal,
      hyTarget, _hyParent, _hlaterFrontier, _hyInitial,
      _hnoForward, hback⟩ :=
    SplitGroundedBlockingFiniteTerminalCase.exists_private_finite_exchange
      hcase
  refine ⟨q, Q, y, hqPrivate, hqStart, hqTarget, hQInitial,
    hQTerminal, hyTarget, hback, ?_⟩
  dsimp only
  intro T
  let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
    hlaterFinite q hqPrivate
  let E := erasedSelectedSwitchedEdgesAt
    (PriorityIndexed (L := L) (hL := hL) (hground := hground))
    S Kq ∅
  have hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    erasedSelectedSwitchedEdgesAt_subset_adj
      (PriorityIndexed (L := L) (hL := hL) (hground := hground))
      S Kq ∅
  have hEunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) :=
    erasedSelectedSwitchedEdgesAt_biUnique
      (PriorityIndexed (L := L) (hL := hL) (hground := hground))
      S Kq ∅ (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
  exact ⟨
    GroundingFinitePriorityRelation.finitePriorityEdgesAt_subset_adj
      E Q T hEadj,
    GroundingFinitePriorityRelation.finitePriorityEdgesAt_biUnique
      E Q T hEunique,
    GroundingFinitePriorityRelation.finitePriorityEdgesAt_reachabilityAntichain
      E Q T⟩

/-- Source-faithful parent deletion form of the finite priority exchange.

The auxiliary private path is used only to reselect the ordinary requests.
The priority trace itself is the canonical whole-parent backward trace.  Its
forward relation is literally empty, so every one of its backward edges is
absent from the final stopped relation. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_parentPriorityDeletion
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (q : FinitePath (PriorityInput (L := L) (hL := hL)).lambda.graph)
        (Q : Alternating.FiniteTrace Gamma.graph) (u : V),
      ∃ hqPrivate : q.support ∩ S.cut =
          {(.old O.later : (PriorityInput (L := L) (hL := hL)).LV)},
      q.start = .old O.later ∧
      Alternating.IsTerminalContactSwitching L.limitWarp Q u ∧
      Q.initial = O.later ∧
      (Alternating.AltPath.finite Q).directionEdges .forward = ∅ ∧
      u ∈ Gamma.source ∧
      let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
        (by
          obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
            hlaterFinite, _hlaterCut⟩ := hcase
          exact hlaterFinite)
        q hqPrivate
      let E := erasedSelectedSwitchedEdgesAt
        (PriorityIndexed (L := L) (hL := hL) (hground := hground))
        S Kq ∅
      ∀ T : Set V,
        GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T ⊆
            {e | Gamma.graph.Adj e.1 e.2} ∧
        Relator.BiUnique (fun x y ↦ (x, y) ∈
          GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T) ∧
        IsReachabilityAntichain
          (GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T) T ∧
        ∀ e ∈ (Alternating.AltPath.finite Q).directionEdges .backward,
          e ∉ GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q T := by
  have hcaseFields := hcase
  obtain ⟨P0, _hP0G0, _hP0block, _hP0point, _hP0terminal,
      hlaterFinite, _hlaterCut⟩ := hcaseFields
  obtain ⟨P, q, _Q0, _y, _hPG0, _hPterminal, hqStart, _hqTarget,
      _hqAvoid, hqPrivate, _hqPure, _hQInitial, _hQTerminal,
      _hyTarget, _hyParent, _hlaterFrontier, _hyInitial,
      _hnoForward, _hback⟩ :=
    SplitGroundedBlockingFiniteTerminalCase.exists_private_finite_exchange
      hcase
  obtain ⟨Q, u, hswitch, hQinitial, hforwardEmpty,
      _huInitial, huSource⟩ :=
    SplitGroundedBlockingFiniteTerminalCase.exists_parentBackwardTerminalContactSwitching
      hcase
  refine ⟨q, Q, u, hqPrivate, hqStart, hswitch, hQinitial,
    hforwardEmpty, huSource, ?_⟩
  dsimp only
  intro T
  let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
    hlaterFinite q hqPrivate
  let E := erasedSelectedSwitchedEdgesAt
    (PriorityIndexed (L := L) (hL := hL) (hground := hground))
    S Kq ∅
  have hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    erasedSelectedSwitchedEdgesAt_subset_adj
      (PriorityIndexed (L := L) (hL := hL) (hground := hground))
      S Kq ∅
  have hEunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) :=
    erasedSelectedSwitchedEdgesAt_biUnique
      (PriorityIndexed (L := L) (hL := hL) (hground := hground))
      S Kq ∅ (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
  refine ⟨
    GroundingFinitePriorityRelation.finitePriorityEdgesAt_subset_adj
      E Q T hEadj,
    GroundingFinitePriorityRelation.finitePriorityEdgesAt_biUnique
      E Q T hEunique,
    GroundingFinitePriorityRelation.finitePriorityEdgesAt_reachabilityAntichain
      E Q T, ?_⟩
  intro e he
  exact
    GroundingFinitePriorityRelation.backward_not_mem_finitePriorityEdgesAt_of_forward_empty
      E Q T hforwardEmpty he

/-- Total source-rooted outcome after the private parent deletion.  If the
modified full-boundary relation is rooted away from the deleted parent's
original source, Assertion 8.22 is complete.  Otherwise the result retains
the exact unrooted boundary point for the deleted-edge normalizer. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_parentPriorityOutput_or_rootObstruction
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (q : FinitePath (PriorityInput (L := L) (hL := hL)).lambda.graph)
        (Q : Alternating.FiniteTrace Gamma.graph) (u : V),
      ∃ hqPrivate : q.support ∩ S.cut =
          {(.old O.later : (PriorityInput (L := L) (hL := hL)).LV)},
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
        (PriorityIndexed (L := L) (hL := hL) (hground := hground))
        S Kq ∅
      let B := GroundingCut.BB
        (PriorityInput (L := L) (hL := hL)) S.cut
      let F := GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B
      Nonempty (GroundingFinalAssembly.Assertion822Output
          (PriorityInput (L := L) (hL := hL)) S.cut) ∨
        ∃ b ∈ B,
          (¬ ∃ a ∈ Gamma.source \ {u},
            Relation.ReflTransGen (fun x y ↦ (x, y) ∈ F) a b) ∧
          ((¬ ∃ a ∈ Gamma.source \ {u},
              Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) ∨
            Nonempty
              (GroundingFinitePriorityRootObstruction.PriorityDeletedRootData
                E Q B (Gamma.source \ {u}) b)) := by
  obtain ⟨q, Q, u, hqPrivate, hqStart, _hswitch, _hQinitial,
      hforwardEmpty, huSource, hgeometry⟩ :=
    hcase.exists_parentPriorityDeletion
  refine ⟨q, Q, u, hqPrivate, hqStart, hforwardEmpty, huSource, ?_⟩
  dsimp only
  let Kq := splitGroundedPrivateSupportAvoidingControls K O.later
    (by
      have hcopy := hcase
      obtain ⟨P, _hPG0, _hblock, _hpoint, _hterminal,
        hlaterFinite, _hlaterCut⟩ := hcopy
      exact hlaterFinite)
    q hqPrivate
  let E := erasedSelectedSwitchedEdgesAt
    (PriorityIndexed (L := L) (hL := hL) (hground := hground))
    S Kq ∅
  let B := GroundingCut.BB
    (PriorityInput (L := L) (hL := hL)) S.cut
  let F := GroundingFinitePriorityRelation.finitePriorityEdgesAt E Q B
  have hfacts := hgeometry B
  by_cases hroot : ∀ b ∈ B, ∃ a ∈ Gamma.source \ {u},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ F) a b
  · left
    apply GroundingAssertion822Output.exists_of_rootedReachability
      (PriorityInput (L := L) (hL := hL)) S.cut F
      (Gamma.source \ {u}) B
    · exact hfacts.1
    · exact hfacts.2.1
    · exact Set.sdiff_subset
    · exact Set.Subset.rfl
    · exact L.splitGroundedAssertion8_18 hL.legal S.cut S.separates
    · exact hfacts.2.2.1
    · exact hroot
    · exact huSource
    · simp
  · right
    have hunrooted : ∃ b ∈ B, ¬ ∃ a ∈ Gamma.source \ {u},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ F) a b := by
      by_contra hnone
      apply hroot
      intro b hb
      by_contra hbnot
      exact hnone ⟨b, hb, hbnot⟩
    obtain ⟨b, hb, hbPriority⟩ := hunrooted
    refine ⟨b, hb, hbPriority, ?_⟩
    by_cases hbBase : ∃ a ∈ Gamma.source \ {u},
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
    · exact Or.inr <|
        GroundingFinitePriorityRootObstruction.exists_priorityDeletedRootData
          E Q B (Gamma.source \ {u}) b
          (erasedSelectedSwitchedEdgesAt_subset_adj
            (PriorityIndexed (L := L) (hL := hL)
              (hground := hground)) S Kq ∅)
          hforwardEmpty hbBase hbPriority
    · exact Or.inl hbBase

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_privatePriorityRelation
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_parentPriorityDeletion
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_parentPriorityOutput_or_rootObstruction

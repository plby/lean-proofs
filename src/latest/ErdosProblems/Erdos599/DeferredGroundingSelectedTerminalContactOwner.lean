/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedFiniteStartEndpoint
import ErdosProblems.Erdos599.DeferredGroundingSelectedReferenceOwner

/-!
# Concrete owners of deferred terminal-contact failures

The two negated predicates left by terminal-contact normalization are pulled
back to the actual final strong-selected route.  Each supplies a literal
limiting-warp owner, and that owner is classified as grounded, attached at
the request apex, or inessential.  These are the concrete ports used by the
whole-owner transaction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder Stationary
open PopularGroundingBridge GroundingSimultaneousDecode
open Alternating PopularAuxiliary.Input GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A forward edge that violates `ForwardLinksOff` has a literal owner in
the limiting warp, with the source/apex/inessential classification needed
by the simultaneous component transaction. -/
theorem reservedStrongSelected_forwardReferenceOwner_exists
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Q : FiniteTrace Gamma.graph)
    (hQ : (selectedErasedCompression
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path = .finite Q)
    (hnot : ¬ ForwardLinksOff
      (canonicalDeferredLadder Gamma kappa preferred).limitWarp (.finite Q)) :
    ∃ e : V × V, ∃ Y : Gamma.DPath,
      e ∈ (AltPath.finite Q).directionEdges .forward ∧
        Y ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp ∧
        e ∈ Y.edgeSet ∧
        (Y.initial ∈ Gamma.source ∨
          requestAuxVertex r ∈ PopularSwitching.ladderTrace
            (popularAuxiliaryInput
              (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  simp only [ForwardLinksOff, not_forall] at hnot
  obtain ⟨l, hl, hldir, hnotDisjoint⟩ := hnot
  obtain ⟨e, hel, heFamily⟩ := Set.not_disjoint_iff.1 hnotDisjoint
  simp only [Alternating.familyEdges, Set.mem_iUnion] at heFamily
  obtain ⟨Y, hY, heY⟩ := heFamily
  have heForwardQ : e ∈ (AltPath.finite Q).directionEdges .forward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hel⟩
  have heForwardSelected : e ∈
      (selectedErasedCompression U S K r).path.directionEdges .forward := by
    rw [hQ]
    exact heForwardQ
  refine ⟨e, Y, heForwardQ, hY, heY, ?_⟩
  by_cases hessential : Y ∈ Gamma.essentialWarpPart L.limitWarp
  · have hYEssential : Y ∈ J.essentialLadder := by
      simpa only [J, popularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder, limitWarp] using hessential
    rcases
        canonicalDeferredLadder_reservedStrongSelected_forwardReferenceOwner_grounded_or_apex
          preferred hkappa huncountable hNoEnter hL S r Y hYEssential
            heForwardSelected heY with hgrounded | hapex
    · exact Or.inl hgrounded
    · exact Or.inr (Or.inl hapex)
  · exact Or.inr (Or.inr ⟨hY, hessential⟩)

/-- A forward vertex witnessing failure of terminal contact coverage has a
literal limiting-warp owner with the same canonical classification.  The
non-backward and nonterminal certificates are retained verbatim. -/
theorem reservedStrongSelected_uncoveredForwardOwner_exists
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Q : FiniteTrace Gamma.graph)
    (hQ : (selectedErasedCompression
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path = .finite Q)
    (hnot : ¬ ForwardVertexContactsCoveredAtTerminal
      Gamma (canonicalDeferredLadder Gamma kappa preferred).limitWarp
        (.finite Q)) :
    ∃ x : V, ∃ Y : Gamma.DPath,
      x ∈ (AltPath.finite Q).directionVertices .forward ∧
        Y ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp ∧
        x ∈ Y.support ∧
        x ∉ (AltPath.finite Q).directionVertices .backward ∧
        (AltPath.finite Q).terminal? ≠ some x ∧
        (Y.initial ∈ Gamma.source ∨
          requestAuxVertex r ∈ PopularSwitching.ladderTrace
            (popularAuxiliaryInput
              (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  simp only [ForwardVertexContactsCoveredAtTerminal, not_forall, not_or] at hnot
  obtain ⟨x, hxForward, hxWarp, hxNotBackward, hxNotTerminal⟩ := hnot
  obtain ⟨Y, hY, hxY⟩ := hxWarp
  have hxForwardSelected : x ∈
      (selectedErasedCompression U S K r).path.directionVertices .forward := by
    rw [hQ]
    exact hxForward
  refine ⟨x, Y, hxForward, hY, hxY, hxNotBackward, hxNotTerminal, ?_⟩
  by_cases hessential : Y ∈ Gamma.essentialWarpPart L.limitWarp
  · have hYEssential : Y ∈ J.essentialLadder := by
      simpa only [J, popularAuxiliaryInput,
        PopularAuxiliary.Input.essentialLadder, limitWarp] using hessential
    rcases
        canonicalDeferredLadder_reservedStrongSelected_forwardVertexOwner_grounded_or_apex
          preferred hkappa huncountable hNoEnter hL S r Y hYEssential
            hxForwardSelected hxY with hgrounded | hapex
    · exact Or.inl hgrounded
    · exact Or.inr (Or.inl hapex)
  · exact Or.inr (Or.inr ⟨hY, hessential⟩)

/-- When the selected request exits at the initial vertex of a displayed
limiting component, the apex alternative in the forward-reference failure
is not a third owner: warp disjointness identifies it with that terminal
component.  Thus the only other owners are genuinely source-grounded or
inessential. -/
theorem reservedStrongSelected_forwardReferenceOwner_grounded_or_terminal_or_inessential
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (Q : FiniteTrace Gamma.graph)
    (hQ : (selectedErasedCompression
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path = .finite Q)
    (hnot : ¬ ForwardLinksOff
      (canonicalDeferredLadder Gamma kappa preferred).limitWarp (.finite Q)) :
    ∃ e : V × V, ∃ Y : Gamma.DPath,
      e ∈ (AltPath.finite Q).directionEdges .forward ∧
        Y ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp ∧
        e ∈ Y.edgeSet ∧
        (Y.initial ∈ Gamma.source ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  obtain ⟨e, Y, he, hY, heY, howner⟩ :=
    reservedStrongSelected_forwardReferenceOwner_exists
      preferred hkappa huncountable hNoEnter hL S r Q hQ hnot
  refine ⟨e, Y, he, hY, heY, ?_⟩
  rcases howner with hgrounded | hapex | hinessential
  · exact Or.inl hgrounded
  · exact Or.inr (Or.inl
      (eq_terminalOwner_of_requestAuxVertex_mem_ladderTrace
        J r (W := L.limitWarp) (by
          simpa only [L, J, popularAuxiliaryInput, limitWarp] using
            (popularAuxiliaryInput L hL.legal).ladder.disjoint)
        Y Z hY hZ hapex hexit))
  · exact Or.inr (Or.inr hinessential)

/-- The same terminal-owner collapse for an uncovered selected forward
vertex.  The witness keeps the non-backward and nonterminal certificates
needed for the subsequent last-contact transaction. -/
theorem reservedStrongSelected_uncoveredForwardOwner_grounded_or_terminal_or_inessential
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Z : Gamma.DPath)
    (hZ : Z ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    (hexit : requestExit r = Z.initial)
    (Q : FiniteTrace Gamma.graph)
    (hQ : (selectedErasedCompression
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path = .finite Q)
    (hnot : ¬ ForwardVertexContactsCoveredAtTerminal
      Gamma (canonicalDeferredLadder Gamma kappa preferred).limitWarp
        (.finite Q)) :
    ∃ x : V, ∃ Y : Gamma.DPath,
      x ∈ (AltPath.finite Q).directionVertices .forward ∧
        Y ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp ∧
        x ∈ Y.support ∧
        x ∉ (AltPath.finite Q).directionVertices .backward ∧
        (AltPath.finite Q).terminal? ≠ some x ∧
        (Y.initial ∈ Gamma.source ∨ Y = Z ∨
          Y ∈ Gamma.inessentialPaths
            (canonicalDeferredLadder Gamma kappa preferred).limitWarp) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  obtain ⟨x, Y, hx, hY, hxY, hxNotBackward, hxNotTerminal, howner⟩ :=
    reservedStrongSelected_uncoveredForwardOwner_exists
      preferred hkappa huncountable hNoEnter hL S r Q hQ hnot
  refine ⟨x, Y, hx, hY, hxY, hxNotBackward, hxNotTerminal, ?_⟩
  rcases howner with hgrounded | hapex | hinessential
  · exact Or.inl hgrounded
  · exact Or.inr (Or.inl
      (eq_terminalOwner_of_requestAuxVertex_mem_ladderTrace
        J r (W := L.limitWarp) (by
          simpa only [L, J, popularAuxiliaryInput, limitWarp] using
            (popularAuxiliaryInput L hL.legal).ladder.disjoint)
        Y Z hY hZ hapex hexit))
  · exact Or.inr (Or.inr hinessential)

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelected_forwardReferenceOwner_exists
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelected_uncoveredForwardOwner_exists
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelected_forwardReferenceOwner_grounded_or_terminal_or_inessential
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelected_uncoveredForwardOwner_grounded_or_terminal_or_inessential

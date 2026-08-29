/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedRelevantPruning
import ErdosProblems.Erdos599.GroundingInputRelevantSourceFirst

/-!
# The source-first boundary for the final deferred selector

This specializes the input-level first-hit construction to the actual final
deferred controls: the simultaneously pruned family contains the one
reserved record and every starting record of the strong selected request
family.  The resulting frontier is a separating subset of the final relevant
boundary and each of its points carries its literal private source-prefix
witness.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

/-- The first relevant-boundary contacts on roofed ambient source prefixes,
for the final reserved strong-selected pruning datum. -/
def reservedStrongSelectedSourceFirstBB : Set V :=
  GroundingInputRelevantSourceFirst.sourceFirstBB
    (reservedStrongSelectedPruningData
      (L := L) (hL := hL) (S := S))

theorem reservedStrongSelectedSourceFirstBB_subset_relevantBB :
    reservedStrongSelectedSourceFirstBB
        (L := L) (hL := hL) (S := S) ⊆
      reservedStrongSelectedRelevantBB
        (L := L) (hL := hL) (S := S) :=
  GroundingInputRelevantSourceFirst.sourceFirstBB_subset_relevantBB
    (reservedStrongSelectedPruningData
      (L := L) (hL := hL) (S := S))

/-- The source-first final deferred frontier still separates the ambient
web. -/
theorem reservedStrongSelectedSourceFirstBB_isSeparator :
    Popular.IsSeparator Gamma
      (reservedStrongSelectedSourceFirstBB
        (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantSourceFirst.sourceFirstBB_isSeparator
    (reservedStrongSelectedPruningData
      (L := L) (hL := hL) (S := S))
    reservedStrongSelectedRelevantFiniteDescentDecoder
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

/-- Unpack the exact source-prefix carried by a source-first frontier point. -/
theorem exists_reservedStrongSelected_sourceFirstPrefix
    {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S)) :
    ∃ R : FinitePath Gamma.graph,
      R.start ∈ Gamma.source ∧
      R.finish = b ∧
      R.support ⊆ (popularAuxiliaryInput L hL.legal).roofRegion ∧
      b ∈ reservedStrongSelectedRelevantBB
        (L := L) (hL := hL) (S := S) ∧
      ∀ x ∈ R.walk.support.dropLast,
        x ∉ reservedStrongSelectedRelevantBB
          (L := L) (hL := hL) (S := S) := by
  exact hb

/-- An escaping blocker at the final deferred source-first frontier is
either already an ambient source, or carries the exact virtual-forward
escape which the selected-route exchange must absorb. -/
theorem reservedStrongSelected_sourceFirst_escapeBlocker_source_or_virtual
    {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (P : (popularAuxiliaryInput L hL.legal).Fragment)
    (hP : P ∈ (reservedStrongSelectedPruningData
      (L := L) (hL := hL) (S := S)).relevantG0)
    (hblock : GroundingCut.blockingPoint
      (popularAuxiliaryInput L hL.legal) S.cut P = b)
    (hescape : P.MeetsEscape
      (popularAuxiliaryInput L hL.legal) S.cut) :
    b ∈ Gamma.source ∨
      Nonempty (GroundingInputRelevantDecoder.RelevantVirtualEscape
        (popularAuxiliaryInput L hL.legal) S.cut b) := by
  obtain ⟨R, hsource, hfinish, hroof, _hbRelevant, hfirst⟩ := hb
  have hout := GroundingInputRelevantDecoder.sourceFirst_escapeBlocker_source_or_virtual
    (reservedStrongSelectedPruningData
      (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    S.separates R hsource hroof (fun {x} hx ↦ hfirst x hx) P hP
      (hblock.trans hfinish.symm) hescape
  simpa only [hfinish] using hout

/-- Relation-facing form: an escaping source-first blocker is already
rooted in the final native relation stopped at the source-first frontier,
unless it carries the genuine virtual-forward escape. -/
theorem reservedStrongSelected_sourceFirst_escapeBlocker_rooted_or_virtual
    {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (P : (popularAuxiliaryInput L hL.legal).Fragment)
    (hP : P ∈ (reservedStrongSelectedPruningData
      (L := L) (hL := hL) (S := S)).relevantG0)
    (hblock : GroundingCut.blockingPoint
      (popularAuxiliaryInput L hL.legal) S.cut P = b)
    (hescape : P.MeetsEscape
      (popularAuxiliaryInput L hL.legal) S.cut) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
          (popularAuxiliaryIndexed L hL) S
          (reservedGroundedCarrierControls L hL S)
          (reservedStrongSelectedSourceFirstBB
            (L := L) (hL := hL) (S := S))) a b) ∨
      Nonempty (GroundingInputRelevantDecoder.RelevantVirtualEscape
        (popularAuxiliaryInput L hL.legal) S.cut b) := by
  rcases reservedStrongSelected_sourceFirst_escapeBlocker_source_or_virtual
      hb P hP hblock hescape with hsource | hvirtual
  · exact Or.inl ⟨b, hsource, Relation.ReflTransGen.refl⟩
  · exact Or.inr hvirtual

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelectedSourceFirstBB_isSeparator
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelected_sourceFirst_escapeBlocker_source_or_virtual
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelected_sourceFirst_escapeBlocker_rooted_or_virtual

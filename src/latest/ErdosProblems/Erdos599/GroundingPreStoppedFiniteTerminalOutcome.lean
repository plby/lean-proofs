/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceTerminalOutcome
import ErdosProblems.Erdos599.GroundingPreStoppedBlockingCollisionReduction

/-!
# Internal terminal outcome of a pre-stopped finite exchange

The finite branch of the pre-stopped boundary classifier already retains a
concrete finite trace and its fresh target-marker endpoint.  This file feeds
that payload to `finiteSourceTerminalOutcome`.  Consequently the branch is
either an actual terminal-contact switch, or it displays one of the two
genuine normalization failures left after endpoint and first-direction
geometry have been discharged.
-/

noncomputable section

namespace Erdos599
namespace DWeb.KappaLadder
namespace Assertion822PreStoppedBoundaryObstruction

open Set Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every private finite exchange from the first-boundary classifier carries
the exact total terminal-contact outcome of its displayed finite trace. -/
theorem PrivateFiniteExchange.exists_terminalOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (h : PrivateFiniteExchange o) :
    ∃ (Q : FiniteTrace Gamma.graph) (y : V),
      Q.initial = o.later ∧
      Q.terminal = y ∧
      y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
      o.later ∈ Gamma.terminalFrontier
        (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
      FiniteSourceTerminalOutcome
        (L.popularAuxiliaryInput hL.legal).ladder.paths Q y := by
  rcases h with ⟨q, Q, y, _hqStart, _hqTarget, _hqAvoid, _hqPrivate,
    _hqPure, hQInitial, hQTerminal, hyTarget, hlaterFrontier,
    _hyInitial, hnoForward, hparent, hback⟩
  have hQi : Q.initial = o.later := by
    change Q.initial = o.later at hQInitial
    exact hQInitial
  have hQt : Q.terminal = y := by
    simpa only [AltPath.terminal?_finite, Option.some.injEq] using hQTerminal
  have hinitialVertex : Q.initial ∈ Gamma.vertexSet
      (L.popularAuxiliaryInput hL.legal).ladder.paths := by
    rw [hQi]
    exact terminalFrontier_subset_vertexSet _ hlaterFrontier
  obtain ⟨P, _hPG0, _hblocking, hPterminal, hyParent⟩ := hparent
  have hlaterParent : o.later ∈ P.parent.support := by
    apply P.support_subset
    exact Gamma.terminal_mem_support hPterminal
  have hne : Q.initial ≠ y := by
    rw [hQi]
    intro hEq
    apply hyParent
    exact hEq ▸ hlaterParent
  refine ⟨Q, y, hQi, hQt, hyTarget, hlaterFrontier, ?_⟩
  exact L.finiteSourceTerminalOutcome hL.legal hback hinitialVertex hne
    hQt hyTarget hnoForward

/-- The finite branch retains enough auxiliary-path data to reconstruct the
actual decoder `MicroTrace`.  Its erased compression is necessarily a finite
trace: the initial finite-source terminal lies on the grounded parent, while
the decoded target marker is disjoint from that parent.  This is the
provenance-preserving form needed by contact-aware normalization. -/
theorem PrivateFiniteExchange.exists_microTrace_compression
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (hcase : BlockingFiniteTerminalCase o)
    (h : PrivateFiniteExchange o) :
    ∃ (q : _root_.Erdos599.DirectedPath.FinitePath
          (L.popularAuxiliaryInput hL.legal).lambda.graph)
        (T : (L.popularAuxiliaryInput hL.legal).MicroTrace q)
        (Q : FiniteTrace Gamma.graph) (y : V),
      q.start = .old o.later ∧
      q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
      (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
        (S.cut \ {(.old o.later :
          (L.popularAuxiliaryInput hL.legal).LV)}) ∧
      q.support ∩ S.cut =
        {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} ∧
      (L.popularAuxiliaryInput hL.legal).IsTargetPure q ∧
      T.erasedCompression.path = .finite Q ∧
      T.initial = o.later ∧ T.terminal = y ∧
      y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
      (∀ z, (y, z) ∉
        (AltPath.finite Q).directionEdges .forward) ∧
      BackwardLinksOn
        (L.popularAuxiliaryInput hL.legal).ladder.paths (.finite Q) := by
  rcases h with ⟨q, _Q₀, _y₀, hqStart, hqTarget, hqAvoid,
    hqPrivate, hqPure, _hQInitial, _hQTerminal, _hyTarget,
    _hlaterFrontier, _hyInitial, _hnoForward, hfragment, _hback⟩
  obtain ⟨_Pcase, _hPG0case, _hblockable, _hPearly,
    _hterminalCase, hlater⟩ := hcase
  obtain ⟨P, _hPG0, _hblocking, hPTerminal, _hyParent⟩ := hfragment
  obtain ⟨T, hTInitial, hyTarget, hAInitial, hATerminal,
      hnoForward, hback⟩ :=
    _root_.Erdos599.GroundingFiniteSourceDuplicateExchange.exists_microTrace_of_finiteSource_target_path
      (L.popularAuxiliaryInput hL.legal) q hqStart hlater.1 hqTarget
  have hcP : o.later ∈ P.path.support :=
    Gamma.terminal_mem_support hPTerminal
  have hparentGrounded :=
    L.fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
      hL.legal P hlater.1 hcP
  have hdisjoint :=
    L.groundedRecord_support_disjoint_targetMarkers
      hL.legal hparentGrounded
  have hyParent : T.terminal ∉ P.parent.support := by
    intro hy
    exact Set.disjoint_left.1 hdisjoint hy hyTarget
  have hne : T.initial ≠ T.terminal := by
    rw [hTInitial]
    intro heq
    apply hyParent
    exact heq ▸ P.support_subset hcP
  cases hA : T.erasedCompression.path with
  | trivial a =>
      have hai : a = T.initial := by
        have haLater : a = o.later := by
          simpa only [hA, AltPath.initial_trivial] using hAInitial
        exact haLater.trans hTInitial.symm
      have hat : a = T.terminal := by
        have : (some a : Option V) = some T.terminal := by
          simpa only [hA, AltPath.terminal?_trivial] using hATerminal
        exact Option.some.inj this
      exact False.elim (hne (hai.symm.trans hat))
  | finite Q =>
      refine ⟨q, T, Q, T.terminal, hqStart, hqTarget, hqAvoid,
        hqPrivate, hqPure, hA, hTInitial, rfl, hyTarget, ?_, ?_⟩
      · simpa only [hA] using hnoForward
      · simpa only [hA] using hback
  | infinite r =>
      have : (none : Option V) = some T.terminal := by
        simpa only [hA, AltPath.terminal?_infinite] using hATerminal
      cases this

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.PrivateFiniteExchange.exists_terminalOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.PrivateFiniteExchange.exists_microTrace_compression

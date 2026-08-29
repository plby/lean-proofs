/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFiniteSwitch
import ErdosProblems.Erdos599.GroundingFiniteSourceDuplicateExchangeCore
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# The private split-grounded exchange at a finite boundary duplicate

A residual blocker--finite collision is genuine: a finite cut source need
not itself index a selected request.  Its displayed blocking fragment does,
however, supply the source-faithful exchange used in Assertion 8.22.  Run
backwards from the finite terminal to the blocker and then along the escape.
The resulting private auxiliary source--target path decodes to a nontrivial
finite alternating trace from the finite terminal to a target marker on a
different limiting-ladder component.

This is the split-legal version of the legacy finite-source duplicate
exchange.  It uses no conversion to ordinary legality.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev FiniteExchangeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- A grounded record remains inessential in the limiting warp and hence
its whole support misses every target marker of the grounded auxiliary. -/
theorem splitGrounded_record_support_disjoint_targetMarkers
    {p : Gamma.DPath} {a : Ladder.Stage kappa}
    (hchosen : L.chosen a = some p)
    (hgrounded : p.initial ∈ Gamma.source) :
    Disjoint p.support
      (FiniteExchangeInput (L := L) (hL := hL)).targetMarkers := by
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  rw [Set.disjoint_left]
  intro y hyp hyTarget
  obtain ⟨q, hqEssential, hyq⟩ := hyTarget.2
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
    (hL.legal.warpStages (Ladder.finalStage kappa)) hqEssential
    ⟨y, hyp, hyq⟩) hpInessential

/-- Every grounded-auxiliary target marker is the initial vertex of its
unique limiting-ladder component. -/
theorem splitGrounded_targetMarker_mem_initialSet_limitWarp
    {y : V}
    (hy : y ∈ (FiniteExchangeInput (L := L) (hL := hL)).targetMarkers) :
    y ∈ Gamma.initialSet L.limitWarp := by
  obtain ⟨p, hpEssential, hyp⟩ := hy.2
  obtain ⟨a, ha⟩ := hy.1
  have htrivialSuccessor : Gamma.trivialPath y ∈ L.successorWarp a :=
    (hL.legal.freshMarkers.2 a y ha).2
  let b : Ladder.Stage kappa :=
    ⟨a.1 + 1, by
      have hone : #(PUnit) < kappa := by
        simpa only [mk_punit] using
          (lt_trans Cardinal.one_lt_aleph0 hL.legal.uncountable)
      have hbound := Stationary.iSup_add_one_lt_ord_of_lt
        hL.legal.regular (f := fun _ : PUnit ↦ a.1) hone (fun _ ↦ a.2)
      exact lt_of_le_of_lt
        (Ordinal.le_iSup (fun _ : PUnit ↦ a.1 + 1) PUnit.unit) hbound⟩
  have htrivialStage : Gamma.trivialPath y ∈
      L.warpAt b := by
    exact htrivialSuccessor
  have hmeet : ((Gamma.trivialPath y).support ∩ p.support).Nonempty :=
    ⟨y, by simp, hyp⟩
  have hext : Gamma.Extends (Gamma.trivialPath y) p :=
    hL.legal.extends_limitWarp_of_stage_intersects
      htrivialStage hpEssential.1 hmeet
  have hpInitial : p.initial = y := by
    simpa using (Gamma.extends_initial hext).symm
  exact ⟨p, hpEssential.1, hpInitial⟩

/-- The exact private finite exchange attached to the residual terminal
case.  Besides the private auxiliary path it exposes every endpoint fact
needed to insert this trace in the global terminal-contact switch. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_private_finite_exchange
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (P : (FiniteExchangeInput (L := L) (hL := hL)).Fragment)
        (q : FinitePath
          (FiniteExchangeInput (L := L) (hL := hL)).lambda.graph)
        (Q : Alternating.FiniteTrace Gamma.graph) (y : V),
      P ∈ GroundingCut.G0
          (FiniteExchangeInput (L := L) (hL := hL)) S.cut ∧
      P.path.terminal? = some O.later ∧
      q.start = .old O.later ∧
      q.finish ∈ (FiniteExchangeInput (L := L) (hL := hL)).lambda.target ∧
      (FiniteExchangeInput (L := L) (hL := hL)).lambda.Avoids q
        (S.cut \ {(.old O.later :
          (FiniteExchangeInput (L := L) (hL := hL)).LV)}) ∧
      q.support ∩ S.cut =
        {(.old O.later :
          (FiniteExchangeInput (L := L) (hL := hL)).LV)} ∧
      q.support ∩
        (FiniteExchangeInput (L := L) (hL := hL)).lambda.target ⊆
          {q.finish} ∧
      (Alternating.AltPath.finite Q).initial = O.later ∧
      (Alternating.AltPath.finite Q).terminal? = some y ∧
      y ∈ (FiniteExchangeInput (L := L) (hL := hL)).targetMarkers ∧
      y ∉ P.parent.support ∧
      O.later ∈ Gamma.terminalFrontier L.limitWarp ∧
      y ∈ Gamma.initialSet L.limitWarp ∧
      (∀ z, (y, z) ∉
        (Alternating.AltPath.finite Q).directionEdges .forward) ∧
      Alternating.BackwardLinksOn L.limitWarp (.finite Q) := by
  classical
  obtain ⟨P, hPG0, hblockable, hblocking, hterminal,
      hlaterFinite, hlaterCut⟩ := hcase
  have hblockingNe : GroundingCut.blockingPoint
      (FiniteExchangeInput (L := L) (hL := hL)) S.cut P ≠ O.later := by
    intro heq
    exact O.distinct (hblocking.symm.trans heq)
  have hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (FiniteExchangeInput (L := L) (hL := hL)) S.cut P := by
    rcases hblockable with hescape | hfinite
    · exact hescape
    · by_contra hnoEscape
      exact hblockingNe
        (GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
          (FiniteExchangeInput (L := L) (hL := hL)) S.cut P
          hnoEscape hterminal)
  have hlaterCV : O.later ∈ GroundingCut.CV
      (FiniteExchangeInput (L := L) (hL := hL)) S.cut :=
    GroundingCut.mem_CV.mpr hlaterCut
  obtain ⟨q, A, y, hqStart, hqTarget, hqAvoid, hqPrivate,
      hqPure, hAInitial, hATerminal, hyTarget, hyNoForward, hback⟩ :=
    GroundingFiniteSourceDuplicateExchangeCore.exists_private_decoded_exchange_of_finiteSource_duplicate
      (FiniteExchangeInput (L := L) (hL := hL)) S.cut P hPG0.1
      hterminal hescape hlaterFinite hlaterCV hblockingNe
  have hparentGrounded :=
    L.splitGrounded_fragment_parent_grounded_of_finiteSource_mem_support
      (hL := hL) P hlaterFinite (Gamma.terminal_mem_support hterminal)
  obtain ⟨a, haGround, hchosen⟩ := hparentGrounded
  obtain ⟨parent, hparentChosen, hparentSource⟩ := haGround
  have hparentEq : parent = P.parent :=
    Option.some.inj (hparentChosen.symm.trans hchosen)
  have hdisjoint : Disjoint P.parent.support
      (FiniteExchangeInput (L := L) (hL := hL)).targetMarkers := by
    subst parent
    exact L.splitGrounded_record_support_disjoint_targetMarkers
      hparentChosen hparentSource
  have hyParent : y ∉ P.parent.support := by
    intro hy
    exact Set.disjoint_left.1 hdisjoint hy hyTarget
  have hcy : O.later ≠ y := by
    intro h
    apply hyParent
    exact h ▸ P.support_subset (Gamma.terminal_mem_support hterminal)
  have hlaterFrontier : O.later ∈ Gamma.terminalFrontier L.limitWarp := by
    refine ⟨P.parent, P.parent_mem, ?_⟩
    exact L.splitGrounded_fragment_parent_terminal_of_finiteSource_terminal
      (hL := hL) P hlaterFinite hterminal
  have hyInitial : y ∈ Gamma.initialSet L.limitWarp :=
    L.splitGrounded_targetMarker_mem_initialSet_limitWarp hyTarget
  cases hA : A with
  | trivial x =>
      have hxc : x = O.later := by
        simpa only [hA, Alternating.AltPath.initial_trivial] using hAInitial
      have hxy : x = y := by
        simpa only [hA, Alternating.AltPath.terminal?_trivial,
          Option.some.injEq] using hATerminal
      exact False.elim (hcy (hxc.symm.trans hxy))
  | finite Q =>
      refine ⟨P, q, Q, y, hPG0, hterminal,
        hqStart, hqTarget, hqAvoid, hqPrivate,
        hqPure, ?_, ?_, hyTarget, ?_, hlaterFrontier, hyInitial, ?_, ?_⟩
      · simpa only [hA] using hAInitial
      · simpa only [hA] using hATerminal
      · simpa only using hyParent
      · simpa only [hA] using hyNoForward
      · simpa only [hA, FiniteExchangeInput,
          splitGroundedPopularAuxiliaryInput] using hback
  | infinite r =>
      have : (none : Option V) = some y := by
        simpa only [hA, Alternating.AltPath.terminal?_infinite] using hATerminal
      cases this

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_private_finite_exchange

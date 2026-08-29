/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryDeparture
import ErdosProblems.Erdos599.GroundingTerminalFragment

/-!
# Eliminating the coarse blocking-to-finite boundary case

If the first-hit path from a blocker to a finite old source is residual,
fragment confinement and split-legal warp disjointness show that the later
source is the terminal of the displayed blocking fragment.  Otherwise the
first selected edge has a named active owner and leaves exactly at the
blocker.  Thus the raw blocking-to-finite owner pair is eliminated in favor
of these two source-level alternatives.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedFiniteInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedFiniteIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Exact terminal-incidence data behind a residual blocking-to-finite
collision. -/
def SplitGroundedBlockingFiniteTerminalCase
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) : Prop :=
  ∃ P : (GroundedFiniteInput (L := L) (hL := hL)).Fragment,
    P ∈ GroundingCut.G0
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut ∧
    GroundingCut.IsBlockable
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut P ∧
    GroundingCut.blockingPoint
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut P = O.earlier ∧
    P.path.terminal? = some O.later ∧
    O.later ∈ (GroundedFiniteInput (L := L) (hL := hL)).finiteSource ∧
    PopularAuxiliary.Input.LambdaVertex.old O.later ∈ S.cut

/-- A residual chain from a displayed blocker to a finite source confines
both endpoints to the same limiting-warp component and forces that source
to be the fragment terminal. -/
theorem SplitGroundedPreStoppedBoundaryObstruction.blockingFiniteTerminalCase_of_residual
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R)
    (P : (GroundedFiniteInput (L := L) (hL := hL)).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut P = O.earlier)
    (hlaterFinite : O.later ∈
      (GroundedFiniteInput (L := L) (hL := hL)).finiteSource)
    (hlaterCut : PopularAuxiliary.Input.LambdaVertex.old O.later ∈ S.cut)
    (hresidual : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ residualLadderEdges
        (GroundedFiniteIndexed (L := L) (hL := hL)
          (hground := hground)) S) O.earlier O.later) :
    SplitGroundedBlockingFiniteTerminalCase O := by
  let J := GroundedFiniteInput (L := L) (hL := hL)
  have hlaterFinite' := hlaterFinite
  have hearlierSupport : O.earlier ∈ P.path.support := by
    rw [← hearlier]
    exact GroundingCut.blockingPoint_mem_support J S.cut P hblockable
  have hlaterSupport : O.later ∈ P.path.support :=
    (GroundingFragmentResidualOrder.mem_and_beforeEq_of_reflTransGen_residualLadderEdges
      (GroundedFiniteIndexed (L := L) (hL := hL)
        (hground := hground)) S hPG0.1 hearlierSupport hresidual).1
  obtain ⟨a, _ha, parent, hchosen, hterminal⟩ := hlaterFinite
  cases parent with
  | inl p =>
      have hfinish : p.finish = O.later := Option.some.inj hterminal
      have hpLimit : (.inl p : Gamma.DPath) ∈ L.limitWarp :=
        (L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
          (by
            change a.1 + 1 ≤ kappa.ord
            exact (Order.add_one_le_iff).2 a.2)).1
      have hlaterParent : O.later ∈
          _root_.Erdos599.DirectedPath.Path.support
            (.inl p : Gamma.DPath) := by
        change O.later ∈ p.support
        exact hfinish ▸ p.finish_mem_support
      have hparent : P.parent = (.inl p : Gamma.DPath) := by
        symm
        apply Alternating.DWeb.IsWarp.eq_of_mem_support
          (hL.legal.warpStages (Ladder.finalStage kappa))
          hpLimit P.parent_mem
        · exact hlaterParent
        · exact P.support_subset hlaterSupport
      have hPterminal : P.path.terminal? = some p.finish :=
        (GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
          J S.cut p P hPG0.1 hparent (hfinish ▸ hlaterSupport)).2
      exact ⟨P, hPG0, hblockable, hearlier,
        hPterminal.trans (congrArg some hfinish), hlaterFinite', hlaterCut⟩
  | inr r =>
      change (none : Option V) = some O.later at hterminal
      cases hterminal

/-- The named selected departure alternative at a first-hit blocker. -/
def SplitGroundedSelectedDepartureAtBlocker
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (D : L.SplitGroundedFirstBoundaryReduction R O) : Prop :=
  ∃ (c : ActiveControlRequestAt
      (GroundedFiniteIndexed (L := L) (hL := hL)
        (hground := hground)) S K (∅ : Set V))
      (v : V),
    (D.reduced.earlier, v) ∈
      (selectedErasedCompression
        (GroundedFiniteIndexed (L := L) (hL := hL)
          (hground := hground)) S K
        (chosenRequest c.1)).path.directionEdges .forward ∧
    (D.reduced.earlier, v) ∈ D.path.edgeSet ∧
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
        (GroundedFiniteIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅)
      v D.reduced.later

/-- The coarse blocking-to-finite case is replaced by an exact terminal
collision or a selected active departure at the blocker. -/
theorem SplitGroundedFirstBoundaryReduction.blockingFiniteTerminal_or_selectedDeparture
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (D : L.SplitGroundedFirstBoundaryReduction R O)
    (P : (GroundedFiniteInput (L := L) (hL := hL)).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (GroundedFiniteInput (L := L) (hL := hL)) S.cut P =
        D.reduced.earlier)
    (hlaterFinite : D.reduced.later ∈
      (GroundedFiniteInput (L := L) (hL := hL)).finiteSource)
    (hlaterCut : PopularAuxiliary.Input.LambdaVertex.old
      D.reduced.later ∈ S.cut) :
    SplitGroundedBlockingFiniteTerminalCase D.reduced ∨
      SplitGroundedSelectedDepartureAtBlocker D := by
  rcases D.residual_or_selectedForward_from_blocker
      P hPG0 hblockable hearlier with hresidual | hselected
  · exact Or.inl <|
      D.reduced.blockingFiniteTerminalCase_of_residual
        P hPG0 hblockable hearlier hlaterFinite hlaterCut hresidual
  · exact Or.inr hselected

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFirstBoundaryReduction.blockingFiniteTerminal_or_selectedDeparture

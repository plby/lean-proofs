/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentResidualOrder
import ErdosProblems.Erdos599.GroundingPreStoppedBoundaryCollisionCases
import ErdosProblems.Erdos599.GroundingTerminalFragment

/-!
# Residual blocking--finite boundary collisions

An arbitrary pre-stopped switched chain can use selected-route edges, so its
endpoints alone do not identify a common ladder fragment.  If the displayed
ordered collision is carried entirely by residual ladder edges, however,
fragment confinement supplies exactly the missing terminal-incidence fact.
The later finite source determines a grounded finite parent; warp
disjointness identifies it with the earlier blocking fragment's parent, and
the terminal-fragment lemma fixes the fragment terminal.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder
namespace Assertion822PreStoppedBoundaryObstruction

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A finite chain in a relation contained in `residual ∪ forward` either
uses residual edges only or displays a particular forward edge together
with the relation prefixes on both sides. -/
theorem reflTransGen_residual_or_exists_forward
    {E residual forward : Set (V × V)} {a b : V}
    (hsub : E ⊆ residual ∪ forward)
    (hab : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ residual) a b ∨
      ∃ u v,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ residual) a u ∧
        (u, v) ∈ forward ∧
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) v b := by
  induction hab using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Or.inl .refl
  | single hab =>
      rcases hsub hab with hresidual | hforward
      · exact Or.inl (.single hresidual)
      · exact Or.inr ⟨_, _, .refl, hforward, .refl⟩
  | trans hab hbc ihab ihbc =>
      rcases ihab with habResidual | ⟨u, v, hau, huv, hvb⟩
      · rcases ihbc with hbcResidual | ⟨u, v, hbu, huv, hvc⟩
        · exact Or.inl (habResidual.trans hbcResidual)
        · exact Or.inr ⟨u, v, habResidual.trans hbu, huv, hvc⟩
      · exact Or.inr ⟨u, v, hau, huv, hvb.trans hbc⟩

/-- Every ordered collision in the reserved pre-stopped switch is either a
residual-ladder chain or contains a displayed selected forward edge. -/
theorem residual_reach_or_exists_selected_forward
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S) o.earlier o.later ∨
      ∃ u v,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ residualLadderEdges
            (L.popularAuxiliaryIndexed hL) S)
          o.earlier u ∧
        (u, v) ∈ erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (∅ : Set V) .forward ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          v o.later := by
  apply reflTransGen_residual_or_exists_forward
    (E := L.assertion822ReservedPreStoppedEdges hL S R)
    (residual := residualLadderEdges (L.popularAuxiliaryIndexed hL) S)
    (forward := erasedSelectedDirectionEdgesAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) ∅ .forward)
  · intro e he
    change e ∈ erasedSelectedSwitchedEdgesAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) ∅ at he
    rw [erasedSelectedSwitchedEdgesAt_empty_eq] at he
    rcases he with ⟨heResidual, _heNotCut⟩ | heForward
    · exact Or.inl heResidual
    · exact Or.inr heForward
  · exact o.reaches

/-- Owner-refined form of `residual_reach_or_exists_selected_forward`.
The nonresidual branch names the active control and the exact forward edge
of its selected compressed route. -/
theorem residual_reach_or_exists_selected_forward_owner
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S) o.earlier o.later ∨
      ∃ (c : ActiveControlRequestAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (∅ : Set V))
          (u v : V),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ residualLadderEdges
            (L.popularAuxiliaryIndexed hL) S)
          o.earlier u ∧
        (u, v) ∈ (selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest c.1)).path.directionEdges .forward ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          v o.later := by
  rcases residual_reach_or_exists_selected_forward o with
    hresidual | ⟨u, v, heu, huv, hvl⟩
  · exact Or.inl hresidual
  · right
    simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at huv
    obtain ⟨c, huv⟩ := huv
    exact ⟨c, u, v, heu, huv, hvl⟩

/-- A residual-ladder chain from a displayed blocking point to a finite
source forces the latter to be the terminal of the same fragment. -/
theorem blockingFiniteTerminalCase_of_residual_reach
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (L.popularAuxiliaryInput hL.legal) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier)
    (hlater : FiniteCase hL S o.later)
    (hresidual : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ residualLadderEdges
        (L.popularAuxiliaryIndexed hL) S) o.earlier o.later) :
    BlockingFiniteTerminalCase o := by
  let J := L.popularAuxiliaryInput hL.legal
  have hearlierSupport : o.earlier ∈ P.path.support := by
    rw [← hearlier]
    exact GroundingCut.blockingPoint_mem_support J S.cut P
  have hlaterSupport : o.later ∈ P.path.support :=
    (GroundingFragmentResidualOrder.mem_and_beforeEq_of_reflTransGen_residualLadderEdges
      (L.popularAuxiliaryIndexed hL) S hPG0.1 hearlierSupport
        hresidual).1
  have hlaterGrounded : o.later ∈ L.groundedFiniteTerminalSet := by
    exact hlater.1
  obtain ⟨a, ha, parent, hchosen, hterminal⟩ := hlaterGrounded
  cases parent with
  | inl p =>
      have hfinish : p.finish = o.later := by
        exact Option.some.inj hterminal
      have hpRecord : (.inl p : Gamma.DPath) ∈ J.groundedRecords :=
        ⟨a, ha.1, hchosen⟩
      have hpLimit : (.inl p : Gamma.DPath) ∈ L.limitWarp :=
        (L.groundedRecord_mem_inessentialPaths_limitWarp
          hL.legal hpRecord).1
      have hlaterParent : o.later ∈
          _root_.Erdos599.DirectedPath.Path.support
            (.inl p : Gamma.DPath) := by
        change o.later ∈ p.support
        exact hfinish ▸ p.finish_mem_support
      have hPParentLimit : P.parent ∈ L.limitWarp := P.parent_mem
      have hparent : P.parent = (.inl p : Gamma.DPath) := by
        symm
        apply Alternating.DWeb.IsWarp.eq_of_mem_support
          (hL.legal.warpStages (Ladder.finalStage kappa))
          hpLimit hPParentLimit
        · exact hlaterParent
        · exact P.support_subset hlaterSupport
      have hPterminal : P.path.terminal? = some p.finish :=
        (GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
          J S.cut p P hPG0.1 hparent
            (hfinish ▸ hlaterSupport)).2
      refine ⟨P, hPG0, hblockable, hearlier, ?_, hlater⟩
      exact hPterminal.trans (congrArg some hfinish)
  | inr r =>
      change (none : Option V) = some o.later at hterminal
      cases hterminal

/-- Consequently, a residual blocking--finite collision has the canonical
private decoded exchange path. -/
theorem exists_private_decoded_exchange_of_residual_blocking_finite
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (L.popularAuxiliaryInput hL.legal) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier)
    (hlater : FiniteCase hL S o.later)
    (hresidual : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ residualLadderEdges
        (L.popularAuxiliaryIndexed hL) S) o.earlier o.later) :
    ∃ (q : _root_.Erdos599.DirectedPath.FinitePath
          (L.popularAuxiliaryInput hL.legal).lambda.graph)
        (A : Alternating.AltPath Gamma.graph) (y : V),
      q.start = .old o.later ∧
      q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
      (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
        (S.cut \ {(.old o.later :
          (L.popularAuxiliaryInput hL.legal).LV)}) ∧
      q.support ∩ S.cut =
        {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} ∧
      A.initial = o.later ∧ A.terminal? = some y ∧
      y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
      Alternating.BackwardLinksOn
        (L.popularAuxiliaryInput hL.legal).ladder.paths A := by
  apply exists_private_decoded_exchange_of_blocking_finite_terminal o
  exact blockingFiniteTerminalCase_of_residual_reach o P hPG0 hblockable
    hearlier hlater hresidual

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.blockingFiniteTerminalCase_of_residual_reach
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.exists_private_decoded_exchange_of_residual_blocking_finite

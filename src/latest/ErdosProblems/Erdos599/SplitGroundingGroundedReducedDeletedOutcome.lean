/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedLastContact
import ErdosProblems.Erdos599.SplitGroundingGroundedReservedControls

/-!
# Concrete deleted-edge outcomes at the reduced grounding frontier

The reduced root normalizer classifies a last missing ladder edge as a
selected backward edge, a forward-incidence conflict, or an edge whose tail
is already in the final frontier.  The forward-conflict case still used to
hide the route which performs the exchange.  The last-contact theorem
extracts that route at the *same* stopping frontier.

This file composes the two results.  Its output is the exact local input for
the remaining boundary transfer: a backward selected owner, a normalized
last-contact suffix, or a literal departure from the chosen frontier `T`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ReducedOutcomeIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ReducedOutcomeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ReducedOutcomeEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (ReducedOutcomeIndexed (L := L) (hL := hL) (hground := hground)) S K T

/-- A limiting-ladder parent supporting a selected backward link is exposed
by that selected request, uniformly at the actual stopping frontier. -/
theorem splitGroundedBackwardLink_parent_exposedAt
    (T : Set V)
    (owner : ActiveControlRequestAt
      (ReducedOutcomeIndexed (L := L) (hL := hL)
        (hground := hground)) S K T)
    (link : Alternating.Link Gamma.graph)
    (hlink : link ∈ (selectedErasedCompression
      (ReducedOutcomeIndexed (L := L) (hL := hL)
        (hground := hground)) S K (chosenRequest owner.1)).path.links)
    (hdir : link.direction = .backward)
    (parent : Gamma.DPath)
    (hparent : parent ∈
      (ReducedOutcomeInput (L := L) (hL := hL)).ladder.paths)
    (hsub : link.path.IsSubpathOf parent) :
    parent ∈ exposedLadderPaths
      (ReducedOutcomeInput (L := L) (hL := hL))
      (strongSelectedPath
        (ReducedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S K (chosenRequest owner.1)) := by
  have hnonempty : link.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        link.path link.path.start_mem_support link.nontrivial
    exact ⟨(link.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈ (selectedErasedCompression
      (ReducedOutcomeIndexed (L := L) (hL := hL)
        (hground := hground)) S K
      (chosenRequest owner.1)).path.directionEdges .backward := by
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨link, hlink, hdir, heLink⟩
  have hePath := (selectedBackwardEdge_auxContact_offApex_split
    (ReducedOutcomeIndexed (L := L) (hL := hL)
      (hground := hground)) S K (chosenRequest owner.1) heDirection).1
  left
  exact ⟨hparent, PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2,
    hePath, Or.inr ⟨e, hsub.2 heLink, rfl⟩⟩

/-- Fully concrete form of one deleted incoming edge in the reduced
frontier normalizer.  In the forward-conflict case the selected owner and
the normalized final-contact suffix have already been chosen. -/
inductive SplitGroundedReducedDeletedOutcomeAt
    (T : Set V) (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (ReducedOutcomeEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T)) : Prop
  | backward
      (tail : V)
      (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (selected_backward : (tail, D.head) ∈
        erasedSelectedDirectionEdgesAt
          (ReducedOutcomeIndexed (L := L) (hL := hL)
            (hground := hground)) S K T .backward)
      (owner : ActiveControlRequestAt
        (ReducedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S K T)
      (link : Alternating.Link Gamma.graph)
      (link_mem : link ∈ (selectedErasedCompression
        (ReducedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S K (chosenRequest owner.1)).path.links)
      (link_direction : link.direction = .backward)
      (edge_mem_link : (tail, D.head) ∈ link.path.edgeSet)
      (link_subpath : link.path.IsSubpathOf parent)
      (parent_exposed : parent ∈ exposedLadderPaths
        (ReducedOutcomeInput (L := L) (hL := hL))
        (strongSelectedPath
          (ReducedOutcomeIndexed (L := L) (hL := hL)
            (hground := hground)) S K (chosenRequest owner.1)))
  | forwardLastContact
      (data : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T parent p D)
  | boundaryDeparture
      (tail : V)
      (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (residual : (tail, D.head) ∈ residualLadderEdges
        (ReducedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S)
      (tail_mem : tail ∈ T)

/-- Compose the reduced deletion classifier with the `T`-parametric final
contact theorem. -/
theorem splitGroundedReducedDeletedOutcomeAt
    (T : Set V) (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (hparent : parent ∈
      (ReducedOutcomeInput (L := L) (hL := hL)).ladder.paths)
    (hpParent : p.support ⊆ parent.support)
    (hpEdges : p.edgeSet ⊆ parent.edgeSet)
    (D : LastDeletedHead p
      (ReducedOutcomeEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T))
    (hclass : SplitGroundedReducedDeletedClassAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T p D) :
    SplitGroundedReducedDeletedOutcomeAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D := by
  rcases hclass with hbackward | hconflict | hboundary
  · obtain ⟨u, hu, hbackward⟩ := hbackward
    have hselected := hbackward
    simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at hbackward
    obtain ⟨owner, howner⟩ := hbackward
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at howner
    obtain ⟨link, hlink, hdir, heLink⟩ := howner
    obtain ⟨ownerParent, hownerParent, hsub⟩ :=
      selectedErasedCompression_backwardLinksOn
        (ReducedOutcomeIndexed (L := L) (hL := hL)
          (hground := hground)) S K (chosenRequest owner.1)
            link hlink hdir
    have heParent : (u, D.head) ∈ parent.edgeSet := hpEdges hu
    have heOwnerParent : (u, D.head) ∈ ownerParent.edgeSet :=
      hsub.2 heLink
    have hownerEq : ownerParent = parent :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (ReducedOutcomeInput (L := L) (hL := hL)).ladder.disjoint
        hownerParent hparent
        (ownerParent.edgeSet_subset_support_prod heOwnerParent).1
        (parent.edgeSet_subset_support_prod heParent).1
    have hsubParent : link.path.IsSubpathOf parent := by
      simpa only [hownerEq] using hsub
    exact .backward u hu hselected owner link hlink hdir heLink hsubParent
      (L.splitGroundedBackwardLink_parent_exposedAt T owner link hlink hdir
        parent hparent hsubParent)
  · obtain ⟨u, hu, hconflict⟩ := hconflict
    exact .forwardLastContact
      (L.exists_splitGroundedReducedForwardConflictSpliceData
        T parent hpParent D u hu hconflict).some
  · obtain ⟨u, hu, hresidual, huT⟩ := hboundary
    exact .boundaryDeparture u hu hresidual huT

namespace SplitGroundedUnusedRecord

/-- The finite-source failure produced by the reduced normalizer already
has one of the three concrete outcomes above. -/
theorem SplitGroundedReducedFiniteSourceRootFailureAt.deletedOutcome
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {T : Set V} {b : V}
    {hb : b ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).finiteSource}
    (F : SplitGroundedReducedFiniteSourceRootFailureAt R T b hb) :
    SplitGroundedReducedDeletedOutcomeAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T (.inl F.parent : Gamma.DPath) F.parent F.lastDeleted := by
  apply L.splitGroundedReducedDeletedOutcomeAt T
    (.inl F.parent : Gamma.DPath) F.parent
  · exact F.parent_inessential.1
  · intro x hx
    change x ∈ F.parent.support
    exact hx
  · intro e he
    change e ∈ F.parent.edgeSet
    exact he
  · exact F.deleted_class

/-- The blocking-point normal form with its deleted constructor refined to
the concrete three-way outcome.  The four first-fragment constructors are
unchanged: they are genuine source-side leaves, not disguised deletion
cases. -/
inductive SplitGroundedReducedBlockingRootFailureRefinedAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (ReducedOutcomeInput (L := L) (hL := hL)).Fragment) : Prop
  | reservedEscape
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (ReducedOutcomeInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedOutcomeEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | reservedTerminal
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (terminal : V) (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ P.MeetsEscape
        (ReducedOutcomeInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedOutcomeEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | hangingEscape
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (ReducedOutcomeInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedOutcomeEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | hangingTerminal
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (terminal : V) (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ P.MeetsEscape
        (ReducedOutcomeInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedOutcomeEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | deleted
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint
        (ReducedOutcomeInput (L := L) (hL := hL)) S.cut P)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (ReducedOutcomeEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedOutcomeEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a lastDeleted.head)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T P.parent segment lastDeleted)

/-- Refine the forward-conflict constructor of the produced blocking
failure to an actual final-contact suffix. -/
theorem SplitGroundedReducedBlockingRootFailureAt.refineDeleted
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {T : Set V}
    {P : (ReducedOutcomeInput (L := L) (hL := hL)).Fragment}
    (F : SplitGroundedReducedBlockingRootFailureAt R T P) :
    SplitGroundedReducedBlockingRootFailureRefinedAt R T P := by
  cases F with
  | reservedEscape heq hinitial hescape hnot =>
      exact .reservedEscape heq hinitial hescape hnot
  | reservedTerminal heq hinitial terminal hterminal hescape hnot =>
      exact .reservedTerminal heq hinitial terminal hterminal hescape hnot
  | hangingEscape hhang hinitial hescape hnot =>
      exact .hangingEscape hhang hinitial hescape hnot
  | hangingTerminal hhang hinitial terminal hterminal hescape hnot =>
      exact .hangingTerminal hhang hinitial terminal hterminal hescape hnot
  | deleted segment hstart hfinish hsupport hedges D hnot hclass =>
      exact .deleted segment hstart hfinish hsupport hedges D hnot
        (L.splitGroundedReducedDeletedOutcomeAt T P.parent segment
          P.parent_mem (hsupport.trans P.support_subset)
            (hedges.trans P.edges_subset) D hclass)

/-- Top-level reduced boundary failure after all forward conflicts have
been replaced by concrete final-contact suffixes. -/
inductive SplitGroundedReducedBBRootFailureRefinedAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (t : V) : Prop
  | finite
      (ht : t ∈ (ReducedOutcomeInput (L := L) (hL := hL)).finiteSource)
      (data : SplitGroundedReducedFiniteSourceRootFailureAt R T t ht)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T (.inl data.parent : Gamma.DPath) data.parent data.lastDeleted)
  | blocking
      (P : (ReducedOutcomeInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (ReducedOutcomeInput (L := L) (hL := hL)) S.cut P = t)
      (data : SplitGroundedReducedBlockingRootFailureRefinedAt R T P)

/-- Refine every forward-conflict leaf in one top-level reduced boundary
failure. -/
theorem SplitGroundedReducedBBRootFailureAt.refineDeleted
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {T : Set V} {t : V}
    (F : SplitGroundedReducedBBRootFailureAt R T t) :
    SplitGroundedReducedBBRootFailureRefinedAt R T t := by
  cases F with
  | finite ht data => exact .finite ht data data.deletedOutcome
  | blocking P hP heq data =>
      exact .blocking P hP heq data.refineDeleted

end SplitGroundedUnusedRecord
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedReducedDeletedOutcomeAt
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.SplitGroundedReducedFiniteSourceRootFailureAt.deletedOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.SplitGroundedReducedBBRootFailureAt.refineDeleted

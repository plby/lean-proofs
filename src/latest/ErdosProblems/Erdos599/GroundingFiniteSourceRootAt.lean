/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceRoot

/-!
# Finite-source rooting for a chosen stopping frontier

The minimal-frontier version of Assertion 8.22 stops the simultaneous
switch at an arbitrary set `T`, rather than at the whole preliminary
boundary `BB`.  This file gives the exact `T`-parametric counterparts of
the finite-source deleted-edge classification and root-splicing lemmas.

No deleted head is asserted to be rooted here.  The public reductions keep
that genuine geometric obligation explicit, while discharging the finite
parent, allowed-root, and surviving-suffix bookkeeping.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Exact reason a ladder-family edge can be absent from the switch stopped
at `T`: a represented cut edge, a selected backward edge, a forward
connector conflict, or a residual departure from `T`. -/
theorem familyEdge_deleted_classificationAt
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (T : Set V)
    {e : V × V} (heFamily : e ∈ J.familyEdges)
    (heDeleted : e ∉
      GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T) :
    e ∈ GroundingCut.CE J S.cut ∨
      e ∈ GroundingErasedDecode.erasedSelectedDirectionEdgesAt
        U S K T .backward ∨
      e ∈ GroundingErasedDecode.forwardConflictCutEdgesAt U S K T ∨
      e ∈ GroundingErasedDecode.boundaryOutgoingCutEdgesAt U S T := by
  by_cases heCut : e ∈ GroundingCut.CE J S.cut
  · exact Or.inl heCut
  · have heResidual : e ∈
        GroundingErasedDecode.residualLadderEdges U S :=
      ⟨heFamily, heCut⟩
    have heToggle : e ∈
        GroundingErasedDecode.erasedSelectedToggleEdgesAt U S K T := by
      by_contra heNotToggle
      exact heDeleted (Or.inl ⟨heResidual, heNotToggle⟩)
    rcases heToggle with heBackward | heConflict | heBoundary
    · exact Or.inr (Or.inl heBackward)
    · exact Or.inr (Or.inr (Or.inl heConflict))
    · exact Or.inr (Or.inr (Or.inr heBoundary))

/-- Classify the incoming edge of a last deleted head for the switch
stopped at `T`. -/
theorem LastDeletedHead.exists_classified_deletedIncomingAt
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (T : Set V)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)) :
    ∃ u, (u, D.head) ∈ p.edgeSet ∧
      ((u, D.head) ∈ GroundingCut.CE J S.cut ∨
        (u, D.head) ∈
          GroundingErasedDecode.erasedSelectedDirectionEdgesAt
            U S K T .backward ∨
        (u, D.head) ∈
          GroundingErasedDecode.forwardConflictCutEdgesAt U S K T ∨
        (u, D.head) ∈
          GroundingErasedDecode.boundaryOutgoingCutEdgesAt U S T) := by
  obtain ⟨u, huParent, huDeleted⟩ := D.deleted_incoming
  exact ⟨u, huParent,
    familyEdge_deleted_classificationAt K T
      (hpFamily huParent) huDeleted⟩

/-- Split form of the last-deleted-edge classification.  The fourth branch
is exposed as a residual edge whose tail lies in the chosen frontier `T`. -/
theorem LastDeletedHead.exists_classified_deletedIncomingAt_split
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (T : Set V)
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE J S.cut) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K T .backward) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K T) ∨
    (∃ u : V,
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.residualLadderEdges U S ∧
      u ∈ T) := by
  obtain ⟨u, huParent, huCut | huBackward | huConflict | huBoundary⟩ :=
    D.exists_classified_deletedIncomingAt K T hpFamily
  · exact Or.inl ⟨u, huParent, huCut⟩
  · exact Or.inr (Or.inl ⟨u, huParent, huBackward⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨u, huParent, huConflict⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨u, huParent, huBoundary.1, huBoundary.2⟩))

/-- Root a finite ladder-family prefix by repairing only the final deleted
head.  The four callbacks are exactly the four switch-specific deletion
classes; after one callback the bundled suffix is already contained in the
`T`-stopped relation. -/
theorem exists_root_reaching_finishAt_of_lastDeletedHead_cases
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) (T : Set V) (A : Set V)
    (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
    (hpFamily : p.edgeSet ⊆ J.familyEdges)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a p.start)
    (hCE : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈ GroundingCut.CE J S.cut →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a D.head)
    (hbackward : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          U S K T .backward →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a D.head)
    (hconflict : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt U S K T →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a D.head)
    (hboundary : ∀ (D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)) u,
      (u, D.head) ∈ p.edgeSet →
      (u, D.head) ∈ GroundingErasedDecode.residualLadderEdges U S →
      u ∈ T →
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
        a D.head) :
    ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        GroundingErasedDecode.erasedSelectedSwitchedEdgesAt U S K T)
      a p.finish := by
  apply exists_root_reaching_finish_of_lastDeletedHead p hstart
  intro D
  rcases D.exists_classified_deletedIncomingAt_split K T hpFamily with
      ⟨u, huParent, huCE⟩ |
      ⟨u, huParent, huBackward⟩ |
      ⟨u, huParent, huConflict⟩ |
      ⟨u, huParent, huResidual, huT⟩
  · exact hCE D u huParent huCE
  · exact hbackward D u huParent huBackward
  · exact hconflict D u huParent huConflict
  · exact hboundary D u huParent huResidual huT

/-- Recorded finite-parent specialization of the `T`-parametric split
classification, for arbitrary selection controls `K`. -/
theorem classified_lastDeletedHead_of_recorded_finiteParentAt
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (K : GroundingSelection.Controls S) (T : Set V)
    {a : Ladder.Stage kappa}
    {p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph}
    (hchosen : L.chosen a = some (.inl p : Gamma.DPath))
    (D : LastDeletedHead p
      (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
        (L.popularAuxiliaryIndexed hL) S K T)) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T .backward) ∨
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T) ∨
    (∃ u : V,
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈
        GroundingErasedDecode.residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S ∧
      u ∈ T) := by
  have hpLimit : (.inl p : Gamma.DPath) ∈ L.limitWarp :=
    (L.recorded_mem_limitWarp_inessential_sourceGeometry
      hL.legal hchosen).1
  have hpFamily : p.edgeSet ⊆
      (L.popularAuxiliaryInput hL.legal).familyEdges := by
    intro e he
    exact ⟨(.inl p : Gamma.DPath), hpLimit, he⟩
  exact D.exists_classified_deletedIncomingAt_split K T hpFamily

/-- Finite-source root splice for arbitrary controls and stopping frontier.
It is enough to root the head of every deleted canonical-parent edge. -/
theorem UnusedGroundedRecord.exists_cutFiniteSource_rootedAt_of_deleted_heads
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S) (T : Set V)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hrepair : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      ∀ e ∈ p.edgeSet,
        e ∉ GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
                (L.popularAuxiliaryIndexed hL) S K T) a e.2) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K T) a b := by
  obtain ⟨p, hchosen, hfinish, hsource, _hlimit, hroot⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hb hbCut
  let E := GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
    (L.popularAuxiliaryIndexed hL) S K T
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start := by
    refine ⟨p.start, ⟨hsource, ?_⟩, .refl⟩
    simpa only [Set.mem_singleton_iff] using hroot.symm
  obtain ⟨a, ha, hab⟩ :=
    exists_root_reaching_finish_of_deleted_heads_reachable p hstart
      (hrepair p hchosen)
  exact ⟨a, ha, hfinish ▸ hab⟩

/-- Minimal finite-source root splice for arbitrary controls and frontier.
Only the final deleted head must be rerooted; its suffix already lies in the
`T`-stopped relation. -/
theorem UnusedGroundedRecord.exists_cutFiniteSource_rootedAt_of_lastDeletedHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (K : GroundingSelection.Controls S) (T : Set V)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hrepair : ∀
      (p : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      ∀ D : LastDeletedHead p
        (GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
          (L.popularAuxiliaryIndexed hL) S K T),
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
                (L.popularAuxiliaryIndexed hL) S K T) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
            (L.popularAuxiliaryIndexed hL) S K T) a b := by
  obtain ⟨p, hchosen, hfinish, hsource, _hlimit, hroot⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hb hbCut
  let E := GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
    (L.popularAuxiliaryIndexed hL) S K T
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start := by
    refine ⟨p.start, ⟨hsource, ?_⟩, .refl⟩
    simpa only [Set.mem_singleton_iff] using hroot.symm
  obtain ⟨a, ha, hab⟩ :=
    exists_root_reaching_finish_of_lastDeletedHead p hstart
      (hrepair p hchosen)
  exact ⟨a, ha, hfinish ▸ hab⟩

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.familyEdge_deleted_classificationAt
#print axioms Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.exists_cutFiniteSource_rootedAt_of_lastDeletedHead

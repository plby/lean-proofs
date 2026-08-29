/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRootTransfer
import ErdosProblems.Erdos599.GroundingBBGeometry
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Grounded split boundary root reductions

These reductions are uniform in the control package.  In particular they
can be instantiated after the unused record has been reserved and the
controls have been refined to avoid it.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedRootInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedRootIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

namespace SplitGroundedUnusedRecord

private theorem exists_unrootedLastDeletedHead_split
    {E : Set (V × V)} {A : Set V}
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish) :
    ∃ D : LastDeletedHead p E,
      ¬ ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet, e ∉ E := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hastart⟩ := hstart
    refine ⟨a, ha, hastart.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      by_contra hxyE
      exact hnone ⟨(x, y), hxy, hxyE⟩
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet p.walk
  let D := (exists_lastDeletedHead p hdeleted).some
  refine ⟨D, ?_⟩
  rintro ⟨a, ha, haD⟩
  apply hfinish
  refine ⟨a, ha, haD.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet
        D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

/-- Positive finite-parent data behind a finite old source which is not
rooted in the pre-stopped relation.  Rooted controls eliminate the `CE`
case, so the displayed last deletion is genuinely selected-backward or a
forward conflict. -/
structure SplitGroundedFiniteSourceRootFailureOutcome
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (b : V)
    (hb : b ∈ (GroundedRootInput (L := L) (hL := hL)).finiteSource) where
  parent : FinitePath Gamma.graph
  chosen : L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
    some (.inl parent : Gamma.DPath)
  parent_finish : parent.finish = b
  parent_start : parent.start ∈ Gamma.source \ {R.record.initial}
  parent_inessential : (.inl parent : Gamma.DPath) ∈
    Gamma.inessentialPaths L.limitWarp
  lastDeleted : LastDeletedHead parent
    (erasedSelectedSwitchedEdgesAt
      (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
        S K ∅)
  head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
        (GroundedRootIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅) a lastDeleted.head
  deleted_class :
    (∃ u, (u, lastDeleted.head) ∈ parent.edgeSet ∧
      (u, lastDeleted.head) ∈ erasedSelectedDirectionEdgesAt
        (GroundedRootIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅ .backward) ∨
    (∃ u, (u, lastDeleted.head) ∈ parent.edgeSet ∧
      (u, lastDeleted.head) ∈ forwardConflictCutEdgesAt
        (GroundedRootIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅)

/-- Construct the exact finite-source failure data. -/
theorem finiteSourceRootFailureOutcome
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (GroundedRootInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a b)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1) :
    Nonempty (SplitGroundedFiniteSourceRootFailureOutcome R b hb) := by
  obtain ⟨p, hchosen, hfinish, hstart, hparent⟩ :=
    R.exists_cutFiniteSource_parent_with_allowed_root hb hbCut
  have hpRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a p.start := ⟨p.start, hstart, .refl⟩
  have hpNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a p.finish := by
    simpa only [hfinish] using hnot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead_split p hpRoot hpNot
  have hpFamily : p.edgeSet ⊆
      (GroundedRootInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨(.inl p : Gamma.DPath), hparent.1, he⟩
  have hclass :
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL)
            (hground := hground)) S K ∅ .backward) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL)
            (hground := hground)) S K ∅) := by
    rcases D.exists_classified_deletedIncomingAt_split K ∅ hpFamily with
        hCE | hbackward | hconflict | ⟨u, _huParent, _huResidual, huEmpty⟩
    · obtain ⟨u, _huPath, huCE⟩ := hCE
      exfalso
      apply hDnot
      let s : Request
          (GroundedRootInput (L := L) (hL := hL)) S.cut :=
        .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
      let c : ControlRequest
          (GroundedRootInput (L := L) (hL := hL)) S.cut :=
        ⟨D.head, ⟨s, rfl⟩⟩
      exact hcontrol c
    · exact Or.inl hbackward
    · exact Or.inr hconflict
    · simp only [Set.mem_empty_iff_false] at huEmpty
  exact ⟨{
    parent := p
    chosen := hchosen
    parent_finish := hfinish
    parent_start := hstart
    parent_inessential := hparent
    lastDeleted := D
    head_not_rooted := hDnot
    deleted_class := hclass }⟩

/-- Before stopping at the preliminary boundary, a represented cut edge is
already handled by the rooted control request at its head.  Thus only the
backward-selection and forward-conflict cases remain as genuine callbacks
for a finite old source. -/
theorem cutFiniteSource_rootedPreStopped_of_lastDeletedHead_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (GroundedRootInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1)
    (hbackward : ∀ (p : FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      p.start ∈ Gamma.source \ {R.record.initial} →
      (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp →
      ∀ (D : LastDeletedHead p (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅)) u,
        (u, D.head) ∈ p.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅ .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K ∅) a D.head)
    (hconflict : ∀ (p : FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      p.start ∈ Gamma.source \ {R.record.initial} →
      (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp →
      ∀ (D : LastDeletedHead p (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅)) u,
        (u, D.head) ∈ p.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅ →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K ∅) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a b := by
  obtain ⟨p, hchosen, hfinish, hstart, hparent⟩ :=
    R.exists_cutFiniteSource_parent_with_allowed_root hb hbCut
  have hpFamily : p.edgeSet ⊆
      (GroundedRootInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨(.inl p : Gamma.DPath), hparent.1, he⟩
  have hrootStart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a p.start := ⟨p.start, hstart, .refl⟩
  obtain ⟨a, ha, hareach⟩ :=
    exists_root_reaching_finishAt_of_lastDeletedHead_cases K ∅
      (Gamma.source \ {R.record.initial}) p hpFamily hrootStart
      (by
        intro D u hu huCE
        let r : Request (GroundedRootInput (L := L) (hL := hL)) S.cut :=
          .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
        let c : ControlRequest
            (GroundedRootInput (L := L) (hL := hL)) S.cut :=
          ⟨D.head, ⟨r, rfl⟩⟩
        exact hcontrol c)
      (hbackward p hchosen hstart hparent)
      (hconflict p hchosen hstart hparent)
      (by
        intro _D u _hu _hresidual huEmpty
        simp only [Set.mem_empty_iff_false] at huEmpty)
  exact ⟨a, ha, hfinish ▸ hareach⟩

/-- The grounded allowed-source prefix roots a selected request anchor in the
pre-stopped switch once its only two genuine deletion cases have been
handled.  As for finite old sources, represented cut edges are discharged
uniformly by rooted controls. -/
theorem selectedRequest_initial_rootedPreStopped_of_lastDeletedHead_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (GroundedRootInput (L := L) (hL := hL)) S.cut)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1)
    (hbackward : ∀ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace
        (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
          S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅ .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K ∅) a D.head)
    (hconflict : ∀ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp →
      q.start ∈ Gamma.source \ {R.record.initial} →
      q.finish = (selectedRequestTrace
        (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
          S K r).initial →
      q.support ⊆ parent.support → q.edgeSet ⊆ parent.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅ →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K ∅) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a
        (selectedRequestTrace
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K r).initial := by
  apply R.selectedRequest_initial_rootedAt_of_lastDeletedHead_cases
    (T := (∅ : Set V)) r
  · intro _parent _q _hparent _hstart _hfinish _hsupport _hedges
      D u _hu huCE
    let s : Request (GroundedRootInput (L := L) (hL := hL)) S.cut :=
      .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
    let c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut :=
      ⟨D.head, ⟨s, rfl⟩⟩
    exact hcontrol c
  · exact hbackward
  · exact hconflict
  · intro _parent _q _hparent _hstart _hfinish _hsupport _hedges
      _D u _hu _hresidual huEmpty
    simp only [Set.mem_empty_iff_false] at huEmpty

/-- A surviving fragment has an allowed rooted initial whenever either its
grounded parent is not the reserved component, or a represented cut edge
enters the fragment.  This is the exact nonexceptional part of the
first-fragment/cut-predecessor split. -/
theorem fragmentInitial_rootedPreStopped_of_grounded_nonreserved_or_cutPredecessor
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (P : (GroundedRootInput (L := L) (hL := hL)).Fragment)
    (hcase :
      (P.IsGrounded ∧ P.parent ≠ R.record ∧
        P.path.initial = P.parent.initial) ∨
      GroundingConcreteControls.hasCutPredecessor
        (GroundedRootInput (L := L) (hL := hL)) S.cut P)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a P.path.initial := by
  rcases hcase with ⟨hgrounded, hparentNe, hfirst⟩ |
      ⟨e, heCE, _heParent, heHead⟩
  · have hinitialNe : P.parent.initial ≠ R.record.initial := by
      intro heq
      apply hparentNe
      exact Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
        P.parent_mem R.limit_inessential.1
        P.parent.initial_mem_support (heq ▸ R.record.initial_mem_support)
    refine ⟨P.path.initial, ?_, .refl⟩
    rw [hfirst]
    exact ⟨hgrounded, fun h ↦ hinitialNe (Set.mem_singleton_iff.mp h)⟩
  · let s : Request (GroundedRootInput (L := L) (hL := hL)) S.cut :=
      .inr ⟨e, (GroundingCut.mem_CE.mp heCE).1⟩
    let c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut :=
      ⟨e.2, ⟨s, rfl⟩⟩
    obtain ⟨a, ha, hareach⟩ := hcontrol c
    change Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
        (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
          S K ∅) a e.2 at hareach
    rw [heHead] at hareach
    exact ⟨a, ha, hareach⟩

/-- Complete first-fragment classification for a surviving grounded-split
fragment.  Every nonexceptional initial is rooted; the only leaves are the
first fragment of the deliberately reserved component and the first
fragment of a genuinely hanging component. -/
theorem fragmentInitial_rootedPreStopped_or_reserved_or_hanging
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (P : (GroundedRootInput (L := L) (hL := hL)).Fragment)
    (hP : P ∈ GroundingCut.fragments
      (GroundedRootInput (L := L) (hL := hL)) S.cut)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1) :
    (∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a P.path.initial) ∨
      (P.parent = R.record ∧ P.path.initial = P.parent.initial) ∨
      (P.IsHanging ∧ P.path.initial = P.parent.initial) := by
  rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
      (GroundedRootInput (L := L) (hL := hL)) S.cut P hP with
      hfirst | hpred
  · rcases PopularAuxiliary.grounded_or_hanging Gamma P.parent with
        hgrounded | hhanging
    · by_cases hparent : P.parent = R.record
      · exact Or.inr (Or.inl ⟨hparent, hfirst⟩)
      · exact Or.inl
          (R.fragmentInitial_rootedPreStopped_of_grounded_nonreserved_or_cutPredecessor
            P (Or.inl ⟨hgrounded, hparent, hfirst⟩) hcontrol)
    · exact Or.inr (Or.inr ⟨hhanging, hfirst⟩)
  · exact Or.inl
      (R.fragmentInitial_rootedPreStopped_of_grounded_nonreserved_or_cutPredecessor
        P (Or.inr hpred) hcontrol)

/-- Exact positive data behind failure to root a blocking point.  Either the
fragment is one of the two genuine first-fragment leaves, or a concrete last
deleted head remains on the finite prefix to the blocking point. -/
inductive SplitGroundedBlockingRootFailureOutcome
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (P : (GroundedRootInput (L := L) (hL := hL)).Fragment) : Prop
  | reservedEscape
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (GroundedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial)
  | reservedTerminal
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (terminal : V) (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ P.MeetsEscape
        (GroundedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial)
  | hangingEscape
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (GroundedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial)
  | hangingTerminal
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (terminal : V) (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ P.MeetsEscape
        (GroundedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial)
  | deleted
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint
        (GroundedRootInput (L := L) (hL := hL)) S.cut P)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a lastDeleted.head)
      (deleted_class :
        (∃ u, (u, lastDeleted.head) ∈ segment.edgeSet ∧
          (u, lastDeleted.head) ∈ erasedSelectedDirectionEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅ .backward) ∨
        (∃ u, (u, lastDeleted.head) ∈ segment.edgeSet ∧
          (u, lastDeleted.head) ∈ forwardConflictCutEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅))

/-- Normalize a non-rooted blocking point to the preceding concrete
outcome.  This theorem performs the first-fragment split and exposes the
actual deleted edge; it does not leave a rooting callback. -/
theorem blockingPointRootFailureOutcome
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (P : (GroundedRootInput (L := L) (hL := hL)).Fragment)
    (hP : P ∈ GroundingCut.G0
      (GroundedRootInput (L := L) (hL := hL)) S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a
        (GroundingCut.blockingPoint
          (GroundedRootInput (L := L) (hL := hL)) S.cut P))
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1) :
    SplitGroundedBlockingRootFailureOutcome R P := by
  have deletedOutcome
      (hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial) :
      SplitGroundedBlockingRootFailureOutcome R P := by
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix P.path
        (GroundingCut.blockingPoint_mem_support
          (GroundedRootInput (L := L) (hL := hL)) S.cut P hP.2)
    have hqRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a q.start := by
      simpa only [hqStart] using hroot
    have hqNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a q.finish := by
      simpa only [hqFinish] using hnot
    obtain ⟨D, hDnot⟩ := exists_unrootedLastDeletedHead_split q hqRoot hqNot
    have hqFamily : q.edgeSet ⊆
        (GroundedRootInput (L := L) (hL := hL)).familyEdges := by
      intro e he
      exact ⟨P.parent, P.parent_mem, P.edges_subset (hqEdges he)⟩
    have hclass :
        (∃ u, (u, D.head) ∈ q.edgeSet ∧
          (u, D.head) ∈ erasedSelectedDirectionEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅ .backward) ∨
        (∃ u, (u, D.head) ∈ q.edgeSet ∧
          (u, D.head) ∈ forwardConflictCutEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) := by
      rcases D.exists_classified_deletedIncomingAt_split K ∅ hqFamily with
          hCE | hbackward | hconflict | ⟨u, _huParent, _huResidual, huEmpty⟩
      · obtain ⟨u, _huSegment, huCE⟩ := hCE
        exfalso
        apply hDnot
        let s : Request
            (GroundedRootInput (L := L) (hL := hL)) S.cut :=
          .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
        let c : ControlRequest
            (GroundedRootInput (L := L) (hL := hL)) S.cut :=
          ⟨D.head, ⟨s, rfl⟩⟩
        exact hcontrol c
      · exact Or.inl hbackward
      · exact Or.inr hconflict
      · simp only [Set.mem_empty_iff_false] at huEmpty
    exact .deleted q hqStart hqFinish hqSupport hqEdges D hDnot hclass
  rcases R.fragmentInitial_rootedPreStopped_or_reserved_or_hanging
      P hP.1 hcontrol with hroot | hreserved | hhanging
  · exact deletedOutcome hroot
  · by_cases hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial
    · exact deletedOutcome hroot
    · by_cases hescape : P.MeetsEscape
          (GroundedRootInput (L := L) (hL := hL)) S.cut
      · exact .reservedEscape hreserved.1 hreserved.2 hescape hroot
      · rcases hP.2 with hPescape | ⟨t, ht⟩
        · exact False.elim (hescape hPescape)
        · exact .reservedTerminal hreserved.1 hreserved.2 t ht hescape hroot
  · by_cases hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a P.path.initial
    · exact deletedOutcome hroot
    · by_cases hescape : P.MeetsEscape
          (GroundedRootInput (L := L) (hL := hL)) S.cut
      · exact .hangingEscape hhanging.1 hhanging.2 hescape hroot
      · rcases hP.2 with hPescape | ⟨t, ht⟩
        · exact False.elim (hescape hPescape)
        · exact .hangingTerminal hhanging.1 hhanging.2 t ht hescape hroot

/-- A blocking point is reached along the initial segment of its fragment.
In the pre-stopped switch the represented-cut case is again supplied by a
rooted control, leaving precisely backward selection and forward conflict as
the construction-specific cases. -/
theorem blockingPoint_rootedPreStopped_of_lastDeletedHead_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (P : (GroundedRootInput (L := L) (hL := hL)).Fragment)
    (hPblockable : GroundingCut.IsBlockable
      (GroundedRootInput (L := L) (hL := hL)) S.cut P)
    (hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a P.path.initial)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1)
    (hbackward : ∀ (q : FinitePath Gamma.graph),
      q.start = P.path.initial →
      q.finish = GroundingCut.blockingPoint
        (GroundedRootInput (L := L) (hL := hL)) S.cut P →
      q.support ⊆ P.path.support → q.edgeSet ⊆ P.path.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅ .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K ∅) a D.head)
    (hconflict : ∀ (q : FinitePath Gamma.graph),
      q.start = P.path.initial →
      q.finish = GroundingCut.blockingPoint
        (GroundedRootInput (L := L) (hL := hL)) S.cut P →
      q.support ⊆ P.path.support → q.edgeSet ⊆ P.path.edgeSet →
      ∀ (D : LastDeletedHead q (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅)) u,
        (u, D.head) ∈ q.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅ →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K ∅) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a
        (GroundingCut.blockingPoint
          (GroundedRootInput (L := L) (hL := hL)) S.cut P) := by
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix P.path
      (GroundingCut.blockingPoint_mem_support
        (GroundedRootInput (L := L) (hL := hL)) S.cut P hPblockable)
  have hqFamily : q.edgeSet ⊆
      (GroundedRootInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨P.parent, P.parent_mem, P.edges_subset (hqEdges he)⟩
  have hqRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K ∅) a q.start := by
    simpa only [hqStart] using hstart
  obtain ⟨a, ha, hareach⟩ :=
    exists_root_reaching_finishAt_of_lastDeletedHead_cases K ∅
      (Gamma.source \ {R.record.initial}) q hqFamily hqRoot
      (by
        intro D u _hu huCE
        let s : Request (GroundedRootInput (L := L) (hL := hL)) S.cut :=
          .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
        let c : ControlRequest
            (GroundedRootInput (L := L) (hL := hL)) S.cut :=
          ⟨D.head, ⟨s, rfl⟩⟩
        exact hcontrol c)
      (hbackward q hqStart hqFinish hqSupport hqEdges)
      (hconflict q hqStart hqFinish hqSupport hqEdges)
      (by
        intro _D u _hu _hresidual huEmpty
        simp only [Set.mem_empty_iff_false] at huEmpty)
  exact ⟨a, ha, hqFinish ▸ hareach⟩

/-- Rooting the raw preliminary boundary in the pre-stopped relation reduces
to its three defining point classes.  Stopping and antichain pruning can be
performed only after this source-rooting statement has been established. -/
theorem preliminaryBoundary_rootedPreStopped_of_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hfinite : ∀ b,
      b ∈ (GroundedRootInput (L := L) (hL := hL)).finiteSource →
      PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a b)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1)
    (hblocking : ∀ P : (GroundedRootInput (L := L) (hL := hL)).Fragment,
      P ∈ GroundingCut.G0
        (GroundedRootInput (L := L) (hL := hL)) S.cut →
      GroundingCut.IsBlockable
        (GroundedRootInput (L := L) (hL := hL)) S.cut P →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a
          (GroundingCut.blockingPoint
            (GroundedRootInput (L := L) (hL := hL)) S.cut P)) :
    ∀ t ∈ GroundingCut.BB
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a t := by
  intro t ht
  rcases GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
      ht with
    ⟨htFinite, htCut⟩ | ⟨r, _hrAux, hrExit⟩ |
      ⟨P, hPG0, hPblockable, hPt, _htSupport⟩
  · exact hfinite t htFinite htCut
  · cases r with
    | inl old =>
        have hold : old.1 = t := by
          simpa only [requestExit] using hrExit
        simpa only [oldRequestControl_val, hold] using
          hcontrol (oldRequestControl old)
    | inr edge => cases _hrAux
  · rw [← hPt]
    exact hblocking P hPG0 hPblockable

/-- Root a finite old cut source from its allowed canonical parent.  The
four callbacks are precisely the possible causes of the last deleted edge.
-/
theorem cutFiniteSource_rootedAt_of_lastDeletedHead_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {b : V}
    (hb : b ∈ (GroundedRootInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hCE : ∀ (p : FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      p.start ∈ Gamma.source \ {R.record.initial} →
      (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp →
      ∀ (D : LastDeletedHead p (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T)) u,
        (u, D.head) ∈ p.edgeSet →
        (u, D.head) ∈ GroundingCut.CE
          (GroundedRootInput (L := L) (hL := hL)) S.cut →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K T) a D.head)
    (hbackward : ∀ (p : FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      p.start ∈ Gamma.source \ {R.record.initial} →
      (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp →
      ∀ (D : LastDeletedHead p (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T)) u,
        (u, D.head) ∈ p.edgeSet →
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T .backward →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K T) a D.head)
    (hconflict : ∀ (p : FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      p.start ∈ Gamma.source \ {R.record.initial} →
      (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp →
      ∀ (D : LastDeletedHead p (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T)) u,
        (u, D.head) ∈ p.edgeSet →
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K T) a D.head)
    (hboundary : ∀ (p : FinitePath Gamma.graph),
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) →
      p.start ∈ Gamma.source \ {R.record.initial} →
      (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp →
      ∀ (D : LastDeletedHead p (erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T)) u,
        (u, D.head) ∈ p.edgeSet →
        (u, D.head) ∈ residualLadderEdges
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground)) S →
        u ∈ T →
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
              (GroundedRootIndexed (L := L) (hL := hL)
                (hground := hground)) S K T) a D.head) :
    ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T) a b := by
  obtain ⟨p, hchosen, hfinish, hstart, hparent⟩ :=
    R.exists_cutFiniteSource_parent_with_allowed_root hb hbCut
  have hpFamily : p.edgeSet ⊆
      (GroundedRootInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨(.inl p : Gamma.DPath), hparent.1, he⟩
  have hrootStart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T) a p.start := ⟨p.start, hstart, .refl⟩
  obtain ⟨a, ha, hareach⟩ :=
    exists_root_reaching_finishAt_of_lastDeletedHead_cases K T
      (Gamma.source \ {R.record.initial}) p hpFamily hrootStart
      (hCE p hchosen hstart hparent)
      (hbackward p hchosen hstart hparent)
      (hconflict p hchosen hstart hparent)
      (hboundary p hchosen hstart hparent)
  exact ⟨a, ha, hfinish ▸ hareach⟩

/-- Pointwise BB-rooting reduces to finite old sources, old request exits,
and blocking points. -/
theorem frontier_rootedAt_of_cases
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hT : T ⊆ GroundingCut.BB
      (GroundedRootInput (L := L) (hL := hL)) S.cut)
    (hfinite : ∀ b,
      b ∈ (GroundedRootInput (L := L) (hL := hL)).finiteSource →
      PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a b)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a c.1)
    (hblocking : ∀ P : (GroundedRootInput (L := L) (hL := hL)).Fragment,
      P ∈ GroundingCut.G0
        (GroundedRootInput (L := L) (hL := hL)) S.cut →
      GroundingCut.IsBlockable
        (GroundedRootInput (L := L) (hL := hL)) S.cut P →
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a
          (GroundingCut.blockingPoint
            (GroundedRootInput (L := L) (hL := hL)) S.cut P)) :
    ∀ t ∈ T, ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
          (GroundedRootIndexed (L := L) (hL := hL) (hground := hground))
            S K T) a t := by
  intro t ht
  rcases GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
      (hT ht) with
    ⟨htFinite, htCut⟩ | ⟨r, _hrAux, hrExit⟩ |
      ⟨P, hPG0, hPblockable, hPt, _htSupport⟩
  · exact hfinite t htFinite htCut
  · cases r with
    | inl old =>
        have hold : old.1 = t := by
          simpa only [requestExit] using hrExit
        simpa only [oldRequestControl_val, hold] using
          hcontrol (oldRequestControl old)
    | inr edge => cases _hrAux
  · rw [← hPt]
    exact hblocking P hPG0 hPblockable

end SplitGroundedUnusedRecord
end DWeb.KappaLadder
end Erdos599

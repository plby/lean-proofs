/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedBoundaryOwner
import ErdosProblems.Erdos599.SplitGroundingGroundedRootTransfer
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Root normalization at a source-correct stopped frontier

This is the `T`-parametric counterpart of the preliminary-boundary root
reduction.  It classifies a failed root at a point of `splitGroundedBB`
without forgetting the `H_empty` deletion.  Old controls are discharged
immediately.  Finite-source and blocking owners retain an actual last
deleted edge in the final relation stopped at `T`; a represented-cut edge is
also discharged immediately by the corresponding rooted control.
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

private abbrev ReducedRootInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ReducedRootIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ReducedRootEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (ReducedRootIndexed (L := L) (hL := hL) (hground := hground)) S K T

/-- After the represented-cut case is rooted by its control, these are the
three genuine possible classes of a deleted incoming edge at the final
frontier `T`. -/
abbrev SplitGroundedReducedDeletedClassAt
    (T : Set V) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (ReducedRootEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T)) : Prop :=
  (∃ u, (u, D.head) ∈ p.edgeSet ∧
    (u, D.head) ∈ erasedSelectedDirectionEdgesAt
      (ReducedRootIndexed (L := L) (hL := hL) (hground := hground))
        S K T .backward) ∨
  (∃ u, (u, D.head) ∈ p.edgeSet ∧
    (u, D.head) ∈ forwardConflictCutEdgesAt
      (ReducedRootIndexed (L := L) (hL := hL) (hground := hground))
        S K T) ∨
  ∃ u, (u, D.head) ∈ p.edgeSet ∧
    (u, D.head) ∈ residualLadderEdges
      (ReducedRootIndexed (L := L) (hL := hL) (hground := hground)) S ∧
    u ∈ T

private theorem exists_unrootedLastDeletedHead_reducedAt
    {T A : Set V} (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a p.start)
    (hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a p.finish) :
    ∃ D : LastDeletedHead p
        (ReducedRootEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T),
      ¬ ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet,
      e ∉ ReducedRootEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hastart⟩ := hstart
    refine ⟨a, ha, hastart.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ ReducedRootEdges
        (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T)
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
      (fun x y ↦ (x, y) ∈ ReducedRootEdges
        (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T)
      D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ ReducedRootEdges
        (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet
        D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

namespace SplitGroundedUnusedRecord

/-- The initial of a surviving fragment is rooted at the final stopped
relation unless it is the first surviving fragment of the reserved record
or of a genuinely hanging component. -/
theorem fragmentInitial_rootedAt_or_reserved_or_hanging
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (ReducedRootInput (L := L) (hL := hL)).Fragment)
    (hP : P ∈ GroundingCut.fragments
      (ReducedRootInput (L := L) (hL := hL)) S.cut)
    (hcontrol : ∀ c : ControlRequest
        (ReducedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    (∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a P.path.initial) ∨
      (P.parent = R.record ∧ P.path.initial = P.parent.initial) ∨
      (P.IsHanging ∧ P.path.initial = P.parent.initial) := by
  rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
      (ReducedRootInput (L := L) (hL := hL)) S.cut P hP with
      hfirst | ⟨e, heCE, _heParent, heHead⟩
  · rcases PopularAuxiliary.grounded_or_hanging Gamma P.parent with
        hgrounded | hhanging
    · by_cases hparent : P.parent = R.record
      · exact Or.inr (Or.inl ⟨hparent, hfirst⟩)
      · left
        have hinitialNe : P.parent.initial ≠ R.record.initial := by
          intro heq
          apply hparent
          exact Alternating.DWeb.IsWarp.eq_of_mem_support
            (hL.legal.warpStages (Ladder.finalStage kappa))
            P.parent_mem R.limit_inessential.1
            P.parent.initial_mem_support
              (heq ▸ R.record.initial_mem_support)
        refine ⟨P.path.initial, ?_, .refl⟩
        rw [hfirst]
        exact ⟨hgrounded,
          fun h ↦ hinitialNe (Set.mem_singleton_iff.mp h)⟩
    · exact Or.inr (Or.inr ⟨hhanging, hfirst⟩)
  · left
    let s : Request (ReducedRootInput (L := L) (hL := hL)) S.cut :=
      .inr ⟨e, (GroundingCut.mem_CE.mp heCE).1⟩
    let c : ControlRequest
        (ReducedRootInput (L := L) (hL := hL)) S.cut :=
      ⟨e.2, ⟨s, rfl⟩⟩
    obtain ⟨a, ha, hareach⟩ := hcontrol c
    change Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ReducedRootEdges
        (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T) a e.2 at hareach
    rw [heHead] at hareach
    exact ⟨a, ha, hareach⟩

/-- Exact positive data behind a failed finite-source root at the final
stopped relation. -/
structure SplitGroundedReducedFiniteSourceRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (b : V)
    (hb : b ∈ (ReducedRootInput (L := L) (hL := hL)).finiteSource) where
  parent : FinitePath Gamma.graph
  chosen : L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
    some (.inl parent : Gamma.DPath)
  parent_finish : parent.finish = b
  parent_start : parent.start ∈ Gamma.source \ {R.record.initial}
  parent_inessential : (.inl parent : Gamma.DPath) ∈
    Gamma.inessentialPaths L.limitWarp
  lastDeleted : LastDeletedHead parent
    (ReducedRootEdges (L := L) (hL := hL) (hground := hground)
      (S := S) (K := K) T)
  head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ReducedRootEdges
        (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T) a lastDeleted.head
  deleted_class : SplitGroundedReducedDeletedClassAt
    (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
      T parent lastDeleted

/-- Normalize a failed finite cut-source root in the final stopped relation.
The represented-cut case is impossible because its control is rooted. -/
theorem finiteSourceRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {b : V}
    (hb : b ∈ (ReducedRootInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a b)
    (hcontrol : ∀ c : ControlRequest
        (ReducedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    Nonempty (SplitGroundedReducedFiniteSourceRootFailureAt R T b hb) := by
  obtain ⟨p, hchosen, hfinish, hstart, hparent⟩ :=
    R.exists_cutFiniteSource_parent_with_allowed_root hb hbCut
  have hpRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a p.start := ⟨p.start, hstart, .refl⟩
  have hpNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a p.finish := by
    simpa only [hfinish] using hnot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead_reducedAt p hpRoot hpNot
  have hpFamily : p.edgeSet ⊆
      (ReducedRootInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨(.inl p : Gamma.DPath), hparent.1, he⟩
  have hclass : SplitGroundedReducedDeletedClassAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T p D := by
    rcases D.exists_classified_deletedIncomingAt_split K T hpFamily with
        hCE | hbackward | hconflict | hboundary
    · obtain ⟨u, _huParent, huCE⟩ := hCE
      exfalso
      apply hDnot
      let s : Request (ReducedRootInput (L := L) (hL := hL)) S.cut :=
        .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
      let c : ControlRequest
          (ReducedRootInput (L := L) (hL := hL)) S.cut :=
        ⟨D.head, ⟨s, rfl⟩⟩
      exact hcontrol c
    · exact Or.inl hbackward
    · exact Or.inr (Or.inl hconflict)
    · exact Or.inr (Or.inr hboundary)
  exact ⟨{
    parent := p
    chosen := hchosen
    parent_finish := hfinish
    parent_start := hstart
    parent_inessential := hparent
    lastDeleted := D
    head_not_rooted := hDnot
    deleted_class := hclass }⟩

/-- Exact positive data behind a failed reduced blocking-point root at the
final stopped relation. -/
inductive SplitGroundedReducedBlockingRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (ReducedRootInput (L := L) (hL := hL)).Fragment) : Prop
  | reservedEscape
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (ReducedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | reservedTerminal
      (parent_eq : P.parent = R.record)
      (initial_eq : P.path.initial = P.parent.initial)
      (terminal : V) (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ P.MeetsEscape
        (ReducedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | hangingEscape
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (meets_escape : P.MeetsEscape
        (ReducedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | hangingTerminal
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (terminal : V) (terminal_eq : P.path.terminal? = some terminal)
      (not_meets_escape : ¬ P.MeetsEscape
        (ReducedRootInput (L := L) (hL := hL)) S.cut)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
  | deleted
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint
        (ReducedRootInput (L := L) (hL := hL)) S.cut P)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (ReducedRootEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a lastDeleted.head)
      (deleted_class : SplitGroundedReducedDeletedClassAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T segment lastDeleted)

/-- Normalize a failed reduced blocking-point root at the actual final
frontier `T`. -/
theorem reducedBlockingPointRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (P : (ReducedRootInput (L := L) (hL := hL)).Fragment)
    (hP : P ∈ L.splitGroundedG0 hL.legal S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a
        (GroundingCut.blockingPoint
          (ReducedRootInput (L := L) (hL := hL)) S.cut P))
    (hcontrol : ∀ c : ControlRequest
        (ReducedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    SplitGroundedReducedBlockingRootFailureAt R T P := by
  have deletedOutcome
      (hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial) :
      SplitGroundedReducedBlockingRootFailureAt R T P := by
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix P.path
        (GroundingCut.blockingPoint_mem_support
          (ReducedRootInput (L := L) (hL := hL)) S.cut P hP.2)
    have hqRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a q.start := by
      simpa only [hqStart] using hroot
    have hqNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a q.finish := by
      simpa only [hqFinish] using hnot
    obtain ⟨D, hDnot⟩ :=
      exists_unrootedLastDeletedHead_reducedAt q hqRoot hqNot
    have hqFamily : q.edgeSet ⊆
        (ReducedRootInput (L := L) (hL := hL)).familyEdges := by
      intro e he
      exact ⟨P.parent, P.parent_mem, P.edges_subset (hqEdges he)⟩
    have hclass : SplitGroundedReducedDeletedClassAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T q D := by
      rcases D.exists_classified_deletedIncomingAt_split K T hqFamily with
          hCE | hbackward | hconflict | hboundary
      · obtain ⟨u, _huSegment, huCE⟩ := hCE
        exfalso
        apply hDnot
        let s : Request (ReducedRootInput (L := L) (hL := hL)) S.cut :=
          .inr ⟨(u, D.head), (GroundingCut.mem_CE.mp huCE).1⟩
        let c : ControlRequest
            (ReducedRootInput (L := L) (hL := hL)) S.cut :=
          ⟨D.head, ⟨s, rfl⟩⟩
        exact hcontrol c
      · exact Or.inl hbackward
      · exact Or.inr (Or.inl hconflict)
      · exact Or.inr (Or.inr hboundary)
    exact .deleted q hqStart hqFinish hqSupport hqEdges D hDnot hclass
  rcases R.fragmentInitial_rootedAt_or_reserved_or_hanging T P hP.1.1 hcontrol with
      hroot | hreserved | hhanging
  · exact deletedOutcome hroot
  · by_cases hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial
    · exact deletedOutcome hroot
    · by_cases hescape : P.MeetsEscape
          (ReducedRootInput (L := L) (hL := hL)) S.cut
      · exact .reservedEscape hreserved.1 hreserved.2 hescape hroot
      · rcases hP.2 with hPescape | ⟨t, ht⟩
        · exact False.elim (hescape hPescape)
        · exact .reservedTerminal hreserved.1 hreserved.2 t ht hescape hroot
  · by_cases hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial
    · exact deletedOutcome hroot
    · by_cases hescape : P.MeetsEscape
          (ReducedRootInput (L := L) (hL := hL)) S.cut
      · exact .hangingEscape hhanging.1 hhanging.2 hescape hroot
      · rcases hP.2 with hPescape | ⟨t, ht⟩
        · exact False.elim (hescape hPescape)
        · exact .hangingTerminal hhanging.1 hhanging.2 t ht hescape hroot

/-- Total owner-level normalization for an unrooted point of the corrected
boundary.  The old-control owner cannot survive the rooted-control premise.
-/
inductive SplitGroundedReducedBBRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (t : V) : Prop
  | finite
      (ht : t ∈ (ReducedRootInput (L := L) (hL := hL)).finiteSource)
      (data : SplitGroundedReducedFiniteSourceRootFailureAt R T t ht)
  | blocking
      (P : (ReducedRootInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (ReducedRootInput (L := L) (hL := hL)) S.cut P = t)
      (data : SplitGroundedReducedBlockingRootFailureAt R T P)

/-- An unrooted corrected-boundary point is either a normalized finite
source failure or a normalized reduced blocking-fragment failure. -/
theorem reducedBBRootFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    (ht : t ∈ L.splitGroundedBB hL.legal S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t)
    (hcontrol : ∀ c : ControlRequest
        (ReducedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    SplitGroundedReducedBBRootFailureAt R T t := by
  cases L.splitGroundedReducedBBPointOwner_of_mem ht with
  | finiteSource hfinite hcut =>
      exact .finite hfinite
        (R.finiteSourceRootFailureAt T hfinite hcut hnot hcontrol).some
  | oldControl old heq =>
      exfalso
      apply hnot
      simpa only [← heq, oldRequestControl_val] using
        hcontrol (oldRequestControl old)
  | blocking P hP heq _hsupport =>
      have hnotP : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ReducedRootEdges
              (L := L) (hL := hL) (hground := hground)
                (S := S) (K := K) T) a
            (GroundingCut.blockingPoint
              (ReducedRootInput (L := L) (hL := hL)) S.cut P) := by
        simpa only [heq] using hnot
      exact .blocking P hP heq
        (R.reducedBlockingPointRootFailureAt T P hP hnotP hcontrol)

/-- Pointwise totalization over an arbitrary final frontier contained in the
corrected boundary.  If rooting does not already hold everywhere, the
failure point retains both its membership in `T` and the complete reduced
owner normal form. -/
theorem reducedFrontier_rootedAt_or_failure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hT : T ⊆ L.splitGroundedBB hL.legal S.cut)
    (hcontrol : ∀ c : ControlRequest
        (ReducedRootInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1) :
    (∀ t ∈ T, ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t) ∨
      ∃ t ∈ T, SplitGroundedReducedBBRootFailureAt R T t := by
  classical
  by_cases hall : ∀ t ∈ T, ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ReducedRootEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨t, ht, hnot⟩ := hall
    have hnot' : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ReducedRootEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a t := by
      rintro ⟨a, ha, hareach⟩
      exact hnot a ha hareach
    exact ⟨t, ht, R.reducedBBRootFailureAt T (hT ht) hnot' hcontrol⟩

end SplitGroundedUnusedRecord
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.reducedBBRootFailureAt
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.reducedFrontier_rootedAt_or_failure

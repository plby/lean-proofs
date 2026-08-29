/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantControlResolution
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingRecord
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingSelection

/-!
# Removing reserved-record leaves from the relevant source-first normal form

A reserved record whose complete auxiliary trace avoids the popular cut is
disjoint from the relevant boundary.  Consequently its initial vertex cannot
be a source-first boundary point, and a relevant first fragment cannot be a
fragment of that record.  These are the two exact eliminations needed when the
source-first totalizer is instantiated with the cut-avoiding unused record.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder.SplitGroundedUnusedRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

local notation "J" => L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev CutAvoidingIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev CutAvoidingEdges (T : Set V) : Set (V × V) :=
  GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
    (CutAvoidingIndexed (L := L) (hL := hL) (hground := hground)) S K T

private abbrev CutAvoidingFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

/-- The source endpoint of a cut-avoiding reserved record is not a member of
the source-first relevant frontier. -/
theorem record_initial_not_mem_relevantSourceFirstBB_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut) :
    R.record.initial ∉
      L.splitGroundedRelevantSourceFirstBB hL.legal S.cut := by
  intro hinitial
  have hinitialBB : R.record.initial ∈
      L.splitGroundedRelevantBB hL.legal S.cut :=
    L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut hinitial
  exact Set.disjoint_left.mp
    (R.relevantBB_disjoint_record_of_trace_disjoint hcut)
      hinitialBB R.record.initial_mem_support

/-- The `sourceEndpoint` equality exposed by the source-first totalizer is
impossible for a cut-avoiding unused record. -/
theorem sourceEndpoint_ne_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut)
    {t : V}
    (ht : t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut) :
    t ≠ R.record.initial := by
  intro heq
  exact R.record_initial_not_mem_relevantSourceFirstBB_of_trace_disjoint hcut
    (heq ▸ ht)

/-- In the virtual-escape constructor of the source-first totalizer, the
reserved-parent alternative is impossible for a cut-avoiding record. -/
theorem virtualEscape_origin_hanging_of_trace_disjoint
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut)
    (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
    (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
    (origin :
      (P.parent = R.record ∧ P.path.initial = P.parent.initial) ∨
      (P.IsHanging ∧ P.path.initial = P.parent.initial)) :
    P.IsHanging ∧ P.path.initial = P.parent.initial := by
  rcases origin with hreserved | hhanging
  · exact False.elim
      (R.relevantG0_parent_ne_record_of_trace_disjoint hcut P hP hreserved.1)
  · exact hhanging

/-- Deleted-edge geometry specialized to the actual source-first frontier.
The boundary-departure constructor retains the concrete roofed ambient
source prefix witnessing that its tail is itself a source-first boundary
point. -/
inductive SplitGroundedRelevantSourceFirstDeletedOutcomeAt
    (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p (CutAvoidingEdges
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))) : Prop
  | backward
      (tail : V)
      (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (selected_backward : (tail, D.head) ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (CutAvoidingIndexed (L := L) (hL := hL)
            (hground := hground)) S K
              (CutAvoidingFrontier (L := L) (hL := hL) (S := S)) .backward)
      (owner : GroundingErasedDecode.ActiveControlRequestAt
        (CutAvoidingIndexed (L := L) (hL := hL)
          (hground := hground)) S K
            (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))
      (link : Alternating.Link Gamma.graph)
      (link_mem : link ∈
        (GroundingErasedDecode.selectedErasedCompression
          (CutAvoidingIndexed (L := L) (hL := hL)
            (hground := hground)) S K
          (GroundingErasedDecode.chosenRequest owner.1)).path.links)
      (link_direction : link.direction = .backward)
      (edge_mem_link : (tail, D.head) ∈ link.path.edgeSet)
      (link_subpath : link.path.IsSubpathOf parent)
      (parent_exposed : parent ∈
        GroundingSimultaneousDecode.exposedLadderPaths
          (L.splitGroundedPopularAuxiliaryInput hL.legal)
          (GroundingSimultaneousDecode.strongSelectedPath
            (CutAvoidingIndexed (L := L) (hL := hL)
              (hground := hground)) S K
            (GroundingErasedDecode.chosenRequest owner.1)))
  | forwardSplice
      (splice : SplitGroundedReducedForwardConflictSpliceData
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          (CutAvoidingFrontier (L := L) (hL := hL) (S := S)) parent p D)
  | boundaryDeparture
      (tail : V)
      (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (residual : (tail, D.head) ∈
        GroundingErasedDecode.residualLadderEdges
          (CutAvoidingIndexed (L := L) (hL := hL)
            (hground := hground)) S)
      (sourcePath : FinitePath Gamma.graph)
      (source_start : sourcePath.start ∈ Gamma.source)
      (source_finish : sourcePath.finish = tail)
      (source_roof : sourcePath.support ⊆
        (L.splitGroundedPopularAuxiliaryInput hL.legal).roofRegion)
      (tail_relevant : tail ∈ L.splitGroundedRelevantBB hL.legal S.cut)
      (source_first : ∀ x ∈ sourcePath.walk.support.dropLast,
        x ∉ L.splitGroundedRelevantBB hL.legal S.cut)

/-- Expand a generic stopped-boundary outcome at the actual relevant
source-first frontier. -/
theorem refineDeletedOutcomeRelevantSourceFirst
    {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p (CutAvoidingEdges
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))}
    (outcome : SplitGroundedReducedDeletedOutcomeAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        (CutAvoidingFrontier (L := L) (hL := hL) (S := S)) parent p D) :
    SplitGroundedRelevantSourceFirstDeletedOutcomeAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        parent p D := by
  cases outcome with
  | backward tail hin hselected owner link hlink hdir heLink hsub hexposed =>
      exact .backward tail hin hselected owner link hlink hdir heLink hsub
        hexposed
  | forwardLastContact splice => exact .forwardSplice splice
  | boundaryDeparture tail hin hresidual htail =>
      obtain ⟨Q, hsource, hfinish, hroof, hrelevant, hfirst⟩ := htail
      exact .boundaryDeparture tail hin hresidual Q hsource hfinish hroof
        hrelevant hfirst

/-- Exact residuals after the unused record has been chosen to avoid the
whole popular cut.  Compared with the premise-free totalizer, the reserved
source endpoint has disappeared, every virtual escape has a hanging parent,
and an unrooted control has already been expanded at the native frontier. -/
inductive SplitGroundedRelevantCutAvoidingFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (t : V) : Prop
  | control
      (c : GroundingErasedDecode.ControlRequest J S.cut)
      (resolution : SplitGroundedRelevantControlResolutionAt R
        (CutAvoidingFrontier (L := L) (hL := hL) (S := S)) c)
  | finite
      (ht : t ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).finiteSource)
      (parent : FinitePath Gamma.graph)
      (chosen : L.chosen (L.finiteTerminalIndex ⟨t, ht⟩) =
        some (.inl parent : Gamma.DPath))
      (parent_finish : parent.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ CutAvoidingEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (CutAvoidingFrontier (L := L) (hL := hL) (S := S))) a t)
      (parent_start : parent.start ∈ Gamma.source \ {R.record.initial})
      (parent_inessential : (.inl parent : Gamma.DPath) ∈
        Gamma.inessentialPaths L.limitWarp)
      (lastDeleted : LastDeletedHead parent (CutAvoidingEdges
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          (CutAvoidingFrontier (L := L) (hL := hL) (S := S))))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ CutAvoidingEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))
            a lastDeleted.head)
      (outcome : SplitGroundedRelevantSourceFirstDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          (.inl parent : Gamma.DPath) parent lastDeleted)
  | hangingVirtualEscape
      (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint J S.cut P = t)
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ CutAvoidingEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))
            a P.path.initial)
      (escape : SplitGroundedRelevantVirtualEscape L hL.legal S.cut t)
  | deleted
      (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint J S.cut P = t)
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (initial_rooted : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ CutAvoidingEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))
          a P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint J S.cut P)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ CutAvoidingEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (CutAvoidingFrontier (L := L) (hL := hL) (S := S))) a t)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment (CutAvoidingEdges
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          (CutAvoidingFrontier (L := L) (hL := hL) (S := S))))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ CutAvoidingEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K)
                (CutAvoidingFrontier (L := L) (hL := hL) (S := S)))
            a lastDeleted.head)
      (outcome : SplitGroundedRelevantSourceFirstDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          P.parent segment lastDeleted)

/-- Eliminate the two reserved-record leaves and expand stopped controls in
one source-first failure. -/
theorem resolveSourceFirstTotalFailureCutAvoiding
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut)
    {t : V}
    (ht : t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
    (F : SplitGroundedRelevantSourceFirstTotalFailureAt R
      (CutAvoidingFrontier (L := L) (hL := hL) (S := S)) t) :
    SplitGroundedRelevantCutAvoidingFailureAt R t := by
  cases F with
  | control c hnot =>
      exact .control c
        (L.splitGroundedRelevantControlResolutionAt R
          (CutAvoidingFrontier (L := L) (hL := hL) (S := S)) c hnot)
  | finite hfinite parent hchosen hfinish hboundary hstart hinessential D hDnot outcome =>
      exact .finite hfinite parent hchosen hfinish hboundary hstart hinessential
        D hDnot (refineDeletedOutcomeRelevantSourceFirst outcome)
  | sourceEndpoint heq =>
      exact False.elim (R.sourceEndpoint_ne_of_trace_disjoint hcut ht heq)
  | virtualEscape P hP heq origin hnot escape =>
      have hhanging :=
        R.virtualEscape_origin_hanging_of_trace_disjoint hcut P hP origin
      exact .hangingVirtualEscape P hP heq hhanging.1 hhanging.2 hnot escape
  | deleted P hP heq segment hstart hinitial hfinish hboundary hsupport hedges D hDnot outcome =>
      exact .deleted P hP heq segment hstart hinitial hfinish hboundary
        hsupport hedges D hDnot
          (refineDeletedOutcomeRelevantSourceFirst outcome)

/-- Cut-avoiding source-first dispatcher with no stopped-control premise and
no reserved-record residual. -/
theorem exists_hindrance_or_splitGroundedRelevantCutAvoidingFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace J R.record) S.cut)
    (hC : Popular.IsSeparator
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
        SplitGroundedRelevantCutAvoidingFailureAt R t := by
  rcases exists_hindrance_or_splitGroundedRelevantSourceFirstTotalFailure
      R hC with hhindrance | ⟨t, ht, hfailure⟩
  · exact Or.inl hhindrance
  · exact Or.inr ⟨t, ht,
      resolveSourceFirstTotalFailureCutAvoiding R hcut ht hfailure⟩

/-- Choose the cut-avoiding unused record internally.  This is the
premise-free separator-branch normal form for arbitrary honest controls. -/
theorem exists_hindrance_or_exists_splitGroundedRelevantCutAvoidingFailure
    (hC : Popular.IsSeparator
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda S.cut) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ R : L.SplitGroundedUnusedRecord hL hground S K,
        Disjoint (PopularSwitching.ladderTrace
          (L.splitGroundedPopularAuxiliaryInput hL.legal) R.record) S.cut ∧
        ∃ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
          SplitGroundedRelevantCutAvoidingFailureAt R t := by
  obtain ⟨R, hcut⟩ :=
    L.exists_splitGroundedUnusedRecord_trace_disjoint hL hground S K
  rcases R.exists_hindrance_or_splitGroundedRelevantCutAvoidingFailure
      hcut hC with hhindrance | hfailure
  · exact Or.inl hhindrance
  · exact Or.inr ⟨R, hcut, hfailure⟩

end DWeb.KappaLadder.SplitGroundedUnusedRecord
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.sourceEndpoint_ne_of_trace_disjoint
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.virtualEscape_origin_hanging_of_trace_disjoint
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.exists_hindrance_or_splitGroundedRelevantCutAvoidingFailure
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.exists_hindrance_or_exists_splitGroundedRelevantCutAvoidingFailure

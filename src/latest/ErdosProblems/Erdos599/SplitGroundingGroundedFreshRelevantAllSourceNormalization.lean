/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantAllSourceFailure
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantDeletedNormalization

/-!
# Normalizing all-source relevant failures

Every finite segment retained by the all-source classifier lies on one
limiting-ladder component and ends on the source-first relevant frontier.
The canonical reserved record is disjoint from that frontier.  Warp
disjointness therefore shows that the entire segment parent is different
from the reserved record, and full-source reachability of its start can be
upgraded to allowed-source reachability.

This is the exact bridge which lets the existing well-founded native-`T`
backward-owner normalizer be reused without treating the reserved source as
an artificial failure.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev AllNormInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev AllNormControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev AllNormRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev AllNormFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev AllNormEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (AllNormControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (AllNormFrontier (L := L) (hL := hL) (S := S))

private abbrev AllNormAllowedSources : Set V :=
  Gamma.source \ {
    (AllNormRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- A limiting-ladder parent containing a source-first frontier point is not
the canonical reserved record. -/
theorem splitGroundedFresh_parent_ne_reserved_of_frontier_segment
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (p : FinitePath Gamma.graph) (hsupport : p.support ⊆ parent.support)
    {t : V} (hfinish : p.finish = t)
    (ht : t ∈ AllNormFrontier (L := L) (hL := hL) (S := S)) :
    parent ≠ (AllNormRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record := by
  intro heq
  let R := AllNormRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  have htParent : t ∈ parent.support := by
    rw [← hfinish]
    exact hsupport p.finish_mem_support
  have htRecord : t ∈ R.record.support := by
    rw [← heq]
    exact htParent
  exact Set.disjoint_left.mp
    (R.relevantBB_disjoint_record_of_trace_disjoint
      (L.splitGroundedFreshAvoidingCanonicalUnusedRecord_trace_disjoint
        hL hground hnotFresh S))
    (L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut ht)
    htRecord

/-- Every point on such a nonreserved limiting-ladder parent lies outside
the reserved record. -/
theorem splitGroundedFresh_mem_parent_not_mem_reserved
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hne : parent ≠ (AllNormRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record)
    {x : V} (hx : x ∈ parent.support) :
    x ∉ (AllNormRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.support := by
  intro hxRecord
  apply hne
  exact Alternating.DWeb.IsWarp.eq_of_mem_support
    (hL.legal.warpStages (Ladder.finalStage kappa))
    hparent
    (AllNormRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).limit_inessential.1
    hx hxRecord

/-- Exact normalized residual after eliminating the artificial
reserved-source possibility from a full-source failure. -/
inductive SplitGroundedFreshRelevantAllSourceNormalizedFailureAt
    (t : V) : Prop
  | control
      (c : ControlRequest (AllNormInput (L := L) (hL := hL)) S.cut)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a c.1)
      (origin : L.SplitGroundedFreshRelevantAllSourceControlOriginAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) t c)
      (resolution : SplitGroundedRelevantControlResolutionAt
        (AllNormRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (AllNormFrontier (L := L) (hL := hL) (S := S)) c)
  | normalized
      (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
      (D : LastDeletedHead p
        (AllNormEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (finish_eq : p.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (data : L.SplitGroundedFreshRelevantDeletedNormalizationAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) parent p D)
  | hangingVirtualEscape
      (P : (AllNormInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (AllNormInput (L := L) (hL := hL)) S.cut P = t)
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a P.path.initial)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (escape : SplitGroundedRelevantVirtualEscape L hL.legal S.cut t)

/-- Every normalized branch retains the non-rooted certificate for the
original source-first frontier point, independently of any intermediate
control or route endpoint exposed by its geometry. -/
theorem SplitGroundedFreshRelevantAllSourceNormalizedFailureAt.boundary_not_rooted
    {t : V}
    (F : L.SplitGroundedFreshRelevantAllSourceNormalizedFailureAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) t) :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllNormEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  cases F with
  | control _ hboundary _ _ _ => exact hboundary
  | normalized _ _ _ _ hboundary _ => exact hboundary
  | hangingVirtualEscape _ _ _ _ _ _ hboundary _ => exact hboundary

/-- Normalize every concrete all-source failure.  The finite and blocking
segments enter the existing well-founded backward-owner recursion after
their full-source root is proved to avoid the reserved record. -/
theorem SplitGroundedFreshRelevantAllSourceFailureAt.normalize
    {t : V}
    (ht : t ∈ AllNormFrontier (L := L) (hL := hL) (S := S))
    (F : L.SplitGroundedFreshRelevantAllSourceFailureAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) t) :
    L.SplitGroundedFreshRelevantAllSourceNormalizedFailureAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) t := by
  let R := AllNormRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  cases F with
  | control c hboundary hnot origin =>
      have hnotAllowed : ¬ ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a c.1 := by
        rintro ⟨a, ha, hac⟩
        exact hnot ⟨a, ha.1, hac⟩
      exact .control c hboundary hnot origin
        (L.splitGroundedRelevantControlResolutionAt R
          (AllNormFrontier (L := L) (hL := hL) (S := S))
          c hnotAllowed)
  | finite hfinite parent hchosen hfinish hboundary hstart hinessential D
      hDnot outcome =>
      have hne := L.splitGroundedFresh_parent_ne_reserved_of_frontier_segment
        (hnotFresh := hnotFresh) (S := S)
        (.inl parent) hinessential.1 parent (fun _ hx ↦ hx) hfinish ht
      have hstartOutside := L.splitGroundedFresh_mem_parent_not_mem_reserved
        (hnotFresh := hnotFresh) (S := S)
        (.inl parent) hinessential.1 hne parent.start_mem_support
      have hstartAllowed : ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a parent.start :=
        L.splitGroundedFresh_root_outside_reserved_avoids_reserved
          (hnotFresh := hnotFresh) (S := S)
          hstartOutside ⟨parent.start, hstart, .refl⟩
      have hfinishAllowed : ¬ ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a parent.finish := by
        rintro ⟨a, ha, hareach⟩
        apply hboundary
        exact ⟨a, ha.1, by simpa only [hfinish] using hareach⟩
      have hDAllowed : ¬ ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a D.head := by
        rintro ⟨a, ha, haD⟩
        exact hDnot ⟨a, ha.1, haD⟩
      exact .normalized (.inl parent) parent D hfinish hboundary
        (L.splitGroundedFreshRelevant_normalizeDeletedOutcome
          (.inl parent) hinessential.1 parent hstartAllowed hfinishAllowed
          (fun _ hx ↦ hx) (fun _ he ↦ he) D hDAllowed
          (SplitGroundedUnusedRecord.refineDeletedOutcomeRelevantSourceFirst
            outcome))
  | hangingVirtualEscape P hP heq hhang hfirst hnot hboundary escape =>
      exact .hangingVirtualEscape P hP heq hhang hfirst hnot hboundary escape
  | deleted P hP heq segment hstart hinitial hfinish hboundary hsupport
      hedges D hDnot outcome =>
      have hfinishT : segment.finish = t := hfinish.trans heq
      have hne := L.splitGroundedFresh_parent_ne_reserved_of_frontier_segment
        (hnotFresh := hnotFresh) (S := S)
        P.parent P.parent_mem segment
          (hsupport.trans P.support_subset) hfinishT ht
      have hinitialOutside := L.splitGroundedFresh_mem_parent_not_mem_reserved
        (hnotFresh := hnotFresh) (S := S)
        P.parent P.parent_mem hne
          (P.support_subset P.path.initial_mem_support)
      have hinitialAllowed :=
        L.splitGroundedFresh_root_outside_reserved_avoids_reserved
          (hnotFresh := hnotFresh) (S := S)
          hinitialOutside hinitial
      have hstartAllowed : ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a segment.start := by
        simpa only [hstart] using hinitialAllowed
      have hfinishAllowed : ¬ ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a segment.finish := by
        rintro ⟨a, ha, hareach⟩
        apply hboundary
        exact ⟨a, ha.1, by simpa only [hfinishT] using hareach⟩
      have hDAllowed : ¬ ∃ a ∈ AllNormAllowedSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllNormEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a D.head := by
        rintro ⟨a, ha, haD⟩
        exact hDnot ⟨a, ha.1, haD⟩
      exact .normalized P.parent segment D hfinishT hboundary
        (L.splitGroundedFreshRelevant_normalizeDeletedOutcome
          P.parent P.parent_mem segment hstartAllowed hfinishAllowed
          (hsupport.trans P.support_subset) (hedges.trans P.edges_subset)
          D hDAllowed
          (SplitGroundedUnusedRecord.refineDeletedOutcomeRelevantSourceFirst
            outcome))

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantAllSourceFailureAt.normalize

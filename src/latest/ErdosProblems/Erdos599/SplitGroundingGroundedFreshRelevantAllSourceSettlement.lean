/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantAllSourceOutcome
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantTerminalSettlement

/-!
# Exact settlement of a full-source relevant-frontier failure

The full-source scan remembers the original failed source-first frontier
point.  This file feeds its control and deleted-edge branches into the
native-frontier terminal normalizers without losing that point.  In
particular, the output is indexed by the original `t`; intermediate rooted
request exits or frontier points remain exchange data and are not counted as
coverage of `t`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev SettlementInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev SettlementControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev SettlementRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev SettlementFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev SettlementEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (SettlementControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (SettlementFrontier (L := L) (hL := hL) (S := S))

/-- Exact terminal settlement indexed by the original failed frontier point.
Every constructor retains its original all-source nonrooted certificate.
The backward and forward constructors additionally carry the complete
same-parent/finish ancestry produced by `terminalProgress`. -/
inductive SplitGroundedFreshRelevantAllSourceSettlementAt (t : V) : Prop
  | control
      (c : ControlRequest (SettlementInput (L := L) (hL := hL)) S.cut)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a c.1)
      (origin : L.SplitGroundedFreshRelevantAllSourceControlOriginAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) t c)
      (normalization : L.SplitGroundedFreshRelevantControlNormalizationAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) c)
  | backward
      (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
      (D : LastDeletedHead p
        (SettlementEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (finish_eq : p.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (data : L.SplitGroundedFreshRelevantBackwardNormalizationAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) parent p D)
      (progress : L.SplitGroundedFreshRelevantBackwardProgressResult
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) data.state)
  | forwardSplice
      (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
      (D : LastDeletedHead p
        (SettlementEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (finish_eq : p.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (data : L.SplitGroundedFreshRelevantForwardNormalizationAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) parent p D)
      (progress : L.SplitGroundedFreshRelevantBackwardProgressResult
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) data.state)
  | boundaryDeparture
      (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
      (D : LastDeletedHead p
        (SettlementEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (finish_eq : p.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (tail : V) (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (residual : (tail, D.head) ∈ residualLadderEdges
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S)
      (sourcePath : FinitePath Gamma.graph)
      (source_start : sourcePath.start ∈ Gamma.source)
      (source_finish : sourcePath.finish = tail)
      (source_roof : sourcePath.support ⊆
        (SettlementInput (L := L) (hL := hL)).roofRegion)
      (tail_relevant : tail ∈ L.splitGroundedRelevantBB hL.legal S.cut)
      (source_first : ∀ x ∈ sourcePath.walk.support.dropLast,
        x ∉ L.splitGroundedRelevantBB hL.legal S.cut)
  | hangingVirtualEscape
      (P : (SettlementInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (SettlementInput (L := L) (hL := hL)) S.cut P = t)
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a P.path.initial)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SettlementEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (escape : SplitGroundedRelevantVirtualEscape L hL.legal S.cut t)

/-- Settle every normalized full-source failure while retaining its original
frontier endpoint and all concrete control/fragment ancestry. -/
theorem SplitGroundedFreshRelevantAllSourceNormalizedFailureAt.settle
    {t : V}
    (F : L.SplitGroundedFreshRelevantAllSourceNormalizedFailureAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) t) :
    L.SplitGroundedFreshRelevantAllSourceSettlementAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) t := by
  cases F with
  | control c hboundary hnot origin resolution =>
      exact .control c hboundary hnot origin
        (resolution.normalizeFreshRelevant c)
  | normalized parent p D hfinish hboundary data =>
      cases data with
      | backward data =>
          exact .backward parent p D hfinish hboundary data
            data.result.terminalProgress
      | forwardSplice data =>
          exact .forwardSplice parent p D hfinish hboundary data
            data.result.terminalProgress
      | boundaryDeparture tail hin hresidual sourcePath hsource hsourceFinish
          hroof hrelevant hfirst =>
          exact .boundaryDeparture parent p D hfinish hboundary tail hin
            hresidual sourcePath hsource hsourceFinish hroof hrelevant hfirst
  | hangingVirtualEscape P hP hpoint hhang hinitial hinitialNot hboundary
      escape =>
      exact .hangingVirtualEscape P hP hpoint hhang hinitial hinitialNot
        hboundary escape

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantAllSourceNormalizedFailureAt.settle

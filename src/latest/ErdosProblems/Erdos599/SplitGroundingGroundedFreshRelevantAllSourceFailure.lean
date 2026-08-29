/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantCutAvoidingFailure
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingCanonical
import ErdosProblems.Erdos599.GroundingStoppedRootReduction
import ErdosProblems.Erdos599.SplitGroundingGroundedReservedRouteDisjoint

/-!
# All-source failures at the relevant stopping frontier

The final source-faithful switch keeps the reserved grounded record as an
inessential component.  Its reachability analysis must therefore begin at
the whole ambient source, rather than at `source \ {reserved}`.  This file
repeats the source-first finite scan with that exact root set.

The useful difference from the omitted-source dispatcher is that a source
endpoint is impossible by reflexivity.  Every remaining failure retains a
concrete unrooted control, a last deleted incoming edge on a finite parent
segment, or the genuine hanging virtual-forward alternative.
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

private abbrev AllSourceInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev AllSourceIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev AllSourceControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev AllSourceRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev AllSourceFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev AllSourceEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (AllSourceIndexed (L := L) (hL := hL) (hground := hground)) S
    (AllSourceControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (AllSourceFrontier (L := L) (hL := hL) (S := S))

/-- A full-source root of a vertex outside the reserved record already
starts at an allowed source.  Forward closure of the actual reserved record
is the only input: no endpoint-specific frontier fact is used. -/
theorem splitGroundedFresh_root_outside_reserved_avoids_reserved
    {x : V}
    (hxOutside : x ∉
      (AllSourceRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)).record.support)
    (hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a x) :
    ∃ a ∈ Gamma.source \ {
        (AllSourceRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)).record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a x := by
  obtain ⟨a, haSource, hax⟩ := hroot
  let R := L.splitGroundedFreshAvoidingBaseUnusedRecord
    hL hground hnotFresh S
  have haNe : a ≠ R.record.initial := by
    intro ha
    subst a
    apply hxOutside
    simpa only [AllSourceRecord,
      splitGroundedFreshAvoidingCanonicalUnusedRecord,
      SplitGroundedUnusedRecord.forReservedControlsFrom] using
      R.reservedSwitched_reachable_mem_record
        (L.splitGroundedFreshAvoidingBaseUnusedRecord_trace_disjoint
          hL hground hnotFresh S)
        (AllSourceFrontier (L := L) (hL := hL) (S := S)) hax
  refine ⟨a, ⟨haSource, ?_⟩, hax⟩
  simpa only [Set.mem_singleton_iff, AllSourceRecord,
    splitGroundedFreshAvoidingCanonicalUnusedRecord,
    SplitGroundedUnusedRecord.forReservedControlsFrom] using haNe

/-- Concrete provenance of a control encountered while resolving an
unrooted source-first frontier point.  The control may be the frontier point
itself, a deleted head on a rooted finite segment ending there, or the
initial vertex of the relevant fragment whose blocker is the frontier
point.  In particular, no constructor forgets the path from the control to
the original failed point. -/
inductive SplitGroundedFreshRelevantAllSourceControlOriginAt
    (t : V)
    (c : ControlRequest (AllSourceInput (L := L) (hL := hL)) S.cut) : Prop
  | directOld
      (old : PopularGroundingBridge.oldRequests
        (AllSourceInput (L := L) (hL := hL)) S.cut)
      (control_eq : c = oldRequestControl old)
      (value_eq : c.1 = t)
  | deleted
      (parent : Gamma.DPath)
      (parent_mem : parent ∈ L.limitWarp)
      (segment : FinitePath Gamma.graph)
      (segment_start_rooted : ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a segment.start)
      (segment_finish : segment.finish = t)
      (segment_support : segment.support ⊆ parent.support)
      (segment_edges : segment.edgeSet ⊆ parent.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (AllSourceEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (tail : V)
      (incoming_mem : (tail, lastDeleted.head) ∈ segment.edgeSet)
      (cut_edge : (tail, lastDeleted.head) ∈
        GroundingCut.CE (AllSourceInput (L := L) (hL := hL)) S.cut)
      (control_eq : c.1 = lastDeleted.head)
  | fragmentOld
      (P : (AllSourceInput (L := L) (hL := hL)).Fragment)
      (fragment_mem : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (blocker_eq : GroundingCut.blockingPoint
        (AllSourceInput (L := L) (hL := hL)) S.cut P = t)
      (old : PopularGroundingBridge.oldRequests
        (AllSourceInput (L := L) (hL := hL)) S.cut)
      (control_eq : c = oldRequestControl old)
      (value_eq : c.1 = P.path.initial)
  | fragmentEdge
      (P : (AllSourceInput (L := L) (hL := hL)).Fragment)
      (fragment_mem : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (blocker_eq : GroundingCut.blockingPoint
        (AllSourceInput (L := L) (hL := hL)) S.cut P = t)
      (edge : V × V)
      (cut_edge : edge ∈
        GroundingCut.CE (AllSourceInput (L := L) (hL := hL)) S.cut)
      (parent_edge : edge ∈ P.parent.edgeSet)
      (head_eq : edge.2 = P.path.initial)
      (control_eq : c.1 = P.path.initial)

/-- In the deleted-segment origin, a root of the encountered control reaches
the original failed frontier point through the surviving suffix stored by
`LastDeletedHead`.  This is the exact suffix-survival bridge used after a
component exchange roots the deleted head. -/
theorem splitGroundedFreshRelevant_deletedControl_root_reaches_boundary
    {t : V}
    (segment : FinitePath Gamma.graph)
    (D : LastDeletedHead segment
      (AllSourceEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)))
    (segment_finish : segment.finish = t)
    {c : ControlRequest (AllSourceInput (L := L) (hL := hL)) S.cut}
    (control_eq : c.1 = D.head)
    (hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a c.1) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  have hhead : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a D.head := by
    simpa only [control_eq] using hroot
  obtain ⟨a, ha, haHead⟩ := hhead
  refine ⟨a, ha, haHead.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ AllSourceEdges
        (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
      D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ AllSourceEdges
        (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.suffix.walk
  simpa only [D.suffix_start, D.suffix_finish, segment_finish] using hsuffix

/-- Exact residual data for a point of the source-first frontier which is
not reachable from *any* ambient source in the canonical stopped relation. -/
inductive SplitGroundedFreshRelevantAllSourceFailureAt (t : V) : Prop
  | control
      (c : ControlRequest (AllSourceInput (L := L) (hL := hL)) S.cut)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a c.1)
      (origin : L.SplitGroundedFreshRelevantAllSourceControlOriginAt
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) t c)
  | finite
      (ht : t ∈ (AllSourceInput (L := L) (hL := hL)).finiteSource)
      (parent : FinitePath Gamma.graph)
      (chosen : L.chosen (L.finiteTerminalIndex ⟨t, ht⟩) =
        some (.inl parent : Gamma.DPath))
      (parent_finish : parent.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (parent_start : parent.start ∈ Gamma.source)
      (parent_inessential : (.inl parent : Gamma.DPath) ∈
        Gamma.inessentialPaths L.limitWarp)
      (lastDeleted : LastDeletedHead parent
        (AllSourceEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a lastDeleted.head)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := AllSourceControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (AllSourceFrontier (L := L) (hL := hL) (S := S))
        (.inl parent : Gamma.DPath) parent lastDeleted)
  | hangingVirtualEscape
      (P : (AllSourceInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (AllSourceInput (L := L) (hL := hL)) S.cut P = t)
      (parent_hanging : P.IsHanging)
      (initial_eq : P.path.initial = P.parent.initial)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a P.path.initial)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (escape : SplitGroundedRelevantVirtualEscape L hL.legal S.cut t)
  | deleted
      (P : (AllSourceInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (AllSourceInput (L := L) (hL := hL)) S.cut P = t)
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (initial_rooted : ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a P.path.initial)
      (segment_finish : segment.finish =
        GroundingCut.blockingPoint
          (AllSourceInput (L := L) (hL := hL)) S.cut P)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (AllSourceEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a lastDeleted.head)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S)
        (K := AllSourceControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (AllSourceFrontier (L := L) (hL := hL) (S := S))
        P.parent segment lastDeleted)

private theorem allSourceControlFailure_of_cutResolution
    {t : V} {parent : Gamma.DPath} {p : FinitePath Gamma.graph}
    (hparent : parent ∈ L.limitWarp)
    (hstart : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a p.start)
    (hfinish : p.finish = t)
    (hboundary : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t)
    (hsupport : p.support ⊆ parent.support)
    (hedges : p.edgeSet ⊆ parent.edgeSet)
    {D : LastDeletedHead p
      (AllSourceEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))}
    (hDnot : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a D.head)
    (tail : V) (_hin : (tail, D.head) ∈ p.edgeSet)
    (hcut : (tail, D.head) ∈
      GroundingCut.CE (AllSourceInput (L := L) (hL := hL)) S.cut) :
    L.SplitGroundedFreshRelevantAllSourceFailureAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) t := by
  let request : Request (AllSourceInput (L := L) (hL := hL)) S.cut :=
    .inr ⟨(tail, D.head), (GroundingCut.mem_CE.mp hcut).1⟩
  let c : ControlRequest (AllSourceInput (L := L) (hL := hL)) S.cut :=
    ⟨D.head, ⟨request, rfl⟩⟩
  exact .control c hboundary (by simpa only [c] using hDnot)
    (.deleted parent hparent p hstart hfinish hsupport hedges D tail _hin
      hcut (by rfl))

/-- Pointwise all-source scan at the actual canonical stopping frontier. -/
theorem splitGroundedFreshRelevantAllSourceFailureAt
    (hC : Popular.IsSeparator
      (AllSourceInput (L := L) (hL := hL)).lambda S.cut)
    {t : V}
    (ht : t ∈ AllSourceFrontier (L := L) (hL := hL) (S := S))
    (hnot : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t) :
    L.SplitGroundedFreshRelevantAllSourceFailureAt
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) t := by
  let R := AllSourceRecord (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  obtain ⟨Q, hQsource, hQfinish, hQroof, hQboundary, hQfirst⟩ := ht
  cases L.splitGroundedRelevantBBPointOwner_of_mem hQboundary with
  | finiteSource hfinite hcut =>
      obtain ⟨p, hchosen, hpFinish, hpStart, hpInessential⟩ :=
        R.exists_cutFiniteSource_parent_with_allowed_root hfinite hcut
      have hpRoot : ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ AllSourceEdges
              (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S)) a p.start :=
        ⟨p.start, hpStart.1, .refl⟩
      have hpNot : ¬ ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ AllSourceEdges
              (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S)) a p.finish := by
        simpa only [hpFinish] using hnot
      obtain ⟨D, hDnot⟩ := exists_unrootedLastDeletedHead p hpRoot hpNot
      have hparent : (.inl p : Gamma.DPath) ∈
          (AllSourceInput (L := L) (hL := hL)).ladder.paths :=
        hpInessential.1
      cases L.splitGroundedRelevantDeletedResolutionAt
          (AllSourceFrontier (L := L) (hL := hL) (S := S))
          (.inl p : Gamma.DPath) hparent p (fun _ hx ↦ hx)
            (fun _ he ↦ he) D with
      | control tail hin hCE =>
          exact allSourceControlFailure_of_cutResolution hparent hpRoot
            hpFinish hnot (fun _ hx ↦ hx) (fun _ he ↦ he)
            hDnot tail hin hCE
      | geometric outcome =>
          exact .finite hfinite p hchosen hpFinish hnot hpStart.1
            hpInessential D hDnot outcome
  | oldControl old value_eq =>
      let c := oldRequestControl old
      exact .control c hnot (by
        simpa only [c, oldRequestControl_val, value_eq] using hnot)
        (.directOld old rfl
          (by simpa only [c, oldRequestControl_val] using value_eq))
  | blocking P hP point_eq point_mem_support =>
      by_cases hinitial : ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ AllSourceEdges
              (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S)) a P.path.initial
      · obtain ⟨p, hpStart, hpFinish, hpSupport, hpEdges⟩ :=
          GroundingPathPrefix.exists_initialFinitePrefix P.path
            (point_eq ▸ point_mem_support)
        have hpRoot : ∃ a ∈ Gamma.source,
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈ AllSourceEdges
                (L := L) (hL := hL) (hground := hground)
                  (hnotFresh := hnotFresh) (S := S)) a p.start := by
          simpa only [hpStart] using hinitial
        have hpNot : ¬ ∃ a ∈ Gamma.source,
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈ AllSourceEdges
                (L := L) (hL := hL) (hground := hground)
                  (hnotFresh := hnotFresh) (S := S)) a p.finish := by
          simpa only [hpFinish, point_eq] using hnot
        obtain ⟨D, hDnot⟩ := exists_unrootedLastDeletedHead p hpRoot hpNot
        cases L.splitGroundedRelevantDeletedResolutionAt
            (AllSourceFrontier (L := L) (hL := hL) (S := S))
            P.parent P.parent_mem p (hpSupport.trans P.support_subset)
              (hpEdges.trans P.edges_subset) D with
        | control tail hin hCE =>
            exact allSourceControlFailure_of_cutResolution
              P.parent_mem hpRoot (hpFinish.trans point_eq) hnot
              (hpSupport.trans P.support_subset)
              (hpEdges.trans P.edges_subset) hDnot tail hin hCE
        | geometric outcome =>
            exact .deleted P hP point_eq p hpStart hinitial hpFinish hnot
              hpSupport hpEdges D hDnot outcome
      · rcases
          GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
            (AllSourceInput (L := L) (hL := hL)) S.cut P
              ((L.splitGroundedRelevantG0_subset_legacyG0
                hL.legal S.cut hP).1) with
          hfirst | ⟨e, heCE, heParent, heHead⟩
        · rcases PopularAuxiliary.grounded_or_hanging Gamma P.parent with
              hgrounded | hhanging
          · exfalso
            apply hinitial
            exact ⟨P.path.initial, hfirst ▸ hgrounded, .refl⟩
          · by_cases hescape : P.MeetsEscape
                (AllSourceInput (L := L) (hL := hL)) S.cut
            · have hblock : GroundingCut.blockingPoint
                  (AllSourceInput (L := L) (hL := hL)) S.cut P = Q.finish :=
                point_eq.trans hQfinish.symm
              rcases
                  L.splitGroundedRelevant_sourceFirst_escapeBlocker_source_or_virtual
                    hL.legal S.cut hC Q hQsource hQroof
                      (hfirst := fun {_} hx ↦ hQfirst _ hx)
                      P hP hblock hescape with hsource | hvirtual
              · exfalso
                apply hnot
                exact ⟨t, hQfinish ▸ hsource, .refl⟩
              · exact .hangingVirtualEscape P hP point_eq hhanging hfirst
                  hinitial hnot (hQfinish ▸ hvirtual.some)
            · have hessential :=
                  L.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
                    hL.legal S.cut P hP hescape
              have hCV :=
                splitGrounded_hangingEssentialFirst_notEscape_initial_mem_CV
                  P hessential hhanging hfirst hescape
              rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit
                  hCV with hfinite | ⟨request, hrequest, hexit⟩
              · have htarget :=
                    splitGrounded_hangingEssential_initial_mem_targetMarkers
                      (hL := hL) P hessential hhanging
                exact (splitGrounded_finiteSource_not_mem_targetMarkers
                  hfinite (hfirst ▸ htarget)).elim
              · cases request with
                | inl old =>
                    let c := oldRequestControl old
                    exact .control c hnot (by
                      simpa only [c, requestExit, ← hexit,
                        oldRequestControl_val] using hinitial)
                      (.fragmentOld P hP point_eq old rfl (by
                        simpa only [c, requestExit, ← hexit,
                          oldRequestControl_val]))
                | inr edge => cases hrequest
        · let request : Request
              (AllSourceInput (L := L) (hL := hL)) S.cut :=
            .inr ⟨e, (GroundingCut.mem_CE.mp heCE).1⟩
          let c : ControlRequest
              (AllSourceInput (L := L) (hL := hL)) S.cut :=
            ⟨e.2, ⟨request, rfl⟩⟩
          exact .control c hnot (by simpa only [c, heHead] using hinitial)
            (.fragmentEdge P hP point_eq e heCE heParent heHead
              (by simp only [c, heHead]))

/-- Either the complete source-first frontier is rooted from the whole
ambient source, or one exact all-source failure remains. -/
theorem splitGroundedFreshRelevantAllSource_rooted_or_failure
    (hC : Popular.IsSeparator
      (AllSourceInput (L := L) (hL := hL)).lambda S.cut) :
    (∀ t ∈ AllSourceFrontier (L := L) (hL := hL) (S := S),
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t) ∨
      ∃ t ∈ AllSourceFrontier (L := L) (hL := hL) (S := S),
        L.SplitGroundedFreshRelevantAllSourceFailureAt
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) t := by
  classical
  by_cases hall : ∀ t ∈ AllSourceFrontier
      (L := L) (hL := hL) (S := S),
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ AllSourceEdges
          (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨t, ht, hnot⟩ := hall
    have hnot' : ¬ ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ AllSourceEdges
            (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a t := by
      rintro ⟨a, ha, hareach⟩
      exact hnot a ha hareach
    exact ⟨t, ht,
      L.splitGroundedFreshRelevantAllSourceFailureAt hC ht hnot'⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevantAllSourceFailureAt
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevantAllSource_rooted_or_failure

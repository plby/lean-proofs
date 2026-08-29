/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSourceFirstNormalization
import ErdosProblems.Erdos599.GroundingFragmentPredecessor

/-!
# Premise-free source-first split grounding normalization

The earlier source-first normal form discharged represented-cut edges with
a universal control-root hypothesis.  At a nonempty stopping frontier that
hypothesis is not supplied by the pre-stopped control theorem: stopping can
change both the active requests and their retained prefixes.

This file keeps every failed old control as positive data instead.  Thus the
result is total for an arbitrary honest controls package at the actual final
frontier.  All other cases retain their concrete deletion or virtual-escape
geometry, and the success side is an ambient hindrance.
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

private abbrev SourceFirstTotalInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev SourceFirstTotalIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev SourceFirstTotalEdges (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (SourceFirstTotalIndexed (L := L) (hL := hL) (hground := hground))
      S K T

/-- A last deleted incoming edge either exposes the exact unrooted control
at a represented cut edge, or has the already concrete geometric outcome. -/
inductive SplitGroundedRelevantDeletedResolutionAt
    (T : Set V) (parent : Gamma.DPath) (p : FinitePath Gamma.graph)
    (D : LastDeletedHead p
      (SourceFirstTotalEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T)) : Prop
  | control
      (tail : V)
      (incoming_mem : (tail, D.head) ∈ p.edgeSet)
      (cut_edge : (tail, D.head) ∈
        GroundingCut.CE (SourceFirstTotalInput (L := L) (hL := hL)) S.cut)
  | geometric
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T parent p D)

/-- Classify a deleted edge without assuming its represented-cut control is
already rooted. -/
theorem splitGroundedRelevantDeletedResolutionAt
    (T : Set V) (parent : Gamma.DPath)
    (hparent : parent ∈
      (SourceFirstTotalInput (L := L) (hL := hL)).ladder.paths)
    (p : FinitePath Gamma.graph)
    (hpSupport : p.support ⊆ parent.support)
    (hpEdges : p.edgeSet ⊆ parent.edgeSet)
    (D : LastDeletedHead p
      (SourceFirstTotalEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T)) :
    SplitGroundedRelevantDeletedResolutionAt
      (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
        T parent p D := by
  have hpFamily : p.edgeSet ⊆
      (SourceFirstTotalInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨parent, hparent, hpEdges he⟩
  rcases D.exists_classified_deletedIncomingAt_split K T hpFamily with
      hcut | hbackward | hconflict | hboundary
  · obtain ⟨tail, htail, hcut⟩ := hcut
    exact .control tail htail hcut
  · obtain ⟨tail, htail, hbackward⟩ := hbackward
    exact .geometric
      (L.splitGroundedReducedDeletedOutcomeAt T parent p hparent
        hpSupport hpEdges D (Or.inl ⟨tail, htail, hbackward⟩))
  · obtain ⟨tail, htail, hconflict⟩ := hconflict
    exact .geometric
      (L.splitGroundedReducedDeletedOutcomeAt T parent p hparent
        hpSupport hpEdges D
          (Or.inr (Or.inl ⟨tail, htail, hconflict⟩)))
  · obtain ⟨tail, htail, hresidual, htailT⟩ := hboundary
    exact .geometric
      (L.splitGroundedReducedDeletedOutcomeAt T parent p hparent
        hpSupport hpEdges D
          (Or.inr (Or.inr ⟨tail, htail, hresidual, htailT⟩)))

/-- Premise-free residual alternatives at one unrooted source-first point.
The `control` constructor is the exact replacement for the unavailable
universal stopped-control rooting hypothesis. -/
inductive SplitGroundedRelevantSourceFirstTotalFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (t : V) : Prop
  | control
      (c : ControlRequest (SourceFirstTotalInput (L := L) (hL := hL)) S.cut)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a c.1)
  | finite
      (ht : t ∈ (SourceFirstTotalInput (L := L) (hL := hL)).finiteSource)
      (parent : FinitePath Gamma.graph)
      (chosen : L.chosen (L.finiteTerminalIndex ⟨t, ht⟩) =
        some (.inl parent : Gamma.DPath))
      (parent_finish : parent.finish = t)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a t)
      (parent_start : parent.start ∈ Gamma.source \ {R.record.initial})
      (parent_inessential : (.inl parent : Gamma.DPath) ∈
        Gamma.inessentialPaths L.limitWarp)
      (lastDeleted : LastDeletedHead parent
        (SourceFirstTotalEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a lastDeleted.head)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T (.inl parent : Gamma.DPath) parent lastDeleted)
  | sourceEndpoint
      (endpoint_eq : t = R.record.initial)
  | virtualEscape
      (P : (SourceFirstTotalInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (SourceFirstTotalInput (L := L) (hL := hL)) S.cut P = t)
      (origin :
        (P.parent = R.record ∧ P.path.initial = P.parent.initial) ∨
        (P.IsHanging ∧ P.path.initial = P.parent.initial))
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
      (escape : SplitGroundedRelevantVirtualEscape L hL.legal S.cut t)
  | deleted
      (P : (SourceFirstTotalInput (L := L) (hL := hL)).Fragment)
      (hP : P ∈ L.splitGroundedRelevantG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (SourceFirstTotalInput (L := L) (hL := hL)) S.cut P = t)
      (segment : FinitePath Gamma.graph)
      (segment_start : segment.start = P.path.initial)
      (initial_rooted : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a P.path.initial)
      (segment_finish : segment.finish = GroundingCut.blockingPoint
        (SourceFirstTotalInput (L := L) (hL := hL)) S.cut P)
      (boundary_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a t)
      (segment_support : segment.support ⊆ P.path.support)
      (segment_edges : segment.edgeSet ⊆ P.path.edgeSet)
      (lastDeleted : LastDeletedHead segment
        (SourceFirstTotalEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T))
      (head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a lastDeleted.head)
      (outcome : SplitGroundedReducedDeletedOutcomeAt
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K)
          T P.parent segment lastDeleted)

namespace SplitGroundedUnusedRecord

/-- A finite allowed-source path whose terminal is not rooted in the
native stopped relation has a last deleted incoming edge whose head is
still unrooted.  This is the reusable descent step for selected backward
owners at a nonempty frontier. -/
theorem exists_unrootedLastDeletedHead_sourceFirstTotal
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a p.start)
    (hfinish : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a p.finish) :
    ∃ D : LastDeletedHead p
        (SourceFirstTotalEdges (L := L) (hL := hL) (hground := hground)
          (S := S) (K := K) T),
      ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet,
      e ∉ SourceFirstTotalEdges (L := L) (hL := hL)
        (hground := hground) (S := S) (K := K) T := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hareach⟩ := hstart
    refine ⟨a, ha, hareach.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T)
    · intro x y hxy
      by_contra hxyE
      exact hnone ⟨(x, y), hxy, hxyE⟩
    · exact Alternating.Walk.reflTransGen_edgeSet p.walk
  let D := (exists_lastDeletedHead p hdeleted).some
  refine ⟨D, ?_⟩
  rintro ⟨a, ha, haD⟩
  apply hfinish
  refine ⟨a, ha, haD.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T)
      D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
        (L := L) (hL := hL) (hground := hground) (S := S) (K := K) T)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

private theorem sourceFirstTotal_endpoint_eq_reserved
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    (htSource : t ∈ Gamma.source)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t) :
    t = R.record.initial := by
  by_contra hne
  apply hnot
  exact ⟨t, ⟨htSource, by simpa only [Set.mem_singleton_iff]⟩, .refl⟩

private theorem controlFailure_of_cutResolution
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    {p : FinitePath Gamma.graph}
    {D : LastDeletedHead p
      (SourceFirstTotalEdges (L := L) (hL := hL) (hground := hground)
        (S := S) (K := K) T)}
    (hDnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a D.head)
    (tail : V) (_hin : (tail, D.head) ∈ p.edgeSet)
    (hcut : (tail, D.head) ∈
      GroundingCut.CE (SourceFirstTotalInput (L := L) (hL := hL)) S.cut) :
    SplitGroundedRelevantSourceFirstTotalFailureAt R T t := by
  let request : Request
      (SourceFirstTotalInput (L := L) (hL := hL)) S.cut :=
    .inr ⟨(tail, D.head), (GroundingCut.mem_CE.mp hcut).1⟩
  let c : ControlRequest
      (SourceFirstTotalInput (L := L) (hL := hL)) S.cut :=
    ⟨D.head, ⟨request, rfl⟩⟩
  exact .control c (by simpa only [c] using hDnot)

/-- Total normalization of one unrooted source-first relevant point, with
no control-root premise. -/
theorem relevantSourceFirstBBTotalFailureAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V) {t : V}
    (hC : Popular.IsSeparator
      (SourceFirstTotalInput (L := L) (hL := hL)).lambda S.cut)
    (ht : t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
          (L := L) (hL := hL) (hground := hground)
            (S := S) (K := K) T) a t) :
    SplitGroundedRelevantSourceFirstTotalFailureAt R T t := by
  obtain ⟨Q, hQsource, hQfinish, hQroof, hQboundary, hQfirst⟩ := ht
  cases L.splitGroundedRelevantBBPointOwner_of_mem hQboundary with
  | finiteSource hfinite hcut =>
      obtain ⟨p, hchosen, hpFinish, hpStart, hpInessential⟩ :=
        R.exists_cutFiniteSource_parent_with_allowed_root hfinite hcut
      have hpRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
              (L := L) (hL := hL) (hground := hground)
                (S := S) (K := K) T) a p.start :=
        ⟨p.start, hpStart, .refl⟩
      have hpNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
              (L := L) (hL := hL) (hground := hground)
                (S := S) (K := K) T) a p.finish := by
        simpa only [hpFinish] using hnot
      obtain ⟨D, hDnot⟩ :=
        R.exists_unrootedLastDeletedHead_sourceFirstTotal T p hpRoot hpNot
      have hparent : (.inl p : Gamma.DPath) ∈
          (SourceFirstTotalInput (L := L) (hL := hL)).ladder.paths :=
        hpInessential.1
      have hpSupport : p.support ⊆
          DirectedPath.Path.support (.inl p : Gamma.DPath) := by
        intro x hx
        exact hx
      have hpEdges : p.edgeSet ⊆
          DirectedPath.Path.edgeSet (.inl p : Gamma.DPath) := by
        intro e he
        exact he
      cases L.splitGroundedRelevantDeletedResolutionAt T
          (.inl p : Gamma.DPath) hparent p hpSupport hpEdges D with
      | control tail hin hCE =>
          exact R.controlFailure_of_cutResolution T hDnot tail hin hCE
      | geometric outcome =>
          exact .finite hfinite p hchosen hpFinish hnot hpStart hpInessential
            D hDnot outcome
  | oldControl old value_eq =>
      let c := oldRequestControl old
      exact .control c (by
        simpa only [c, oldRequestControl_val, value_eq] using hnot)
  | blocking P hP point_eq point_mem_support =>
      by_cases hinitial : ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
              (L := L) (hL := hL) (hground := hground)
                (S := S) (K := K) T) a P.path.initial
      · obtain ⟨p, hpStart, hpFinish, hpSupport, hpEdges⟩ :=
          GroundingPathPrefix.exists_initialFinitePrefix P.path
            (point_eq ▸ point_mem_support)
        have hpRoot : ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
                (L := L) (hL := hL) (hground := hground)
                  (S := S) (K := K) T) a p.start := by
          simpa only [hpStart] using hinitial
        have hpNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
                (L := L) (hL := hL) (hground := hground)
                  (S := S) (K := K) T) a p.finish := by
          simpa only [hpFinish, point_eq] using hnot
        obtain ⟨D, hDnot⟩ :=
          R.exists_unrootedLastDeletedHead_sourceFirstTotal T p hpRoot hpNot
        cases L.splitGroundedRelevantDeletedResolutionAt T P.parent P.parent_mem
            p (hpSupport.trans P.support_subset)
              (hpEdges.trans P.edges_subset) D with
        | control tail hin hCE =>
            exact R.controlFailure_of_cutResolution T hDnot tail hin hCE
        | geometric outcome =>
            exact .deleted P hP point_eq p hpStart hinitial hpFinish hnot
              hpSupport hpEdges D hDnot outcome
      · rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
          (SourceFirstTotalInput (L := L) (hL := hL)) S.cut P
            ((L.splitGroundedRelevantG0_subset_legacyG0 hL.legal S.cut hP).1) with
        hfirst | ⟨e, heCE, _heParent, heHead⟩
        · have origin :
              (P.parent = R.record ∧ P.path.initial = P.parent.initial) ∨
              (P.IsHanging ∧ P.path.initial = P.parent.initial) := by
            rcases PopularAuxiliary.grounded_or_hanging Gamma P.parent with
                hgrounded | hhanging
            · by_cases hparent : P.parent = R.record
              · exact Or.inl ⟨hparent, hfirst⟩
              · exfalso
                apply hinitial
                refine ⟨P.path.initial, ?_, .refl⟩
                rw [hfirst]
                refine ⟨hgrounded, ?_⟩
                intro heq
                apply hparent
                exact Alternating.DWeb.IsWarp.eq_of_mem_support
                  (hL.legal.warpStages (Ladder.finalStage kappa))
                  P.parent_mem R.limit_inessential.1
                  P.parent.initial_mem_support
                    (Set.mem_singleton_iff.mp heq ▸ R.record.initial_mem_support)
            · exact Or.inr ⟨hhanging, hfirst⟩
          by_cases hescape : P.MeetsEscape
              (SourceFirstTotalInput (L := L) (hL := hL)) S.cut
          · have hblock : GroundingCut.blockingPoint
                (SourceFirstTotalInput (L := L) (hL := hL)) S.cut P =
                Q.finish := point_eq.trans hQfinish.symm
            rcases L.splitGroundedRelevant_sourceFirst_escapeBlocker_source_or_virtual
                hL.legal S.cut hC Q hQsource hQroof
                  (hfirst := fun {_} hx ↦ hQfirst _ hx)
                  P hP hblock hescape with hsource | hvirtual
            · exact .sourceEndpoint
                (R.sourceFirstTotal_endpoint_eq_reserved T
                  (hQfinish ▸ hsource) hnot)
            · exact .virtualEscape P hP point_eq origin hinitial
                (hQfinish ▸ hvirtual.some)
          · have hessential :=
                L.splitGroundedRelevantG0_parent_mem_essentialLadder_of_not_meetsEscape
                  hL.legal S.cut P hP hescape
            rcases origin with hreserved | hhanging
            · rw [hreserved.1] at hessential
              exact (R.limit_inessential.2 hessential).elim
            · have hCV :=
                splitGrounded_hangingEssentialFirst_notEscape_initial_mem_CV
                  P hessential hhanging.1 hhanging.2 hescape
              rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit
                  hCV with hfinite | ⟨request, hrequest, hexit⟩
              · have htarget :=
                    splitGrounded_hangingEssential_initial_mem_targetMarkers
                      (hL := hL) P hessential hhanging.1
                exact (splitGrounded_finiteSource_not_mem_targetMarkers
                  hfinite (hhanging.2 ▸ htarget)).elim
              · cases request with
                | inl old =>
                    let c := oldRequestControl old
                    exact .control c (by
                      simpa only [c, requestExit, ← hexit,
                        oldRequestControl_val] using
                        hinitial)
                | inr edge => cases hrequest
        · let request : Request
              (SourceFirstTotalInput (L := L) (hL := hL)) S.cut :=
            .inr ⟨e, (GroundingCut.mem_CE.mp heCE).1⟩
          let c : ControlRequest
              (SourceFirstTotalInput (L := L) (hL := hL)) S.cut :=
            ⟨e.2, ⟨request, rfl⟩⟩
          exact .control c (by simpa only [c, heHead] using hinitial)

end SplitGroundedUnusedRecord

/-- Premise-free source-first separator dispatcher.  It either constructs
the ambient hindrance or exposes one exact native-`T` residual. -/
theorem exists_hindrance_or_splitGroundedRelevantSourceFirstTotalFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hC : Popular.IsSeparator
      (SourceFirstTotalInput (L := L) (hL := hL)).lambda S.cut) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ L.splitGroundedRelevantSourceFirstBB hL.legal S.cut,
        SplitGroundedRelevantSourceFirstTotalFailureAt R
          (L.splitGroundedRelevantSourceFirstBB hL.legal S.cut) t := by
  let T := L.splitGroundedRelevantSourceFirstBB hL.legal S.cut
  by_cases hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a t
  · left
    have houtput :=
      L.splitGroundedAssertion822Output_of_frontierGeometry_withControls
        R T
          ((L.splitGroundedRelevantSourceFirstBB_subset hL.legal S.cut).trans
            (L.splitGroundedRelevantBB_subset_legacyBB hL.legal S.cut))
          (L.splitGroundedRelevantSourceFirstBB_isSeparator hL.legal S.cut hC)
          hroot
    exact exists_hindrance_of_splitGroundedAssertion822Output houtput.some
  · right
    push Not at hroot
    obtain ⟨t, ht, hnot⟩ := hroot
    have hnot' : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ SourceFirstTotalEdges
            (L := L) (hL := hL) (hground := hground)
              (S := S) (K := K) T) a t := by
      rintro ⟨a, ha, hareach⟩
      exact hnot a ha hareach
    exact ⟨t, ht, R.relevantSourceFirstBBTotalFailureAt T hC ht hnot'⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.relevantSourceFirstBBTotalFailureAt
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedRelevantSourceFirstTotalFailure

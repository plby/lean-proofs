/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion822Stationarity
import ErdosProblems.Erdos599.GroundingAssertion818Seed
import ErdosProblems.Erdos599.GroundingErasedSourceGeometry

/-!
# The unused grounded record in Assertion 8.22

The stationary-set subtraction supplies an ordinal which is not merely
absent from the selected index set.  It has a concrete recorded ladder path
and a canonical source of the auxiliary web: the terminal of the record in
the finite case, and its fresh proxy in the ray case.  This file packages
those witnesses and proves that the canonical source is not used by any
member of the strengthened selected warp.

For a proxy source the conclusion is stronger.  No auxiliary edge enters a
proxy, so the unused proxy occurs nowhere on any selected path.  These are
the source-provenance facts needed when the simultaneous switched relation
is followed from an unreached grounded component.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath

namespace DWeb

open Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The concrete record and auxiliary source represented by a grounded
stage which is absent from the strengthened selector's initial indices. -/
structure UnusedGroundedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) where
  stage : Ladder.Stage kappa
  stage_ground : stage ∈ L.phiGround
  stage_unused :
    stage ∉ Popular.initialIndicesOf
      (L.popularAuxiliaryIndexed hL)
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)).paths
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)).starts_in_source
  record : Gamma.DPath
  chosen : L.chosen stage = some record
  grounded : PopularAuxiliary.IsGroundedPath Gamma record
  limit_inessential : record ∈ Gamma.inessentialPaths L.limitWarp
  auxiliarySource :
    (L.popularAuxiliaryInput hL.legal).lambda.source
  source_index :
    (L.popularAuxiliaryIndexed hL).f auxiliarySource = stage
  auxiliarySource_not_mem_cut : auxiliarySource.1 ∉ S.cut
  source_represents :
    (∃ p : FinitePath Gamma.graph,
      record = .inl p ∧ auxiliarySource.1 = .old p.finish) ∨
    (∃ i : L.groundedInfiniteRecords,
      record = i.1 ∧ auxiliarySource.1 = .proxy i)

/-- Turn a particular unused grounded stage into its concrete recorded path
and canonical auxiliary source. -/
theorem exists_unusedGroundedRecord_at
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (a : Ladder.Stage kappa) (haGround : a ∈ L.phiGround)
    (haUnused :
      a ∉ Popular.initialIndicesOf
        (L.popularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)).paths
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)).starts_in_source)
    (haCutSourceUnused :
      a ∉ Popular.initialIndicesOf
        (L.popularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.popularAuxiliaryInput hL.legal).lambda S.cut).paths
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.popularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source) :
    Nonempty (UnusedGroundedRecord L hL S) := by
  have haGroundCopy := haGround
  obtain ⟨p, hchosen, hpGround⟩ := haGround
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨p, hchosen⟩
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  rcases p with p | r
  · have haFinite : a ∈ L.phiFinite := by
      refine ⟨haPhi, ?_⟩
      intro haInfinite
      obtain ⟨q, hq, hqRay⟩ :=
        L.bookkeeping.chosen_isRay_of_mem_phiInfinite
          hL.legal.validBookkeeping haInfinite
      have hqp : q = (.inl p : Gamma.DPath) :=
        Option.some.inj (hq.symm.trans hchosen)
      subst q
      change (some p.finish : Option V) = none at hqRay
      cases hqRay
    let xg : L.groundedFiniteTerminalSet :=
      ⟨p.finish, a, ⟨haGroundCopy, haFinite⟩, .inl p, hchosen, rfl⟩
    let x : L.finiteTerminalSet :=
      ⟨xg.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xg.2⟩
    let source :
        (L.popularAuxiliaryInput hL.legal).lambda.source :=
      ⟨.old x.1,
        ((L.popularAuxiliaryInput hL.legal).mem_lambda_source_old x.1).2
          xg.2⟩
    have hindex :
        (L.popularAuxiliaryIndexed hL).f source = a := by
      change L.finiteTerminalStage x = a
      exact L.finiteTerminalStage_eq hL.legal hchosen rfl x.2
    have hsourceNotCut : source.1 ∉ S.cut := by
      intro hsourceCut
      apply haCutSourceUnused
      rw [← hindex]
      exact GroundingSimultaneousDecode.source_mem_sourceCutWarp_initialIndices
        (L.popularAuxiliaryIndexed hL) S.cut source hsourceCut
    exact ⟨{
      stage := a
      stage_ground := haGroundCopy
      stage_unused := haUnused
      record := .inl p
      chosen := hchosen
      grounded := hpGround
      limit_inessential := hpInessential
      auxiliarySource := source
      source_index := hindex
      auxiliarySource_not_mem_cut := hsourceNotCut
      source_represents := Or.inl ⟨p, rfl, rfl⟩ }⟩
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨haPhi, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : L.groundedInfiniteRecords :=
      ⟨.inr r, ⟨a, ⟨haGroundCopy, haInfinite⟩, hchosen⟩⟩
    let source :
        (L.popularAuxiliaryInput hL.legal).lambda.source :=
      ⟨.proxy i,
        (L.popularAuxiliaryInput hL.legal).mem_lambda_source_proxy i⟩
    have hindex :
        (L.popularAuxiliaryIndexed hL).f source = a := by
      change L.groundedInfiniteStage i = a
      exact L.groundedInfiniteStage_eq hL.legal i hchosen
    have hsourceNotCut : source.1 ∉ S.cut := by
      intro hsourceCut
      apply haCutSourceUnused
      rw [← hindex]
      exact GroundingSimultaneousDecode.source_mem_sourceCutWarp_initialIndices
        (L.popularAuxiliaryIndexed hL) S.cut source hsourceCut
    exact ⟨{
      stage := a
      stage_ground := haGroundCopy
      stage_unused := haUnused
      record := .inr r
      chosen := hchosen
      grounded := hpGround
      limit_inessential := hpInessential
      auxiliarySource := source
      source_index := hindex
      auxiliarySource_not_mem_cut := hsourceNotCut
      source_represents := Or.inr ⟨i, rfl, rfl⟩ }⟩

/-- The stationary subtraction yields a fully decoded unused grounded
record, rather than only an ordinal outside a set. -/
theorem exists_unusedGroundedRecord
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    Nonempty (UnusedGroundedRecord L hL S) := by
  obtain ⟨a, haGround, haUnused, haCutSourceUnused⟩ :=
    L.exists_groundedStage_not_mem_selected_or_cutSourceInitialIndices hL S
  exact L.exists_unusedGroundedRecord_at hL S a haGround haUnused
    haCutSourceUnused

namespace UnusedGroundedRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}

/-- The excluded root is an actual source vertex of the original web. -/
theorem record_initial_mem_source (R : UnusedGroundedRecord L hL S) :
    R.record.initial ∈ Gamma.source :=
  R.grounded

/-- Once the final wave omits the unused record's genuine root, it is
already an ordinary hindrance.  No retained inessential component is
needed for this source-faithful final step. -/
theorem isHindrance_of_record_initial_not_mem_initialSet
    (R : UnusedGroundedRecord L hL S) {W : Set Gamma.DPath}
    (hW : Gamma.IsWave W)
    (hmiss : R.record.initial ∉ Gamma.initialSet W) :
    Gamma.IsHindrance W := by
  refine ⟨hW, ?_⟩
  intro heq
  apply hmiss
  rw [heq]
  exact R.record_initial_mem_source

/-- No selected request path begins at the canonical source of the unused
record. -/
theorem auxiliarySource_ne_strongSelectedPath_start
    (R : UnusedGroundedRecord L hL S)
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    R.auxiliarySource.1 ≠
      (GroundingSimultaneousDecode.strongSelectedPath
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r).start := by
  intro heq
  let P := GroundingSimultaneousDecode.strongSelectedWarp
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S)
  let q := GroundingSimultaneousDecode.strongSelectedPath
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r
  have hqP : q ∈ P.paths := ⟨r, rfl⟩
  apply R.stage_unused
  refine ⟨q, hqP, ?_⟩
  have hs :
      (⟨q.start, P.starts_in_source hqP⟩ :
        (L.popularAuxiliaryInput hL.legal).lambda.source) =
        R.auxiliarySource := by
    apply Subtype.ext
    exact heq.symm
  calc
    (L.popularAuxiliaryIndexed hL).f
        ⟨q.start, P.starts_in_source hqP⟩ =
      (L.popularAuxiliaryIndexed hL).f R.auxiliarySource :=
        congrArg (L.popularAuxiliaryIndexed hL).f hs
    _ = R.stage := R.source_index

/-- In the ray case the unused proxy occurs nowhere on a selected
auxiliary path.  This strengthens endpoint non-use using the fact that no
Lambda arc enters a proxy. -/
theorem proxy_not_mem_strongSelectedPath_support
    (R : UnusedGroundedRecord L hL S)
    (i : L.groundedInfiniteRecords)
    (hsource : R.auxiliarySource.1 = .proxy i)
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    PopularAuxiliary.Input.LambdaVertex.proxy i ∉
      (GroundingSimultaneousDecode.strongSelectedPath
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r).support := by
  intro hi
  let P := GroundingSimultaneousDecode.strongSelectedWarp
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S)
  let q := GroundingSimultaneousDecode.strongSelectedPath
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r
  have hqP : q ∈ P.paths := ⟨r, rfl⟩
  have hqStart : q.start = .proxy i :=
    (L.popularAuxiliaryInput hL.legal).proxy_mem_support_eq_start
      q (P.starts_in_source hqP) hi
  apply R.auxiliarySource_ne_strongSelectedPath_start r
  exact hsource.trans hqStart.symm

/-- No selected decoded request route starts on the limiting-ladder record
chosen at the unused grounded stage.  This is the precise path-level meaning
of the record being *unreached* in the final paragraph after Assertion 8.22:
the simultaneous selector may traverse the record later, but it never consumes
the source occurrence represented by this grounded index. -/
theorem selectedRequestTrace_initial_not_mem_record_support
    (R : UnusedGroundedRecord L hL S)
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    (GroundingErasedDecode.selectedRequestTrace
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) r).initial ∉
      R.record.support := by
  intro hcontact
  obtain ⟨a, parent, _haGround, hchosen, hparentInessential,
    hparentContact, _hparentSource, hindex, _hdescription⟩ :=
      L.selectedRequestTrace_grounded_record_data hL S r
  have hparentRecord : parent = R.record :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      hparentInessential.1 R.limit_inessential.1
      hparentContact hcontact
  have ha : a = R.stage := by
    apply L.bookkeeping.chosen_stage_unique hL.legal.validBookkeeping
    · exact hchosen
    · rw [hparentRecord]
      change L.chosen R.stage = some R.record
      exact R.chosen
  apply R.stage_unused
  let P := GroundingSimultaneousDecode.strongSelectedWarp
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S)
  let q := GroundingSimultaneousDecode.strongSelectedPath
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r
  have hqP : q ∈ P.paths := ⟨r, rfl⟩
  refine ⟨q, hqP, ?_⟩
  exact hindex.symm.trans ha

/-- Two distinct auxiliary sources cannot encode limiting-ladder parents
with the same genuine initial vertex.  Warp disjointness first identifies
the parents, bookkeeping then identifies their stages, and injectivity of
the concrete auxiliary source index finally identifies the sources. -/
theorem record_initial_ne_parent_initial_of_auxiliarySource_ne
    (R : UnusedGroundedRecord L hL S)
    (x : (L.popularAuxiliaryInput hL.legal).lambda.source)
    (a : Ladder.Stage kappa) (parent : Gamma.DPath)
    (hx : x ≠ R.auxiliarySource)
    (hindex : (L.popularAuxiliaryIndexed hL).f x = a)
    (hchosen : L.chosen a = some parent)
    (hparent : parent ∈ L.limitWarp) :
    R.record.initial ≠ parent.initial := by
  intro hroot
  have hparentRecord : parent = R.record :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa)) hparent
      R.limit_inessential.1 parent.initial_mem_support
      (hroot ▸ R.record.initial_mem_support)
  have ha : a = R.stage := by
    apply L.bookkeeping.chosen_stage_unique hL.legal.validBookkeeping
    · change L.chosen a = some parent
      exact hchosen
    · rw [hparentRecord]
      change L.chosen R.stage = some R.record
      exact R.chosen
  apply hx
  apply L.popularAuxiliaryIndexed_sourceIndexed hL
  exact (hindex.trans ha).trans R.source_index.symm

/-- The grounded parent which supplies a selected request trace never has
the genuine root of the unused record.  This is the selected-route half of
the missing-source argument following Assertion 8.22. -/
theorem record_initial_ne_selectedRequest_parent_initial
    (R : UnusedGroundedRecord L hL S)
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Ladder.Stage kappa) (parent : Gamma.DPath)
    (hchosen : L.chosen a = some parent)
    (hparent : parent ∈ L.limitWarp)
    (hindex : a = (L.popularAuxiliaryIndexed hL).f
      ⟨(GroundingSimultaneousDecode.strongSelectedPath
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r).start,
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)).starts_in_source
              ⟨r, rfl⟩⟩) :
    R.record.initial ≠ parent.initial := by
  let x : (L.popularAuxiliaryInput hL.legal).lambda.source :=
    ⟨(GroundingSimultaneousDecode.strongSelectedPath
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) r).start,
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)).starts_in_source ⟨r, rfl⟩⟩
  have hx : x ≠ R.auxiliarySource := by
    intro heq
    apply R.auxiliarySource_ne_strongSelectedPath_start r
    exact congrArg Subtype.val heq.symm
  exact R.record_initial_ne_parent_initial_of_auxiliarySource_ne
    x a parent hx hindex.symm hchosen hparent

/-- Bundled selected-request provenance with the root exclusion appended.
This avoids forcing downstream component arguments to reopen the stationary
bookkeeping calculation. -/
theorem exists_selectedRequest_parent_with_root_ne
    (R : UnusedGroundedRecord L hL S)
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ (a : Ladder.Stage kappa) (parent : Gamma.DPath),
      a ∈ L.phiGround ∧ L.chosen a = some parent ∧
        parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        (GroundingErasedDecode.selectedRequestTrace
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S) r).initial ∈ parent.support ∧
        parent.initial ∈ Gamma.source ∧
        a = (L.popularAuxiliaryIndexed hL).f
          ⟨(GroundingSimultaneousDecode.strongSelectedPath
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S) r).start,
            (GroundingSimultaneousDecode.strongSelectedWarp
              (L.popularAuxiliaryIndexed hL) S
                (L.groundedConcreteControls hL S)).starts_in_source
                  ⟨r, rfl⟩⟩ ∧
        R.record.initial ≠ parent.initial := by
  obtain ⟨a, parent, haGround, hchosen, hparent, htrace, hsource,
    hindex, _hdescription⟩ :=
      L.selectedRequestTrace_grounded_record_data hL S r
  exact ⟨a, parent, haGround, hchosen, hparent, htrace, hsource,
    hindex, R.record_initial_ne_selectedRequest_parent_initial r a parent
      hchosen hparent.1 hindex⟩

/-- An auxiliary source already contained in the cut cannot encode a
limiting-ladder parent rooted at the unused record's genuine source.  This
is the trivial-cut-source half of the missing-source argument. -/
theorem record_initial_ne_cutSource_parent_initial
    (R : UnusedGroundedRecord L hL S)
    (x : (L.popularAuxiliaryInput hL.legal).lambda.source)
    (hxCut : x.1 ∈ S.cut)
    (a : Ladder.Stage kappa) (parent : Gamma.DPath)
    (hindex : (L.popularAuxiliaryIndexed hL).f x = a)
    (hchosen : L.chosen a = some parent)
    (hparent : parent ∈ L.limitWarp) :
    R.record.initial ≠ parent.initial := by
  have hx : x ≠ R.auxiliarySource := by
    intro heq
    apply R.auxiliarySource_not_mem_cut
    exact congrArg Subtype.val heq ▸ hxCut
  exact R.record_initial_ne_parent_initial_of_auxiliarySource_ne
    x a parent hx hindex hchosen hparent

/-- The proxy-prefix repair of the simultaneous relation never deletes an
outgoing edge of the unused record.  Every such deletion is owned by a
selected route attachment, and the preceding theorem rules out an attachment
point on this record. -/
theorem record_edge_not_mem_attachmentCutEdges
    (R : UnusedGroundedRecord L hL S) {e : V × V}
    (he : e ∈ R.record.edgeSet) :
    e ∉ GroundingErasedDecode.attachmentCutEdges
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) := by
  intro heAttachment
  obtain ⟨c, hr⟩ := heAttachment.2
  apply R.selectedRequestTrace_initial_not_mem_record_support
    (GroundingErasedDecode.chosenRequest c)
  rw [← hr]
  exact (R.record.edgeSet_subset_support_prod he).1

theorem record_edgeSet_disjoint_attachmentCutEdges
    (R : UnusedGroundedRecord L hL S) :
    Disjoint R.record.edgeSet
      (GroundingErasedDecode.attachmentCutEdges
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)) := by
  rw [Set.disjoint_left]
  exact fun _ he ↦ R.record_edge_not_mem_attachmentCutEdges he

end UnusedGroundedRecord
end KappaLadder
end DWeb
end Erdos599

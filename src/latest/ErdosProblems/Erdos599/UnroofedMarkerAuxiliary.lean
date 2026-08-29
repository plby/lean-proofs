/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerGroundingData
import ErdosProblems.Erdos599.GroundingAllMarkerAuxiliary
import ErdosProblems.Erdos599.GroundingAllMarkerCutRecords
import ErdosProblems.Erdos599.PopularLayers

/-!
# The genuine unbalanced all-marker auxiliary of the unroofed ladder

The source set represents all grounded selected paths, not just the finite
ones. Targets represent every inserted marker. The decoded finite and ray
walks satisfy the already-proved strict birth-index barrier. This yields
the concrete indexed/unbalanced web needed for the popularity theorem,
including its source-cardinality hypothesis.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u}

def auxiliaryInput (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    GroundingAllMarkerAuxiliary.Input G (GroundedRecord G kappa preferred) where
  reference := ⟨(ladder G kappa preferred).limitWarp,
    (ladder_geometry G kappa preferred hNoEnter).warpStages (finalStage kappa)⟩
  record p := p.1
  record_mem p := (groundedRecord_mem_final_inessential G kappa preferred hNoEnter p).1
  record_injective := Subtype.val_injective
  markers := (ladder G kappa preferred).markerSet
  markers_initial := by
    rw [ladder_initialSet_limitWarp G kappa preferred hNoEnter]
    exact Set.subset_union_right

def auxiliarySourceIndex (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (auxiliaryInput G kappa preferred hNoEnter).web.source → Stage kappa :=
  groundedRecordStage G kappa preferred ∘
    (auxiliaryInput G kappa preferred hNoEnter).sourceEquiv.symm

def auxiliaryTargetIndex (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    (auxiliaryInput G kappa preferred hNoEnter).web.target ↪ Stage kappa :=
  (auxiliaryInput G kappa preferred hNoEnter).targetEquiv.symm.toEmbedding.trans
    (ladder G kappa preferred).markerStage

theorem auxiliarySourceIndex_injective (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    Function.Injective (auxiliarySourceIndex G kappa preferred hNoEnter) :=
  (groundedRecordStage_injective G kappa preferred).comp
    (auxiliaryInput G kappa preferred hNoEnter).sourceEquiv.symm.injective

theorem auxiliarySourceIndex_range_stationary (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Stationary.IsStationaryBelow kappa
      (Set.range (auxiliarySourceIndex G kappa preferred hNoEnter)) := by
  apply (groundedRecordStage_range_stationary G kappa preferred hNoEnter
    hkappa huncountable hphi).mono
  rintro a ⟨p, hp⟩
  refine ⟨(auxiliaryInput G kappa preferred hNoEnter).sourceEquiv p, ?_⟩
  change groundedRecordStage G kappa preferred
    ((auxiliaryInput G kappa preferred hNoEnter).sourceEquiv.symm
      ((auxiliaryInput G kappa preferred hNoEnter).sourceEquiv p)) = a
  rwa [Equiv.symm_apply_apply]

/-- Every actual source-to-target path in the contracted auxiliary has
strictly decreasing index, by decoding into the all-marker port barrier. -/
theorem auxiliary_path_descends (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph)
    (hstart : p.start ∈ (auxiliaryInput G kappa preferred hNoEnter).web.source)
    (hfinish : p.finish ∈ (auxiliaryInput G kappa preferred hNoEnter).web.target) :
    auxiliaryTargetIndex G kappa preferred hNoEnter ⟨p.finish, hfinish⟩ <
      auxiliarySourceIndex G kappa preferred hNoEnter ⟨p.start, hstart⟩ := by
  let L := ladder G kappa preferred
  let A := auxiliaryInput G kappa preferred hNoEnter
  let i : GroundedRecord G kappa preferred := A.sourceEquiv.symm ⟨p.start, hstart⟩
  let y : L.markerSet := A.targetEquiv.symm ⟨p.finish, hfinish⟩
  have hsi : p.start = GroundingAllMarkerAuxiliary.Input.Vertex.source i :=
    (A.sourceEquiv_symm_val ⟨p.start, hstart⟩).symm
  have hty : p.finish = GroundingAllMarkerAuxiliary.Input.Vertex.marker y :=
    (A.targetEquiv_symm_val ⟨p.finish, hfinish⟩).symm
  have w : Walk A.web.graph (.source i) (.marker y) := hsi ▸ hty ▸ p.walk
  change L.markerStage y < groundedRecordStage G kappa preferred i
  have hchosen := (groundedRecordStage_spec G kappa preferred i).1
  have hmarker := L.markerStage_spec y
  cases hi : i.1 with
  | inl f =>
      have hdecode := A.walk_decode_finite_record f hi y w
      exact ladder_finiteRecord_reachable_marker_index_lt G kappa preferred hNoEnter f
        (hi ▸ hchosen) hmarker hdecode
  | inr r =>
      obtain ⟨x, hx, z, hxz, hdecode⟩ := A.walk_decode_ray_record r hi y w
      exact ladder_rayRecord_reachable_marker_index_lt G kappa preferred hNoEnter r
        (hi ▸ hchosen) hx hxz hmarker hdecode

/-- The all-marker auxiliary is genuinely unbalanced whenever the actual
ladder record set is stationary. No grounding conclusion is a premise. -/
def auxiliaryUnbalanced (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Popular.KappaUnbalanced (auxiliaryInput G kappa preferred hNoEnter).web kappa where
  regular := hkappa
  uncountable := huncountable
  f := auxiliarySourceIndex G kappa preferred hNoEnter
  g := auxiliaryTargetIndex G kappa preferred hNoEnter
  f_range_stationary := auxiliarySourceIndex_range_stationary G kappa preferred hNoEnter
    hkappa huncountable hphi
  descends := auxiliary_path_descends G kappa preferred hNoEnter

theorem auxiliaryUnbalanced_sourceBounded (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Popular.KappaIndexed.SourceBounded
      (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed :=
  Popular.KappaIndexed.sourceBounded_of_sourceIndexed _
    (auxiliarySourceIndex_injective G kappa preferred hNoEnter)

/-- The proved popular-separator theorem now applies to the actual larger
auxiliary, with its source bound discharged rather than assumed. -/
def auxiliaryPopularSeparator (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Popular.PopularSeparator
      (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed :=
  Popular.theorem8_4
    (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliaryUnbalanced_sourceBounded G kappa preferred hNoEnter hkappa huncountable hphi)

/-- The stationary set of surviving original record indices after removing
all record owners touched by the actual popular separator. -/
def auxiliaryGoodRecordIndices (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Set (Stage kappa) :=
  (auxiliaryInput G kappa preferred hNoEnter).goodRecordIndices
    (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut

theorem auxiliaryGoodRecordIndices_stationary (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Stationary.IsStationaryBelow kappa
      (auxiliaryGoodRecordIndices G kappa preferred hNoEnter hkappa huncountable hphi) :=
  (auxiliaryInput G kappa preferred hNoEnter).goodRecordIndices_stationary _
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)

/-- Each surviving index is represented by the genuinely selected grounded
path with that index. Its complete owner has no cut reference edge. -/
theorem exists_uncut_grounded_record (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    {a : Stage kappa}
    (ha : a ∈ auxiliaryGoodRecordIndices G kappa preferred hNoEnter hkappa huncountable hphi) :
    ∃ p : GroundedRecord G kappa preferred,
      groundedRecordStage G kappa preferred p = a ∧
      GroundingAllMarkerAuxiliary.Input.Vertex.source p ∉
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut ∧
      Disjoint p.1.edgeSet ((auxiliaryInput G kappa preferred hNoEnter).cutEdges
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut) := by
  let A := auxiliaryInput G kappa preferred hNoEnter
  obtain ⟨p, hp, hsource, hedges⟩ := A.exists_uncut_record_of_mem_goodRecordIndices
    (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut ha
  refine ⟨p, ?_, hsource, hedges⟩
  change groundedRecordStage G kappa preferred (A.sourceEquiv.symm (A.sourceEquiv p)) = a at hp
  rwa [Equiv.symm_apply_apply] at hp

#print axioms auxiliaryInput
#print axioms auxiliary_path_descends
#print axioms auxiliaryUnbalanced
#print axioms auxiliaryUnbalanced_sourceBounded
#print axioms auxiliaryPopularSeparator
#print axioms auxiliaryGoodRecordIndices_stationary
#print axioms exists_uncut_grounded_record

end Erdos599.DWeb.UnroofedMarker

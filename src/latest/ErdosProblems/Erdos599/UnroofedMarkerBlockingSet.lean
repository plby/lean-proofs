/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerResidual
import ErdosProblems.Erdos599.GroundingAllMarkerBlockedInitials

/-!
# An actual separating blocking set for the unroofed ladder

The essential final frontier separates the original web, by the genuine
ladder's source-roof invariant. Inessential selected records avoid that
frontier by warp disjointness. These facts discharge every hypothesis of
the vertexwise blocking-set separator theorem. Its separator misses every
surviving grounded record; converting it to a grounded orthogonal warp
still requires the fragmentwise grounding construction.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u}

def auxiliaryTerminalCut (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) : Set V :=
  G.terminalFrontier (G.essentialWarpPart (ladder G kappa preferred).limitWarp)

theorem auxiliaryTerminalCut_separates (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source) :
    Popular.IsSeparator G (auxiliaryTerminalCut G kappa preferred) := by
  have hroof : G.source ⊆ G.roof (auxiliaryTerminalCut G kappa preferred) := by
    rw [auxiliaryTerminalCut, G.terminalFrontier_essentialWarpPart, G.roof_essential]
    exact (ladder_geometry G kappa preferred hNoEnter).roofsSourceAtStages (finalStage kappa)
  intro p hpSource hpTarget
  exact hroof hpSource p ⟨rfl, hpTarget⟩

theorem auxiliaryTerminalCut_disjoint_record (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (p : GroundedRecord G kappa preferred) :
    Disjoint (auxiliaryTerminalCut G kappa preferred) p.1.support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨q, hq, hqx⟩ hxp
  exact (G.not_mem_inessentialPaths_of_intersects_essential
    ((ladder_geometry G kappa preferred hNoEnter).warpStages (finalStage kappa))
    hq ⟨x, hxp, G.terminal_mem_support hqx⟩)
    (groundedRecord_mem_final_inessential G kappa preferred hNoEnter p)

def auxiliaryBlockingSet (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) : Set V :=
  (auxiliaryInput G kappa preferred hNoEnter).blockingSet
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut

/-- All terminal-profile and separation hypotheses are discharged by the
actual ladder; no ordinary hindrance or grounding output is assumed. -/
theorem auxiliaryBlockingSet_separates (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Popular.IsSeparator G
      (auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi) := by
  let A := auxiliaryInput G kappa preferred hNoEnter
  apply A.blockingSet_separates _ ?_
    (ladder_source_disjoint_markers G kappa preferred hNoEnter)
    (auxiliaryTerminalCut G kappa preferred)
    (auxiliaryTerminalCut_separates G kappa preferred hNoEnter) ?_ ?_
  · change G.source ⊆ G.initialSet (ladder G kappa preferred).limitWarp
    rw [ladder_initialSet_limitWarp G kappa preferred hNoEnter]
    exact Set.subset_union_left
  · rintro x ⟨p, hp, hpx⟩
    exact ⟨p, hp.1, hpx⟩
  · apply Set.disjoint_left.mpr
    rintro x hxT ⟨p, _hpGood, hxp⟩
    exact Set.disjoint_left.mp
      (auxiliaryTerminalCut_disjoint_record G kappa preferred hNoEnter p) hxT hxp

/-- Stationarily many original grounded records have whole supports
disjoint from the newly proved separator and have no deleted owner edge. -/
theorem exists_uncut_grounded_record_disjoint_blockingSet
    (G : DWeb V) (kappa : Cardinal.{u}) (preferred : Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    {a : Stage kappa}
    (ha : a ∈ auxiliaryGoodRecordIndices G kappa preferred hNoEnter hkappa huncountable hphi) :
    ∃ p : GroundedRecord G kappa preferred,
      groundedRecordStage G kappa preferred p = a ∧
      GroundingAllMarkerAuxiliary.Input.Vertex.source p ∉
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut ∧
      Disjoint p.1.edgeSet ((auxiliaryInput G kappa preferred hNoEnter).cutEdges
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut) ∧
      Disjoint p.1.support
        (auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi) := by
  let A := auxiliaryInput G kappa preferred hNoEnter
  let S := auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi
  obtain ⟨p, hp, hsource, hedges⟩ := exists_uncut_grounded_record G kappa preferred
    hNoEnter hkappa huncountable hphi ha
  refine ⟨p, hp, hsource, hedges, ?_⟩
  have hpGood : p ∉ A.badRecords S.cut := by
    rintro (hsrc | ⟨e, he, heC⟩)
    · exact hsource hsrc
    · exact Set.disjoint_left.mp hedges he heC
  apply Set.disjoint_left.mpr
  intro x hxp hxK
  exact Set.disjoint_left.mp (A.goodRecordVertices_disjoint_blockingSet S.cut S.separates)
    ⟨p, hpGood, hxp⟩ hxK

theorem auxiliaryBlockedFragment_grounded_or_attachable
    (G : DWeb V) (kappa : Cardinal.{u}) (preferred : Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    (P : (auxiliaryInput G kappa preferred hNoEnter).CutFragment)
    (hP : P ∈ (auxiliaryInput G kappa preferred hNoEnter).blockedFragments
      (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut) :
    (auxiliaryInput G kappa preferred hNoEnter).CutFragmentGrounded P ∨
      (auxiliaryInput G kappa preferred hNoEnter).CutFragmentAttachable
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut P := by
  apply (auxiliaryInput G kappa preferred hNoEnter).blockedFragment_grounded_or_attachable _ ?_ hP
  change G.initialSet (ladder G kappa preferred).limitWarp ⊆
    G.source ∪ (ladder G kappa preferred).markerSet
  rw [ladder_initialSet_limitWarp G kappa preferred hNoEnter]

#print axioms auxiliaryTerminalCut_separates
#print axioms auxiliaryTerminalCut_disjoint_record
#print axioms auxiliaryBlockingSet_separates
#print axioms exists_uncut_grounded_record_disjoint_blockingSet
#print axioms auxiliaryBlockedFragment_grounded_or_attachable

end Erdos599.DWeb.UnroofedMarker

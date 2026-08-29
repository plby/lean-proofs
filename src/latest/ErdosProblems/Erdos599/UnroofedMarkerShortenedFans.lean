/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerPrunedFans
import ErdosProblems.Erdos599.GroundingAllMarkerShortenedFans

/-!
# Concrete stationary fans with fully normalized ray sources

Actual grounded records begin at original sources, disjoint from all
markers. This discharges the sole initial-profile premise of ray
shortening. Every request now has a stationary, cut-normalized fan which
avoids hanging-fragment gadgets and all ports on its own origin ray.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)

theorem auxiliary_record_initial_not_marker (i : GroundedRecord G kappa preferred) :
    ((auxiliaryInput G kappa preferred hNoEnter).record i).initial ∉
      (auxiliaryInput G kappa preferred hNoEnter).markers := by
  change i.1.initial ∉ (ladder G kappa preferred).markerSet
  exact Set.disjoint_left.mp (ladder_source_disjoint_markers G kappa preferred hNoEnter)
    (groundedRecordStage_spec G kappa preferred i).2

variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)

def auxiliaryShortenedRecordFan
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Popular.JoinedFamily (auxiliaryInput G kappa preferred hNoEnter).web {r.1} :=
  (auxiliaryInput G kappa preferred hNoEnter).shortenedRecordFan
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter)

theorem auxiliaryShortenedRecordFan_stationary
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf
        (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed
        (auxiliaryShortenedRecordFan G kappa preferred hNoEnter hkappa huncountable hphi r).paths
        (auxiliaryShortenedRecordFan G kappa preferred hNoEnter
          hkappa huncountable hphi r).starts_in_source) :=
  (auxiliaryInput G kappa preferred hNoEnter).shortenedRecordFan_stationary
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter)

theorem auxiliaryShortenedRecordFan_cut_normalized
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryShortenedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    p.support ∩
        (auxiliaryPopularSeparator G kappa preferred hNoEnter
          hkappa huncountable hphi).cut ⊆ {r.1} :=
  (auxiliaryInput G kappa preferred hNoEnter).shortenedRecordFan_cut_normalized
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) hp

theorem auxiliaryShortenedRecordFan_start_good_record
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryShortenedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    ∃ i : GroundedRecord G kappa preferred,
      p.start = GroundingAllMarkerAuxiliary.Input.Vertex.source i ∧
      i ∉ (auxiliaryInput G kappa preferred hNoEnter).badRecords
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut :=
  (auxiliaryInput G kappa preferred hNoEnter).shortenedRecordFan_start_good_record
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) hp

theorem auxiliaryShortenedRecordFan_avoids_hanging_fragment
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryShortenedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths)
    {P : (auxiliaryInput G kappa preferred hNoEnter).CutFragment}
    (hP : P ∈ (auxiliaryInput G kappa preferred hNoEnter).cutFragments
      (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut)
    (hHang : P.path.initial ∉ G.source) :
    Disjoint p.support
      ((auxiliaryInput G kappa preferred hNoEnter).fragmentEdgeVertices P) := by
  apply (auxiliaryInput G kappa preferred hNoEnter).shortenedRecordFan_avoids_hanging_fragment
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) ?_ hp hP hHang
  change G.initialSet (ladder G kappa preferred).limitWarp ⊆
    G.source ∪ (ladder G kappa preferred).markerSet
  rw [ladder_initialSet_limitWarp G kappa preferred hNoEnter]

theorem auxiliaryShortenedRecordFan_own_ray_ports
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryShortenedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths)
    (i : GroundedRecord G kappa preferred) (ray : Ray G.graph)
    (hpi : p.start = GroundingAllMarkerAuxiliary.Input.Vertex.source i) (hi : i.1 = .inr ray)
    {a : (auxiliaryInput G kappa preferred hNoEnter).Vertex} (ha : a ∈ p.support)
    {x : V} (hx : x ∈ ray.support) :
    (auxiliaryInput G kappa preferred hNoEnter).sending a ≠ some x ∧
      (auxiliaryInput G kappa preferred hNoEnter).receiving a ≠ some x :=
  (auxiliaryInput G kappa preferred hNoEnter).shortenedRecordFan_own_ray_ports
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) hp i ray hpi hi ha hx

#print axioms auxiliaryShortenedRecordFan_stationary
#print axioms auxiliaryShortenedRecordFan_cut_normalized
#print axioms auxiliaryShortenedRecordFan_start_good_record
#print axioms auxiliaryShortenedRecordFan_avoids_hanging_fragment
#print axioms auxiliaryShortenedRecordFan_own_ray_ports

end Erdos599.DWeb.UnroofedMarker

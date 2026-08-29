/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerFans
import ErdosProblems.Erdos599.GroundingAllMarkerPrunedFans

/-!
# Actual stationary fans after all hanging-fragment pruning

The actual ladder's proved initial-set equality discharges the generic
initial-profile hypothesis. The resulting stationary fans start at uncut
grounded records, are normalized against the real popular cut, and avoid
the internal gadgets of every fragment not rooted at an original source.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
  (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)

def auxiliaryPrunedRecordFan
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Popular.JoinedFamily (auxiliaryInput G kappa preferred hNoEnter).web {r.1} :=
  (auxiliaryInput G kappa preferred hNoEnter).prunedRecordFan
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r

theorem auxiliaryPrunedRecordFan_stationary
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf
        (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed
        (auxiliaryPrunedRecordFan G kappa preferred hNoEnter hkappa huncountable hphi r).paths
        (auxiliaryPrunedRecordFan G kappa preferred hNoEnter
          hkappa huncountable hphi r).starts_in_source) :=
  (auxiliaryInput G kappa preferred hNoEnter).prunedRecordFan_stationary
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r

theorem auxiliaryPrunedRecordFan_cut_normalized
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryPrunedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    p.support ∩
        (auxiliaryPopularSeparator G kappa preferred hNoEnter
          hkappa huncountable hphi).cut ⊆ {r.1} :=
  (auxiliaryInput G kappa preferred hNoEnter).prunedRecordFan_cut_normalized
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r hp

theorem auxiliaryPrunedRecordFan_start_good_record
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryPrunedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    ∃ i : GroundedRecord G kappa preferred,
      p.start = GroundingAllMarkerAuxiliary.Input.Vertex.source i ∧
      i ∉ (auxiliaryInput G kappa preferred hNoEnter).badRecords
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut :=
  (auxiliaryInput G kappa preferred hNoEnter).prunedRecordFan_start_good_record
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r hp

/-- No hanging-track or initial-provenance hypothesis is left to assume
for this concrete ladder. -/
theorem auxiliaryPrunedRecordFan_avoids_hanging_fragment
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryPrunedRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths)
    {P : (auxiliaryInput G kappa preferred hNoEnter).CutFragment}
    (hP : P ∈ (auxiliaryInput G kappa preferred hNoEnter).cutFragments
      (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut)
    (hHang : P.path.initial ∉ G.source) :
    Disjoint p.support
      ((auxiliaryInput G kappa preferred hNoEnter).fragmentEdgeVertices P) := by
  apply (auxiliaryInput G kappa preferred hNoEnter).prunedRecordFan_avoids_hanging_fragment
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r ?_ hp hP hHang
  change G.initialSet (ladder G kappa preferred).limitWarp ⊆
    G.source ∪ (ladder G kappa preferred).markerSet
  rw [ladder_initialSet_limitWarp G kappa preferred hNoEnter]

#print axioms auxiliaryPrunedRecordFan_stationary
#print axioms auxiliaryPrunedRecordFan_cut_normalized
#print axioms auxiliaryPrunedRecordFan_start_good_record
#print axioms auxiliaryPrunedRecordFan_avoids_hanging_fragment

end Erdos599.DWeb.UnroofedMarker

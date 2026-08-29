/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerBlockingSet
import ErdosProblems.Erdos599.GroundingAllMarkerFanEscape

/-!
# Actual stationary good-record fans for unroofed-ladder requests

The request family is the nonsource part of the concrete popular cut.
The concrete fans are stationary, normalized against that entire cut,
and start at genuinely surviving grounded records. They already avoid
the edge gadgets of all uncut-marker initial fragments.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u}

def auxiliaryRequests (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :=
  (auxiliaryInput G kappa preferred hNoEnter).Request
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut

def auxiliaryGoodRecordFan (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Popular.JoinedFamily (auxiliaryInput G kappa preferred hNoEnter).web {r.1} :=
  (auxiliaryInput G kappa preferred hNoEnter).goodRecordFan
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r

theorem auxiliaryRequests_card_le (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    #(auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) ≤ kappa :=
  (auxiliaryInput G kappa preferred hNoEnter).requests_card_le
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)

theorem auxiliaryGoodRecordFan_stationary (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf
        (auxiliaryUnbalanced G kappa preferred hNoEnter hkappa huncountable hphi).toKappaIndexed
        (auxiliaryGoodRecordFan G kappa preferred hNoEnter hkappa huncountable hphi r).paths
        (auxiliaryGoodRecordFan G kappa preferred hNoEnter
          hkappa huncountable hphi r).starts_in_source) :=
  (auxiliaryInput G kappa preferred hNoEnter).goodRecordFan_stationary
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r

theorem auxiliaryGoodRecordFan_cut_normalized (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryGoodRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    p.support ∩
        (auxiliaryPopularSeparator G kappa preferred hNoEnter
          hkappa huncountable hphi).cut ⊆ {r.1} :=
  (auxiliaryInput G kappa preferred hNoEnter).goodRecordFan_cut_normalized
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r hp

theorem auxiliaryGoodRecordFan_start_good_record (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {p : FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph}
    (hp : p ∈ (auxiliaryGoodRecordFan G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    ∃ i : GroundedRecord G kappa preferred,
      p.start = GroundingAllMarkerAuxiliary.Input.Vertex.source i ∧
      i ∉ (auxiliaryInput G kappa preferred hNoEnter).badRecords
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut :=
  (auxiliaryInput G kappa preferred hNoEnter).goodRecordFan_start_good_record
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi) r hp

#print axioms auxiliaryRequests_card_le
#print axioms auxiliaryGoodRecordFan_stationary
#print axioms auxiliaryGoodRecordFan_cut_normalized
#print axioms auxiliaryGoodRecordFan_start_good_record

end Erdos599.DWeb.UnroofedMarker

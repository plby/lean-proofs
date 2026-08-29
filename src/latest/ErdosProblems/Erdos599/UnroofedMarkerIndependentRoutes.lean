/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerShortenedFans
import ErdosProblems.Erdos599.GroundingAllMarkerIndependentGeometry

/-!
# Concrete independent auxiliary routes for every cut request

Every request is assigned an actual member of its shortened stationary
fan. Their full fragmentwise footprints are pairwise disjoint. This
exports the complete selection on the real unroofed ladder, without an
independent-selection or grounding hypothesis.
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

def auxiliaryIndependentPath
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    FinitePath (auxiliaryInput G kappa preferred hNoEnter).web.graph :=
  (auxiliaryInput G kappa preferred hNoEnter).independentSelectedPath
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r

theorem auxiliaryIndependentPath_mem
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi r ∈
      (auxiliaryShortenedRecordFan G kappa preferred hNoEnter hkappa huncountable hphi r).paths :=
  (auxiliaryInput G kappa preferred hNoEnter).independentSelectedPath_mem
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r

theorem auxiliaryIndependentPath_finish
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi r).finish = r.1 :=
  (auxiliaryInput G kappa preferred hNoEnter).independentSelectedPath_finish
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r

theorem auxiliaryIndependentPath_start_good_record
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    ∃ i : GroundedRecord G kappa preferred,
      (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi r).start =
        GroundingAllMarkerAuxiliary.Input.Vertex.source i ∧
      i ∉ (auxiliaryInput G kappa preferred hNoEnter).badRecords
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut :=
  (auxiliaryInput G kappa preferred hNoEnter).independentSelectedPath_start_good_record
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r

theorem auxiliaryIndependentPath_footprints_disjoint : Pairwise
    (fun r s : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi ↦
      Disjoint ((auxiliaryInput G kappa preferred hNoEnter).routeFootprint
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut
        (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi r))
        ((auxiliaryInput G kappa preferred hNoEnter).routeFootprint
          (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut
          (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi s))) :=
  (auxiliaryInput G kappa preferred hNoEnter).independentSelectedPath_footprints_disjoint
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter)

theorem auxiliaryIndependentPath_supports_disjoint : Pairwise
    (fun r s : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi ↦
      Disjoint (auxiliaryIndependentPath G kappa preferred hNoEnter
        hkappa huncountable hphi r).support
        (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi s).support) :=
  (auxiliaryInput G kappa preferred hNoEnter).independentSelectedPath_supports_disjoint
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter)

#print axioms auxiliaryIndependentPath
#print axioms auxiliaryIndependentPath_mem
#print axioms auxiliaryIndependentPath_finish
#print axioms auxiliaryIndependentPath_start_good_record
#print axioms auxiliaryIndependentPath_footprints_disjoint
#print axioms auxiliaryIndependentPath_supports_disjoint

end Erdos599.DWeb.UnroofedMarker

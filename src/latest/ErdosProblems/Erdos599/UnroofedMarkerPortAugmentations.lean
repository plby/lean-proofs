/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerUntouchedRecords
import ErdosProblems.Erdos599.GroundingAllMarkerPortAugmentation

/-!
# Finite port augmentations on the actual unroofed ladder

Each actual auxiliary request has a finite simple augmenting port path
with a good grounded origin. No assumed path decoder, source truncation,
or free-endpoint certificate is added to the ladder hypotheses.
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

local notation "A" => auxiliaryInput G kappa preferred hNoEnter
local notation "S" => auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi

def auxiliaryPortAugmentation
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    (A).PortAugmentation (S).cut
      (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi r) r :=
  (A).independentPortAugmentation S
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r

theorem auxiliaryPortAugmentation_source_unmatched
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) (y : V) :
    let D := auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r
    ¬ (A).originStoppedMatching (S).cut D.origin D.departure D.departure y :=
  Input.PortAugmentation.source_unmatched A
    (auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r) y

theorem auxiliaryPortAugmentation_request_unmatched
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) (x : V) :
    let D := auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r
    ¬ (A).originStoppedMatching (S).cut D.origin D.departure x ((A).requestVertex r) :=
  Input.PortAugmentation.request_unmatched A
    (auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r) x

theorem auxiliaryPortAugmentation_forward_tail_not_blockingSet
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {x y : V} (he : (.inl x, .inr y) ∈
      (auxiliaryPortAugmentation G kappa preferred hNoEnter
        hkappa huncountable hphi r).path.edgeSet) :
    x ∉ auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi :=
  (A).independentPortAugmentation_forward_tail_not_blockingSet S
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r he

#print axioms auxiliaryPortAugmentation
#print axioms auxiliaryPortAugmentation_source_unmatched
#print axioms auxiliaryPortAugmentation_request_unmatched
#print axioms auxiliaryPortAugmentation_forward_tail_not_blockingSet

end Erdos599.DWeb.UnroofedMarker

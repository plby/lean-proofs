/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerPortAugmentations
import ErdosProblems.Erdos599.GroundingAllMarkerPortSwitch
import ErdosProblems.Erdos599.GroundingAllMarkerRequestInitials

/-!
# Exact port-switch certificates on the actual unroofed ladder

The matching toggle, projected balance, absence of reverse rays and
preservation of every blocking sink are specialized to the constructed
augmentations. Request fragments are proved hanging using the actual
source/marker disjointness. Source-rooted realization still needs the
finite-fragment localization, not a global source-boundary assumption.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
  (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)

local notation "A" => auxiliaryInput G kappa preferred hNoEnter
local notation "S" => auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi

def auxiliaryPortBaseEdges
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) : Set (V × V) :=
  (auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r).baseEdges A

def auxiliaryPortSwitchedEdges
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) : Set (V × V) :=
  (auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r).switchedEdges A

theorem auxiliaryPortSwitchedEdges_biUnique
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      auxiliaryPortSwitchedEdges G kappa preferred hNoEnter hkappa huncountable hphi r) :=
  (auxiliaryPortAugmentation G kappa preferred hNoEnter
    hkappa huncountable hphi r).switchedEdges_biUnique A

theorem auxiliaryPortSwitchedEdges_edgeBalance
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) (x : V) :
    edgeBalance
        (auxiliaryPortSwitchedEdges G kappa preferred hNoEnter hkappa huncountable hphi r) x =
      edgeBalance (auxiliaryPortBaseEdges G kappa preferred hNoEnter hkappa huncountable hphi r) x +
        propInt (x = (auxiliaryPortAugmentation G kappa preferred hNoEnter
          hkappa huncountable hphi r).departure) - propInt (x = (A).requestVertex r) :=
  (auxiliaryPortAugmentation G kappa preferred hNoEnter
    hkappa huncountable hphi r).switchedEdges_edgeBalance A x

theorem auxiliaryPortSwitchedEdges_noReverseRay
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    ¬ ContainsReverseDirectedRay
      (auxiliaryPortSwitchedEdges G kappa preferred hNoEnter hkappa huncountable hphi r) :=
  (auxiliaryPortAugmentation G kappa preferred hNoEnter
    hkappa huncountable hphi r).switchedEdges_noReverseRay A

theorem auxiliaryPortSwitchedEdges_blockingSink
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    {x : V} (hx : x ∈ auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi)
    (hin : HasIncoming
      (auxiliaryPortBaseEdges G kappa preferred hNoEnter hkappa huncountable hphi r) x) :
    HasIncoming
        (auxiliaryPortSwitchedEdges G kappa preferred hNoEnter hkappa huncountable hphi r) x ∧
      ¬ HasOutgoing
        (auxiliaryPortSwitchedEdges G kappa preferred hNoEnter hkappa huncountable hphi r) x :=
  (auxiliaryPortAugmentation G kappa preferred hNoEnter
    hkappa huncountable hphi r).switchedEdges_preserves_blocking_sink A S
      (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) r
      (auxiliaryIndependentPath_mem G kappa preferred hNoEnter hkappa huncountable hphi r) hx hin

theorem auxiliaryRequestFragment_not_grounded
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)
    (P : (A).CutFragment) (hinit : P.path.initial = (A).requestVertex r) :
    ¬ (A).CutFragmentGrounded P :=
  (A).requestFragment_not_grounded (S).cut r hNoEnter
    (ladder_source_disjoint_markers G kappa preferred hNoEnter) P hinit

#print axioms auxiliaryPortSwitchedEdges_biUnique
#print axioms auxiliaryPortSwitchedEdges_edgeBalance
#print axioms auxiliaryPortSwitchedEdges_noReverseRay
#print axioms auxiliaryPortSwitchedEdges_blockingSink
#print axioms auxiliaryRequestFragment_not_grounded

end Erdos599.DWeb.UnroofedMarker

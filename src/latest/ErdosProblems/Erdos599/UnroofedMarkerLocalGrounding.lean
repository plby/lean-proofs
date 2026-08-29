/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerPortSwitches
import ErdosProblems.Erdos599.GroundingAllMarkerLocalWarp

/-!
# Source-rooted local path families on the actual unroofed ladder

The actual limit-warp initial profile and grounded-origin specification
discharge the local grounding premises. Each request yields a genuine
finite family of disjoint original-source paths covering every required
local blocker. No source-rooting or realization hypothesis is assumed.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)

local notation "A" => auxiliaryInput G kappa preferred hNoEnter

theorem auxiliary_reference_initial_profile :
    G.initialSet (A).reference.paths ⊆ G.source ∪ (A).markers := by
  change G.initialSet (ladder G kappa preferred).limitWarp ⊆
    G.source ∪ (ladder G kappa preferred).markerSet
  rw [ladder_initialSet_limitWarp G kappa preferred hNoEnter]

variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)

local notation "S" => auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi
local notation "hi" => auxiliary_record_initial_not_marker G kappa preferred hNoEnter
local notation "his" => auxiliary_reference_initial_profile G kappa preferred hNoEnter

variable (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi)

local notation "D" =>
  auxiliaryPortAugmentation G kappa preferred hNoEnter hkappa huncountable hphi r
local notation "hq" =>
  auxiliaryIndependentPath_mem G kappa preferred hNoEnter hkappa huncountable hphi r

theorem auxiliaryPortAugmentation_origin_source : ((A).record (D).origin).initial ∈ G.source :=
  (groundedRecordStage_spec G kappa preferred (D).origin).2

local notation "ho" => auxiliaryPortAugmentation_origin_source G kappa preferred hNoEnter
  hkappa huncountable hphi r

def auxiliaryLocalSwitchedEdges : Set (V × V) := (D).localSwitchedEdges A S hi r hq

def auxiliaryLocalBlockingSet : Set V := (D).localBlockingSet A

theorem auxiliaryLocalBlockingSet_finite :
    (auxiliaryLocalBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi r).Finite :=
  (D).localBlockingSet_finite A

theorem auxiliaryLocalBlockingSet_rooted {x : V}
    (hx : x ∈ auxiliaryLocalBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi r) :
    ∃ a ∈ G.source, Relation.ReflTransGen (fun u v ↦ (u, v) ∈
      auxiliaryLocalSwitchedEdges G kappa preferred hNoEnter hkappa huncountable hphi r) a x :=
  (D).localBlockingSet_rooted A S hi r hq his ho hx

def auxiliaryLocalGroundingWarp : Popular.XSWarp G
    (auxiliaryLocalBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi r) :=
  (D).localGroundingWarp A S hi his r hq ho

theorem auxiliaryLocalGroundingWarp_covers :
    ∀ b ∈ auxiliaryLocalBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi r,
      ∃ p ∈ (auxiliaryLocalGroundingWarp G kappa preferred hNoEnter
        hkappa huncountable hphi r).paths, p.finish = b :=
  (D).localGroundingWarp_covers A S hi his r hq ho

theorem auxiliaryLocalGroundingWarp_one_hit {p : FinitePath G.graph}
    (hp : p ∈ (auxiliaryLocalGroundingWarp G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths) :
    p.support ∩ auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi =
      {p.finish} :=
  (D).localGroundingWarp_one_hit A S hi his r hq ho hp

theorem auxiliaryLocalGroundingWarp_paths_finite :
    (auxiliaryLocalGroundingWarp G kappa preferred hNoEnter
      hkappa huncountable hphi r).paths.Finite :=
  (D).localGroundingWarp_paths_finite A S hi his r hq ho

#print axioms auxiliaryLocalBlockingSet_rooted
#print axioms auxiliaryLocalGroundingWarp_covers
#print axioms auxiliaryLocalGroundingWarp_one_hit
#print axioms auxiliaryLocalGroundingWarp_paths_finite

end Erdos599.DWeb.UnroofedMarker

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerPersistence
import ErdosProblems.Erdos599.UnroofedMarkerProvenance

/-!
# Grounded stationary records for the unroofed-marker construction

The provenance map is strictly regressive on hanging records. Literal
persistence puts all selected components in the final warp, so its
disjointness and bookkeeping uniqueness make the provenance map injective.
Fodor's lemma then leaves a stationary set of original-source records.

Only the four stated bookkeeping/geometric properties are used. In
particular the historical marker-exhaustion clause is not assumed.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Persistent selected paths with the same initial vertex have the same
record index. No global legality or marker-selection condition is needed. -/
theorem chosen_stage_eq_of_initial_eq_of_persistent
    (L : G.KappaLadder kappa) (hvalid : L.HasValidBookkeeping)
    (hwarp : G.IsWarp L.limitWarp) (hpersist : L.RecordedPathsPersist)
    {a b : Stage kappa} {p q : G.DPath}
    (hp : L.chosen a = some p) (hq : L.chosen b = some q)
    (hinitial : p.initial = q.initial) : a = b := by
  have hpFinal : p ∈ L.limitWarp :=
    (hpersist a p hp (finalStage kappa) (Stage.succExtended a).2).1
  have hqFinal : q ∈ L.limitWarp :=
    (hpersist b q hq (finalStage kappa) (Stage.succExtended b).2).1
  have hpq : p = q := DWeb.IsWarp.eq_of_initial_eq G hwarp hpFinal hqFinal hinitial
  exact L.bookkeeping.chosen_stage_unique hvalid (hpq ▸ hp) hq

/-- Hanging records are nonstationary from their strict provenance and
literal final-warp persistence alone. -/
theorem phiHanging_not_stationary_of_provenance
    (L : G.KappaLadder kappa) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa) (hvalid : L.HasValidBookkeeping)
    (hwarp : G.IsWarp L.limitWarp) (hpersist : L.RecordedPathsPersist)
    (hprovenance : L.HasHangingProvenance) :
    ¬ Stationary.IsStationaryBelow kappa L.phiHanging := by
  classical
  let origin (a : Stage kappa) : Stage kappa :=
    if ha : a ∈ L.phiHanging then
      Classical.choose (hprovenance a ha (L.selectedPath hvalid ⟨a, ha.1⟩)
        (L.chosen_selectedPath hvalid ⟨a, ha.1⟩))
    else a
  have horigin (a : Stage kappa) (ha : a ∈ L.phiHanging) :
      origin a < a ∧
        L.marker (origin a) = some (L.selectedPath hvalid ⟨a, ha.1⟩).initial := by
    dsimp only [origin]
    rw [dif_pos ha]
    exact Classical.choose_spec (hprovenance a ha (L.selectedPath hvalid ⟨a, ha.1⟩)
      (L.chosen_selectedPath hvalid ⟨a, ha.1⟩))
  apply Stationary.not_isStationaryBelow_of_injOn_regressive huncountable hkappa
    (f := origin) (fun a ha ↦ (horigin a ha).1)
  intro a ha b hb hab
  apply L.chosen_stage_eq_of_initial_eq_of_persistent hvalid hwarp hpersist
    (L.chosen_selectedPath hvalid ⟨a, ha.1⟩)
    (L.chosen_selectedPath hvalid ⟨b, hb.1⟩)
  have hma := (horigin a ha).2
  rw [hab] at hma
  exact Option.some.inj (hma.symm.trans (horigin b hb).2)

/-- The stationary grounded part follows without the historical legality
predicate, using only the four concrete properties displayed here. -/
theorem phiGround_isStationary_of_provenance
    (L : G.KappaLadder kappa) (hkappa : kappa.IsRegular)
    (huncountable : aleph0 < kappa) (hvalid : L.HasValidBookkeeping)
    (hwarp : G.IsWarp L.limitWarp) (hpersist : L.RecordedPathsPersist)
    (hprovenance : L.HasHangingProvenance)
    (hphi : Stationary.IsStationaryBelow kappa L.phi) :
    Stationary.IsStationaryBelow kappa L.phiGround :=
  Ladder.phiGround_isStationary hkappa huncountable L.bookkeeping hvalid
    (fun p : G.DPath ↦ p.initial) G.source hphi
    (L.phiHanging_not_stationary_of_provenance hkappa huncountable hvalid
      hwarp hpersist hprovenance)

end Erdos599.DWeb.KappaLadder

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

theorem ladder_phiHanging_not_stationary (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa) :
    ¬ Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phiHanging :=
  (ladder G kappa preferred).phiHanging_not_stationary_of_provenance
    hkappa huncountable (ladder_validBookkeeping G kappa preferred)
    ((ladder_geometry G kappa preferred hNoEnter).warpStages (finalStage kappa))
    (ladder_recordedPathsPersist G kappa preferred hNoEnter)
    (ladder_hasHangingProvenance G kappa preferred hNoEnter)

theorem ladder_phiGround_isStationary (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi) :
    Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phiGround :=
  (ladder G kappa preferred).phiGround_isStationary_of_provenance
    hkappa huncountable (ladder_validBookkeeping G kappa preferred)
    ((ladder_geometry G kappa preferred hNoEnter).warpStages (finalStage kappa))
    (ladder_recordedPathsPersist G kappa preferred hNoEnter)
    (ladder_hasHangingProvenance G kappa preferred hNoEnter) hphi

#print axioms ladder_phiHanging_not_stationary
#print axioms ladder_phiGround_isStationary

end Erdos599.DWeb.UnroofedMarker

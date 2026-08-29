/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageSelection
import ErdosProblems.Erdos599.ColouredSafeTouchedStrongSwitch

/-!
# The actual endpoint-pruned protected two-port switch

Select a nondegenerate occurrence, localize it without changing finite
switched reachability, and retain the whole finite-character touched switch.
Its two protected ports are distinct actual paths, with all companions kept.
The same explicit fixed-stage roof filter is used throughout.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_hasCard_exists_strongTouchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    {extra : Occurrence (reference C.ladder.limitWarp s (some t)) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s (some t)) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedStrongSwitch (A.retypeEndpointStageReference C.legal hARoof) t,
          Gamma.vertexSet T.paths ∩ X ⊆ {s, t} ∧
          T.sourcePath.support ∩ X ⊆ {s} ∧
          T.terminalPath.support ∩ X ⊆ {t} ∧
          Disjoint (Gamma.vertexSet T.companions) X ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) ∧
          (A.retypeEndpointStageReference C.legal hARoof).touchedReference ⊆
            ladderReference C.ladder a ∧
          T.sourcePath.finish ∈ C.ladder.frontier a := by
  obtain ⟨A, hA, hARoof, hEss, hBX, hBRoof⟩ :=
    C.endpoint_hasCard_exists_essentialOccurrence_avoiding ha h
      (fun A hA ↦ hroof A hA.1) hX
  have hgood : A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra :=
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1⟩
  let B := A.retypeEndpointStageReference C.legal hARoof
  have hBfinite : Gamma.HasFiniteCharacter B.touchedReference :=
    fun hp ↦ ladderReference.finiteCharacter (hEss hp)
  have hnondeg : ¬B.HasFiniteSwitchedPathTo t := by
    intro hBdeg
    exact hA.2.2.2.2.2
      ((A.hasFiniteSwitchedPathTo_retypeEndpointStageReference_iff C.legal hARoof
        (hARoof (A.terminal_mem_vertexSet hA.2.1))).mp hBdeg)
  have hsOff : s ∉ Gamma.vertexSet (stageReference C.legal a s (some t)) := by
    intro hs
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      hs (Or.inl rfl)
  have htOff : t ∉ Gamma.vertexSet (stageReference C.legal a s (some t)) := by
    intro ht
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      ht (Or.inr rfl)
  obtain ⟨T⟩ := (hA.1.retypeEndpointStageReference C.legal hARoof).exists_touchedStrongSwitch
    stageReference_isWarp hBfinite
    (by simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_terminal?] using hA.2.1)
    hne hsOff htOff hnondeg
  have hports := T.protected_ports (by simpa only [endpoints_some] using hBX)
  have hTX : Gamma.vertexSet T.paths ∩ X ⊆ {s, t} := by
    intro x hx
    simpa only [endpoints_some] using hBX ⟨T.carrier_subset hx.1, hx.2⟩
  refine ⟨A, hgood, hARoof, T, hTX, hports.1, hports.2.1, hports.2.2,
    T.carrier_subset.trans hBRoof, hEss, ?_⟩
  obtain ⟨p, hp, hpt⟩ := T.source_finish
  rw [← ladderReference.terminalFrontier_eq C.legal]
  exact ⟨p, hEss hp, hpt⟩

#print axioms endpoint_hasCard_exists_strongTouchedSwitch_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

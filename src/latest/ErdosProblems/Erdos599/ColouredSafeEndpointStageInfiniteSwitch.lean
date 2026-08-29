/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageSelection
import ErdosProblems.Erdos599.ColouredSafeTouchedInfiniteSwitch

/-!
# The actual endpoint-pruned protected infinite-occurrence switch

The selected infinite word remains infinite after localization. Its touched
reference is finite-character, so its complete actual switch has a finite
source path to the frontier and all reference-source companions. The entire
carrier avoids the protected set except at the displayed source.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_hasCard_exists_infiniteTouchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V}
    {extra : Occurrence (reference C.ladder.limitWarp s none) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s none) s none extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s none) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s none) s none extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedInfiniteSwitch (A.retypeEndpointStageReference C.legal hARoof),
          Gamma.vertexSet T.paths ∩ X ⊆ {s} ∧
          Disjoint (Gamma.vertexSet T.companions) X ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) ∧
          (A.retypeEndpointStageReference C.legal hARoof).touchedReference ⊆
            ladderReference C.ladder a ∧
          T.sourcePath.finish ∈ C.ladder.frontier a := by
  obtain ⟨A, hA, hARoof, hEss, hBX, hBRoof⟩ :=
    C.endpoint_hasCard_exists_essentialOccurrence_avoiding ha h hroof hX
  let B := A.retypeEndpointStageReference C.legal hARoof
  have hBfinite : Gamma.HasFiniteCharacter B.touchedReference :=
    fun hp ↦ ladderReference.finiteCharacter (hEss hp)
  have hsOff : s ∉ Gamma.vertexSet (stageReference C.legal a s none) := by
    intro hs
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      hs (Or.inl rfl)
  obtain ⟨T⟩ := (hA.1.retypeEndpointStageReference C.legal hARoof).exists_touchedInfiniteSwitch
    stageReference_isWarp hBfinite
    (by simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_terminal?] using hA.2.1)
    hsOff
  have havoid : B.referenceClosure ∩ X ⊆ {s} := by
    simpa only [endpoints_none] using hBX
  refine ⟨A, hA, hARoof, T, ?_, T.companions_disjoint_protected havoid,
    T.carrier_subset.trans hBRoof, hEss, ?_⟩
  · intro x hx
    exact havoid ⟨T.carrier_subset hx.1, hx.2⟩
  · obtain ⟨p, hp, hpt⟩ := T.source_finish
    rw [← ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpt⟩

#print axioms endpoint_hasCard_exists_infiniteTouchedSwitch_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

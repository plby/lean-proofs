/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTouchedInfiniteSwitch
import ErdosProblems.Erdos599.ColouredSafeStageStrongSwitch

/-!
# The actual protected infinite-occurrence switch at a club stage

Selection excludes the inessential carrier before localization. Hence the
whole touched switch is finite-character, every new terminal is on the
stage frontier, and its complete carrier avoids the protected set except
at the old source. Uniform roof capture remains explicit.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem native_global_hasCard_exists_infiniteTouchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s none extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s none extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedInfiniteSwitch (A.retypeStageReference C.legal hARoof),
          Gamma.vertexSet T.paths ∩ X ⊆ {s} ∧
          Disjoint (Gamma.vertexSet T.companions) X ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) ∧
          (A.retypeStageReference C.legal hARoof).touchedReference ⊆
            ladderReference C.ladder a ∧
          T.sourcePath.finish ∈ C.ladder.frontier a := by
  obtain ⟨A, hA, hARoof, hEss, hBX, hBRoof⟩ :=
    C.native_global_hasCard_exists_essentialOccurrence_avoiding ha h hroof hX
  let B := A.retypeStageReference C.legal hARoof
  have hBfinite : Gamma.HasFiniteCharacter B.touchedReference :=
    fun hp ↦ ladderReference.finiteCharacter (hEss hp)
  have hs : s ∉ Gamma.vertexSet (C.ladder.warpAt a) := by
    rintro ⟨p, hp, hsp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact hA.2.2.1
      ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hsp⟩
  obtain ⟨T⟩ := (hA.1.retypeStageReference C.legal hARoof).exists_touchedInfiniteSwitch
    (C.legal.warpStages (Stage.toExtended a)) hBfinite
    (by simpa [B] using hA.2.1) hs
  have havoid : B.referenceClosure ∩ X ⊆ {s} :=
    by simpa only [endpoints_none] using hBX
  refine ⟨A, hA, hARoof, T, ?_, T.companions_disjoint_protected havoid,
    T.carrier_subset.trans hBRoof, hEss, ?_⟩
  · intro x hx
    exact havoid ⟨T.carrier_subset hx.1, hx.2⟩
  · obtain ⟨p, hp, hpt⟩ := T.source_finish
    rw [← ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpt⟩

#print axioms native_global_hasCard_exists_infiniteTouchedSwitch_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

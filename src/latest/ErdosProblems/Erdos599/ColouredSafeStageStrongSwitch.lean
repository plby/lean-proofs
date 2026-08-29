/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTouchedStrongSwitch
import ErdosProblems.Erdos599.ColouredSafeStageWeakSwitch

/-!
# Selecting an actual native strong two-port switch at a club stage

Reserve the protected set and the stage's inessential carrier before
selecting the occurrence. The localized touched reference is genuinely
essential and finite-character. Nondegeneracy survives exact roofed
reference transport, yielding the two actual protected finite ports.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- Selection and localization with the complete closure avoidance retained.
The route may have a finite end or be infinite. -/
theorem native_global_hasCard_exists_essentialOccurrence_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s e extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s e extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        (A.retypeStageReference C.legal hARoof).touchedReference ⊆
          ladderReference C.ladder a ∧
        (A.retypeStageReference C.legal hARoof).referenceClosure ∩ X ⊆ endpoints s e ∧
        (A.retypeStageReference C.legal hARoof).referenceClosure ⊆
          Gamma.roof (C.ladder.frontier a) := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  have hreserve : #(X ∪ bad : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  obtain ⟨A, hA, havoid⟩ := h.exists_goodRoute_avoiding_referenceClosure
    (C.legal.warpStages (finalStage (succ kappa))) C.capacity_infinite hreserve
  let hARoof := hroof A hA.2.2.2.2
  let B := A.retypeStageReference C.legal hARoof
  have hbadGlobal : bad ⊆ Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, C.legal.mem_limitWarp_of_mem_inessential hp, hxp⟩
  have hAbad : Disjoint A.vertexSet bad := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBad
    have hxEnds := havoid ⟨Or.inl hxA, Or.inr hxBad⟩
    rcases hxEnds with hxs | hxt
    · exact hA.2.2.1 (Set.mem_singleton_iff.mp hxs ▸ hbadGlobal hxBad)
    · exact hA.2.2.2.1 x hxt (hbadGlobal hxBad)
  have hBessential : B.touchedReference ⊆ ladderReference C.ladder a := by
    intro p hp
    by_contra hpEss
    obtain ⟨x, hxp, hxB⟩ := hp.2
    have hxA : x ∈ A.vertexSet := by simpa [B] using hxB
    have hxBad : x ∈ bad := ⟨p, ⟨hp.1, hpEss⟩, hxp⟩
    exact Set.disjoint_left.mp hAbad hxA hxBad
  have hBClosure : B.referenceClosure ⊆ A.referenceClosure :=
    A.retypeStageReference_referenceClosure_subset C.legal hARoof
  have hBX : B.referenceClosure ∩ X ⊆ endpoints s e := by
    intro x hx
    exact havoid ⟨hBClosure hx.1, Or.inl hx.2⟩
  have hstageRoof : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.roof (C.ladder.frontier a) := by
    rw [C.ladder.frontier_eq_essential_terminalFrontier C.legal.roofsSourceAtStages,
      Gamma.roof_essential]
    exact DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier C.legal a
  refine ⟨A, hA, hARoof, hBessential, hBX, ?_⟩
  apply Set.union_subset
  · simpa [B] using hARoof
  · exact meetingVertices_subset_roof Gamma (C.ladder.warpAt a) B.vertexSet _
      (fun p hp x hxp ↦ hstageRoof ⟨p, hp, hxp⟩)

/-- The finite-end strong branch supplies the whole actual switch, not
merely a source-to-frontier path. -/
theorem native_global_hasCard_exists_strongTouchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedStrongSwitch (A.retypeStageReference C.legal hARoof) t,
          Gamma.vertexSet T.paths ∩ X ⊆ {s, t} ∧
          T.sourcePath.support ∩ X ⊆ {s} ∧
          T.terminalPath.support ∩ X ⊆ {t} ∧
          Disjoint (Gamma.vertexSet T.companions) X ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) ∧
          (A.retypeStageReference C.legal hARoof).touchedReference ⊆
            ladderReference C.ladder a ∧
          T.sourcePath.finish ∈ C.ladder.frontier a := by
  obtain ⟨A, hA, hARoof, hEss, hBX, hBRoof⟩ :=
    C.native_global_hasCard_exists_essentialOccurrence_avoiding ha h
      (fun A hA ↦ hroof A hA.1) hX
  have hgood : A ∈ goodRoutes C.ladder.limitWarp s (some t) extra :=
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1⟩
  let B := A.retypeStageReference C.legal hARoof
  have hBfinite : Gamma.HasFiniteCharacter B.touchedReference :=
    fun hp ↦ ladderReference.finiteCharacter (hEss hp)
  have hstageV : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hxp⟩
  have hnondeg : ¬B.HasFiniteSwitchedPathTo t := by
    intro hBdeg
    exact hA.2.2.2.2.2
      ((A.hasFiniteSwitchedPathTo_retypeStageReference_iff C.legal hARoof
        (hARoof (A.terminal_mem_vertexSet hA.2.1))).mp hBdeg)
  obtain ⟨T⟩ := (hA.1.retypeStageReference C.legal hARoof).exists_touchedStrongSwitch
    (C.legal.warpStages (Stage.toExtended a)) hBfinite
    (by simpa [B] using hA.2.1) hne
    (fun hs ↦ hA.2.2.1 (hstageV hs))
    (fun ht ↦ hA.2.2.2.1 t rfl (hstageV ht)) hnondeg
  have hports := T.protected_ports (by simpa only [endpoints_some] using hBX)
  have hTX : Gamma.vertexSet T.paths ∩ X ⊆ {s, t} := by
    intro x hx
    simpa only [endpoints_some] using hBX ⟨T.carrier_subset hx.1, hx.2⟩
  refine ⟨A, hgood, hARoof, T, hTX, hports.1, hports.2.1, hports.2.2,
    T.carrier_subset.trans hBRoof, hEss, ?_⟩
  obtain ⟨p, hp, hpt⟩ := T.source_finish
  rw [← ladderReference.terminalFrontier_eq C.legal]
  exact ⟨p, hEss hp, hpt⟩

#print axioms native_global_hasCard_exists_essentialOccurrence_avoiding
#print axioms native_global_hasCard_exists_strongTouchedSwitch_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

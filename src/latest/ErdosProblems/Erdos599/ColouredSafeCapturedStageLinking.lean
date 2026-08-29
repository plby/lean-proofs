/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageLinking
import ErdosProblems.Erdos599.ColouredSafeReferenceEquiv

/-!
# Linking a globally witnessed hammock inside one actual stage roof

Uniform capture of the eligible occurrence carriers at the displayed stage
permits native localization. Reserve that stage's small inessential carrier
before choosing the hammock member, then restrict the localized occurrence
to the finite essential reference. This proves a genuine path into the
stage frontier. Uniform capture is an explicit filter property; existential
capture at a member-dependent stage is not substituted for it.
-/

noncomputable section

namespace Erdos599

open Set Cardinal Order DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {W : Set Gamma.DPath} {s : V}

theorem retypeStageReference_switchedEdges_subset
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence W L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).switchedEdges ⊆ A.switchedEdges := by
  intro e he
  rcases he with he | he
  · exact Or.inl ⟨(hL.stageReferenceEmbedding a).familyEdges_subset he.1,
      by simpa using he.2⟩
  · exact Or.inr (by simpa using he)

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace ColouredSafeAmbientOccurrence

variable {L : Gamma.KappaLadder kappa} {a : Stage kappa} {s : V}

theorem Valid.retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {A : Occurrence L.limitWarp s} (hA : Valid A)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Valid (A.retypeStageReference hL hRoof) := by
  obtain ⟨W, hW, hfinite, hforward⟩ := hA
  exact ⟨W, hW, hfinite, by simpa using hforward⟩

end ColouredSafeAmbientOccurrence

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeReverseReachability

variable {Y : Set Gamma.DPath}

theorem native_global_hasCard_exists_frontier_path_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {s : V} {e : Option V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s e extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnondeg : ∀ A, extra A → ∀ t, e = some t → ¬A.HasFiniteSwitchedPathTo t)
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ (A : Occurrence C.ladder.limitWarp s) (p : FinitePath Gamma.graph),
      A ∈ goodRoutes C.ladder.limitWarp s e extra ∧ p.start = s ∧
      p.finish ∈ C.ladder.frontier a ∧
      p.edgeSet ⊆ A.switchedEdges ∧ p.support ∩ X ⊆ endpoints s e := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  let reserve := X ∪ bad
  have hreserve : #reserve ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  have hGlobalWarp : Gamma.IsWarp C.ladder.limitWarp :=
    C.legal.warpStages (finalStage (succ kappa))
  obtain ⟨A, hA, havoid⟩ :=
    h.exists_goodRoute_avoiding_referenceClosure hGlobalWarp C.capacity_infinite hreserve
  have hbadGlobal : bad ⊆ Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, C.legal.mem_limitWarp_of_mem_inessential hp, hxp⟩
  have hendsOff : Disjoint (endpoints s e) (Gamma.vertexSet C.ladder.limitWarp) := by
    apply Set.disjoint_left.mpr
    intro x hx hxY
    rcases hx with hxs | hxt
    · exact hA.2.2.1 (Set.mem_singleton_iff.mp hxs ▸ hxY)
    · exact hA.2.2.2.1 x hxt hxY
  have hAbad : Disjoint A.vertexSet bad := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBad
    exact Set.disjoint_left.mp hendsOff
      (havoid ⟨Or.inl hxA, Or.inr hxBad⟩) (hbadGlobal hxBad)
  let hARoof := hroof A hA.2.2.2.2
  let B : Occurrence (C.ladder.warpAt a) s := A.retypeStageReference C.legal hARoof
  have hBvalid : Valid B := hA.1.retypeStageReference C.legal hARoof
  have hBbad : Disjoint B.vertexSet
      (Gamma.vertexSet (C.ladder.warpAt a \ ladderReference C.ladder a)) := by
    simpa only [B, CurrentSafeOccurrence.retypeStageReference_vertexSet,
      bad, inessentialCarrierAt, DWeb.inessentialPaths, ladderReference] using hAbad
  let hback := B.backwardEdges_subset_of_avoids_discardedReference hBbad
  have hsub : ladderReference C.ladder a ⊆ C.ladder.warpAt a := fun _ hp ↦ hp.1
  let Q : Occurrence (ladderReference C.ladder a) s := B.restrictReference hsub hback
  have hQvalid : Valid Q := hBvalid.restrictReference hsub hback
  have hQE : Q.switchedEdges ⊆ A.switchedEdges :=
    (B.restrictReference_switchedEdges_subset hsub hback).trans
      (A.retypeStageReference_switchedEdges_subset C.legal hARoof)
  have hQT : Q.terminal? = e := by simpa [Q, B] using hA.2.1
  have hlocalGlobal : Gamma.vertexSet (ladderReference C.ladder a) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp.1⟩).1, (E.owner ⟨p, hp.1⟩).2,
      E.support_subset ⟨p, hp.1⟩ hxp⟩
  have hQs : s ∉ Gamma.vertexSet (ladderReference C.ladder a) :=
    fun hs ↦ hA.2.2.1 (hlocalGlobal hs)
  have hQnondeg : ∀ t, e = some t → ¬Q.HasFiniteSwitchedPathTo t := by
    rintro t ht ⟨p, hps, hpt, hpe⟩
    exact hnondeg A hA.2.2.2.2 t ht ⟨p, hps, hpt, hpe.trans hQE⟩
  have hpath : ∃ p : FinitePath Gamma.graph, p.start = s ∧
      p.finish ∈ Gamma.terminalFrontier (ladderReference C.ladder a) ∧
      p.edgeSet ⊆ Q.switchedEdges ∧ p.support ⊆ Q.referenceClosure := by
    cases he : e with
    | none =>
        exact hQvalid.exists_referenceTerminal_path_of_infinite
          (ladderReference.isWarp C.legal) ladderReference.finiteCharacter
          (hQT.trans he) hQs
    | some t =>
        exact hQvalid.exists_referenceTerminal_path_of_nondegenerate
          (ladderReference.isWarp C.legal) ladderReference.finiteCharacter
          (hQT.trans he) hQs (fun ht ↦ hA.2.2.2.1 t he (hlocalGlobal ht))
          (hQnondeg t he)
  obtain ⟨p, hps, hpt, hpQ, _hpSupportQ⟩ := hpath
  have hpA : p.edgeSet ⊆ A.switchedEdges := hpQ.trans hQE
  have hpSupport := A.finitePath_support_subset_referenceClosure hGlobalWarp p hps hpA
  rw [ladderReference.terminalFrontier_eq C.legal] at hpt
  exact ⟨A, p, hA, hps, hpt, hpA,
    fun _ hx ↦ havoid ⟨hpSupport hx.1, Or.inl hx.2⟩⟩

#print axioms native_global_hasCard_exists_frontier_path_avoiding

end Blueprint.LinkageBlueprint.ClubStageGeometry
end Erdos599

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeTouchedReferenceSwitch
import ErdosProblems.Erdos599.ColouredSafeWeakContinuation

/-!
# Selecting a complete weak native switch at a club stage

Before choosing a degenerate hammock member, reserve the small inessential
carrier of the displayed club stage. Localization then has a genuinely
finite-character touched reference. Its exact switched warp contains both
the endpoint connector and the reference-source companions. The companions
avoid the whole protected carrier, not just its complement of the two ends.
The uniform fixed-stage roof filter remains explicit.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

open Set Cardinal Order DirectedPath Ladder Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}
variable {W : Set Gamma.DPath} {s : V}

/-- Every local touched owner is a prefix of a global touched owner. -/
theorem retypeStageReference_referenceClosure_subset
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence W L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).referenceClosure ⊆ A.referenceClosure := by
  rintro x (hxA | hxOwner)
  · exact Or.inl (by simpa using hxA)
  · obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxOwner
    let E := hL.stageReferenceEmbedding a
    let q := E.owner ⟨p.1, p.2.1⟩
    have hxq : x ∈ q.1.support := E.support_subset ⟨p.1, p.2.1⟩ hxp
    obtain ⟨y, hyp, hyA⟩ := p.2.2
    exact Or.inr (support_subset_meetingVertices Gamma L.limitWarp A.vertexSet q.2
      ⟨y, E.support_subset ⟨p.1, p.2.1⟩ hyp, by simpa using hyA⟩ hxq)

#print axioms retypeStageReference_referenceClosure_subset

end Erdos599.ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Erdos599.ColouredSafeAmbientOccurrence.TouchedWeakSwitch

open Set Cardinal Order DirectedPath Ladder Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa} {s t : V}

/-- A limiting reference owner which hit the displayed frontier and is
newly touched by the local switch has its unchanged initial in a companion.
This is the actual global/local source-coverage bridge. -/
theorem limitOwner_initial_mem_companions_of_meets
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {A : Occurrence L.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedWeakSwitch (A.retypeStageReference hL hARoof) t)
    (hs : s ∉ Gamma.vertexSet (L.warpAt a))
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty)
    (hmeet : (p.support ∩ Gamma.vertexSet T.paths).Nonempty) :
    p.initial ∈ Gamma.initialSet T.companions := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    LinkageBlueprint.ladderReference.exists_prefix_of_limitWarp_frontier_hit
      hL hp hvFrontier hvp
  obtain ⟨x, hxp, hxT⟩ := hmeet
  have hxq : x ∈ q.support :=
    DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      hL a hp hq.1 hqp ⟨hxp, hTRoof hxT⟩
  have hqInitial := T.referenceOwner_initial_mem_companions_of_meets
    (hL.warpStages (Stage.toExtended a)) hs hq.1 ⟨x, hxq, hxT⟩
  exact Gamma.extends_initial hqp ▸ hqInitial

#print axioms limitOwner_initial_mem_companions_of_meets

end Erdos599.ColouredSafeAmbientOccurrence.TouchedWeakSwitch

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The actual selected weak switch retains all touched reference sources
and has no protected-carrier contact on any companion component. -/
theorem native_global_weak_hasCard_exists_essentialTouchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnot : ¬HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedWeakSwitch (A.retypeStageReference C.legal hARoof) t,
          Disjoint (Gamma.vertexSet T.companions) X ∧
          T.connector.support ∩ X ⊆ {s, t} ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) ∧
          (A.retypeStageReference C.legal hARoof).touchedReference ⊆
            ladderReference C.ladder a := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  let reserve : Set V := X ∪ bad
  have hreserve : #reserve ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  have hGlobalWarp : Gamma.IsWarp C.ladder.limitWarp :=
    C.legal.warpStages (finalStage (succ kappa))
  have hdeg := h.hasCard_degenerate_of_not_nondegenerate C.capacity_infinite hnot
  obtain ⟨A, hA, havoid⟩ := hdeg.exists_goodRoute_avoiding_referenceClosure
    hGlobalWarp C.capacity_infinite hreserve
  have hgood : A ∈ goodRoutes C.ladder.limitWarp s (some t) extra :=
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1⟩
  let hARoof := hroof A hgood.2.2.2.2
  let B := A.retypeStageReference C.legal hARoof
  have hBvalid : Valid B := hA.1.retypeStageReference C.legal hARoof
  have hstageV : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    let E := C.legal.stageReferenceEmbedding a
    exact ⟨(E.owner ⟨p, hp⟩).1, (E.owner ⟨p, hp⟩).2, E.support_subset ⟨p, hp⟩ hxp⟩
  have hAbad : Disjoint A.vertexSet bad := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBad
    have hxEnds : x ∈ ({s, t} : Set V) := by
      simpa only [endpoints_some] using havoid ⟨Or.inl hxA, Or.inr hxBad⟩
    have hxGlobal : x ∈ Gamma.vertexSet C.ladder.limitWarp := by
      obtain ⟨p, hp, hxp⟩ := hxBad
      exact ⟨p, C.legal.mem_limitWarp_of_mem_inessential hp, hxp⟩
    rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
    · exact hgood.2.2.1 (hxs ▸ hxGlobal)
    · exact hgood.2.2.2.1 t rfl (Set.mem_singleton_iff.mp hxt ▸ hxGlobal)
  have hBessential : B.touchedReference ⊆ ladderReference C.ladder a := by
    intro p hp
    by_cases hpEss : p ∈ ladderReference C.ladder a
    · exact hpEss
    · obtain ⟨x, hxp, hxB⟩ := hp.2
      have hxA : x ∈ A.vertexSet := by simpa [B] using hxB
      have hxBad : x ∈ bad := ⟨p, ⟨hp.1, hpEss⟩, hxp⟩
      exact False.elim (Set.disjoint_left.mp hAbad hxA hxBad)
  have hBfinite : Gamma.HasFiniteCharacter B.touchedReference :=
    fun hp ↦ ladderReference.finiteCharacter (hBessential hp)
  have htRoof : t ∈ Gamma.roof (C.ladder.frontier a) :=
    hARoof (A.terminal_mem_vertexSet hA.2.1)
  have hBdeg : B.HasFiniteSwitchedPathTo t :=
    (A.hasFiniteSwitchedPathTo_retypeStageReference_iff C.legal hARoof htRoof).mpr
      hA.2.2.2.2.2
  obtain ⟨T⟩ := hBvalid.exists_touchedWeakSwitch
    (C.legal.warpStages (Stage.toExtended a)) hBfinite
    (by simpa [B] using hA.2.1) hne
    (fun hs ↦ hgood.2.2.1 (hstageV hs))
    (fun ht ↦ hgood.2.2.2.1 t rfl (hstageV ht)) hBdeg
  have hBClosure : B.referenceClosure ⊆ A.referenceClosure :=
    A.retypeStageReference_referenceClosure_subset C.legal hARoof
  have hBX : B.referenceClosure ∩ X ⊆ {s, t} := by
    intro x hx
    simpa only [endpoints_some] using havoid ⟨hBClosure hx.1, Or.inl hx.2⟩
  have hstageRoof : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.roof (C.ladder.frontier a) := by
    rw [C.ladder.frontier_eq_essential_terminalFrontier C.legal.roofsSourceAtStages,
      Gamma.roof_essential]
    exact DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier C.legal a
  have hBClosureRoof : B.referenceClosure ⊆ Gamma.roof (C.ladder.frontier a) := by
    apply Set.union_subset
    · simpa [B] using hARoof
    · exact meetingVertices_subset_roof Gamma (C.ladder.warpAt a) B.vertexSet _
        (fun p hp x hxp ↦ hstageRoof ⟨p, hp, hxp⟩)
  refine ⟨A, hgood, hARoof, T, T.companions_disjoint_protected hBX, ?_,
    T.carrier_subset.trans hBClosureRoof, hBessential⟩
  intro x hx
  exact hBX ⟨T.carrier_subset ⟨.inl T.connector, T.connector_mem, hx.1⟩, hx.2⟩

/-- The roofed protected-switch interface, without forgetting that the
construction above also restricts every touched owner to the essential part. -/
theorem native_global_weak_hasCard_exists_touchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnot : ¬HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedWeakSwitch (A.retypeStageReference C.legal hARoof) t,
          Disjoint (Gamma.vertexSet T.companions) X ∧
          T.connector.support ∩ X ⊆ {s, t} ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) := by
  obtain ⟨A, hA, hARoof, T, hcomp, hconn, hTRoof, _hEss⟩ :=
    C.native_global_weak_hasCard_exists_essentialTouchedSwitch_avoiding
      ha hne h hroof hnot hX
  exact ⟨A, hA, hARoof, T, hcomp, hconn, hTRoof⟩

#print axioms native_global_weak_hasCard_exists_touchedSwitch_avoiding
#print axioms native_global_weak_hasCard_exists_essentialTouchedSwitch_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingCanonical
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Localization of a fresh-avoiding route on a hanging component

In the nonstationary-fresh branch every finally selected auxiliary path
avoids every hanging limiting-ladder trace away from its own request apex.
The decoder can represent one original vertex by an old gadget, an edge
gadget, or its initial proxy, so the corresponding statement for the
compressed original-web route needs a short carrier argument.  This file
supplies it: every route vertex on a hanging limiting component lies in the
carrier of the route's own request apex.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedCarrierRank PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev HangingContactInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev HangingContactIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev HangingContactControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

/-- A compressed selected-route vertex lying on a hanging limiting-ladder
component is represented by the route's own request-apex gadget. -/
theorem splitGroundedFreshAvoiding_hangingContact_mem_apexCarrier
    (r : Request (HangingContactInput (L := L) (hL := hL)) S.cut)
    (Y : Gamma.DPath)
    (hYL : Y ∈ (HangingContactInput (L := L) (hL := hL)).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    {x : V}
    (hxRoute : x ∈ (selectedErasedCompression
      (HangingContactIndexed (L := L) (hL := hL) (hground := hground))
      S (HangingContactControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) r).path.vertexSet)
    (hxY : x ∈ Y.support) :
    x ∈ (HangingContactInput (L := L) (hL := hL)).gadgetCarrier
      (requestAuxVertex r) := by
  let J := HangingContactInput (L := L) (hL := hL)
  let U := HangingContactIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := HangingContactControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let p := strongSelectedPath U S K r
  have hpStart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  have hxDecoded : x ∈ J.decodedVertexCarrier p :=
    selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K r hxRoute
  simp only [PopularAuxiliary.Input.decodedVertexCarrier,
    Set.mem_iUnion] at hxDecoded
  obtain ⟨a, haPath, hxa⟩ := hxDecoded
  have apex_of_trace
      (haTrace : a ∈ PopularSwitching.ladderTrace J Y) :
      a = requestAuxVertex r := by
    by_contra hne
    apply L.splitGroundedFreshAvoidingCanonicalPath_no_hangingCollision
      hL hground hnotFresh S r
    exact ⟨Y, ⟨hYL, hhang⟩, a,
      ⟨haTrace, by
        intro ha
        exact hne (Set.mem_singleton_iff.1 ha)⟩, haPath⟩
  cases a with
  | old z =>
      have hxz : x = z := by simpa [J, gadgetCarrier] using hxa
      have haTrace : (LambdaVertex.old z : J.LV) ∈
          PopularSwitching.ladderTrace J Y :=
        Or.inl ⟨z, hxz ▸ hxY, rfl⟩
      rw [apex_of_trace haTrace] at hxa
      exact hxa
  | edge z w =>
      have hzw : (z, w) ∈ J.familyEdges :=
        J.edgeNode_mem_familyEdges_of_start_in_source p hpStart haPath
      obtain ⟨Z, hZL, hzwZ⟩ := hzw
      have hxEnds : x = z ∨ x = w := by
        simpa [J, gadgetCarrier, eq_comm] using hxa
      have hxZ : x ∈ Z.support := hxEnds.elim
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hzwZ).1)
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hzwZ).2)
      have hZY : Z = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
          hZL hYL hxZ hxY
      have haTrace : (LambdaVertex.edge z w : J.LV) ∈
          PopularSwitching.ladderTrace J Y :=
        Or.inr ⟨(z, w), hZY ▸ hzwZ, rfl⟩
      rw [apex_of_trace haTrace] at hxa
      exact hxa
  | proxy i =>
      have hproxyL : J.proxyPath i ∈ J.ladder.paths := by
        simpa [J, HangingContactInput] using
          (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL).1 i
      have hproxyY : J.proxyPath i = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
          hproxyL hYL (by simpa [J, gadgetCarrier] using hxa) hxY
      obtain ⟨a, ha, hchosen⟩ := i.2
      obtain ⟨q, hqChosen, hqGround⟩ := ha.1
      have hiq : i.1 = q := Option.some.inj (hchosen.symm.trans hqChosen)
      exfalso
      apply hhang
      rw [← hproxyY]
      simpa [J, splitGroundedPopularAuxiliaryInput,
        splitGroundedInfinitePath, hiq] using hqGround

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_hangingContact_mem_apexCarrier

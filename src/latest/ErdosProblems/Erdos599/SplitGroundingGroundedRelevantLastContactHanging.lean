/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingHangingContact
import ErdosProblems.Erdos599.SplitGroundingGroundedReducedLastContact

/-!
# Final contacts with hanging parents in the relevant branch

Combining exact vertex-carrier preservation of signed-route compression
with canonical hanging-trace avoidance shows that the final contact chosen
by the last-contact repair lies in the selected request's own apex gadget.
This is the source-faithful localization needed to splice a normalized
route into a surviving hanging fragment.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation
open PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev HangingLastInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev HangingLastIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev HangingLastControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

/-- The final contact of a canonical fresh-avoiding selected route with a
hanging limiting component is carried by that selected request's own apex. -/
theorem SplitGroundedReducedForwardConflictLastContact.lastContact_mem_apexCarrier
    {T : Set V} {Y : Gamma.DPath}
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := HangingLastControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) T Y)
    (hYL : Y ∈ (HangingLastInput (L := L) (hL := hL)).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y) :
    D.lastContact.vertex ∈
      (HangingLastInput (L := L) (hL := hL)).gadgetCarrier
        (requestAuxVertex (chosenRequest D.owner.1)) := by
  let U := HangingLastIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := HangingLastControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let r := chosenRequest D.owner.1
  let trace := selectedRequestTrace U S K r
  let E := trace.erasedRoute
  have hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s := by
    intro s hs
    exact trace.valid s (E.steps_sublist.subset hs)
  have hxRoute : D.lastContact.vertex ∈
      (selectedErasedCompression U S K r).path.vertexSet := by
    have hx := E.vertexChain_subset_compressionOfValid_vertexSet hvalid
      D.lastContact.vertex_mem_chain
    simpa only [E, trace, selectedErasedCompression,
      EndpointTrace.erasedCompression] using hx
  exact L.splitGroundedFreshAvoiding_hangingContact_mem_apexCarrier
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) r Y hYL hhang hxRoute D.lastContact.vertex_mem

/-- Endpoint form of the hanging final-contact localization.  The contact
is the selected exit itself, except for the single genuine edge-request
alternative at the represented cut edge's tail. -/
theorem SplitGroundedReducedForwardConflictLastContact.lastContact_eq_exit_or_mem_tail
    {T : Set V} {Y : Gamma.DPath}
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := HangingLastControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) T Y)
    (hYL : Y ∈ (HangingLastInput (L := L) (hL := hL)).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y) :
    D.lastContact.vertex = requestExit (chosenRequest D.owner.1) ∨
      D.lastContact.vertex ∈ requestTailSet (chosenRequest D.owner.1) := by
  have hcarrier := D.lastContact_mem_apexCarrier
    (hnotFresh := hnotFresh) hYL hhang
  rw [gadgetCarrier_requestAuxVertex_eq_exit_union_tail] at hcarrier
  rcases hcarrier with hexit | htail
  · exact Or.inl (Set.mem_singleton_iff.mp hexit)
  · exact Or.inr htail

/-- In fact the edge-tail alternative cannot be final.  If the selected
request is an edge request and its tail lies on the contacted hanging
component, disjointness identifies that component with the component of the
represented cut edge.  The request exit therefore lies on the same parent,
and, being the route terminal, is the true final contact. -/
theorem SplitGroundedReducedForwardConflictLastContact.lastContact_eq_exit
    {T : Set V} {Y : Gamma.DPath}
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := HangingLastControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) T Y)
    (hYL : Y ∈ (HangingLastInput (L := L) (hL := hL)).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y) :
    D.lastContact.vertex = requestExit (chosenRequest D.owner.1) := by
  let U := HangingLastIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := HangingLastControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let r := chosenRequest D.owner.1
  rcases D.lastContact_eq_exit_or_mem_tail
      (hnotFresh := hnotFresh) hYL hhang with hexit | htail
  · exact hexit
  · change D.lastContact.vertex ∈ requestTailSet r at htail
    cases hr : r with
    | inl old =>
        rw [hr] at htail
        exact False.elim (by simpa only [requestTailSet_inl,
          Set.mem_empty_iff_false] using htail)
    | inr edge =>
        rw [hr] at htail
        have hlastTail : D.lastContact.vertex = edge.1.1 := by
          simpa only [requestTailSet_inr, Set.mem_singleton_iff] using htail
        have htailY : edge.1.1 ∈ Y.support := by
          rw [← hlastTail]
          exact D.lastContact.vertex_mem
        let p := strongSelectedPath U S K r
        have hpStart : p.start ∈
            (HangingLastInput (L := L) (hL := hL)).lambda.source :=
          (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
        have hapexPath : requestAuxVertex r ∈ p.support := by
          rw [← strongSelectedPath_finish U S K r]
          exact p.finish_mem_support
        have hedgePath :
            (PopularAuxiliary.Input.LambdaVertex.edge edge.1.1 edge.1.2 :
              (HangingLastInput (L := L) (hL := hL)).LV) ∈ p.support := by
          simpa only [hr, requestAuxVertex] using hapexPath
        have hedgeFamily : edge.1 ∈
            (HangingLastInput (L := L) (hL := hL)).familyEdges := by
          have := (HangingLastInput (L := L) (hL := hL))
            |>.edgeNode_mem_familyEdges_of_start_in_source p hpStart hedgePath
          exact this
        obtain ⟨Z, hZL, hedgeZ⟩ := hedgeFamily
        have htailZ : edge.1.1 ∈ Z.support :=
          (Z.edgeSet_subset_support_prod hedgeZ).1
        have hZY : Z = Y :=
          Alternating.DWeb.IsWarp.eq_of_mem_support
            (HangingLastInput (L := L) (hL := hL)).ladder.disjoint
              hZL hYL htailZ htailY
        have hexitY : requestExit r ∈ Y.support := by
          have hheadZ : edge.1.2 ∈ Z.support :=
            (Z.edgeSet_subset_support_prod hedgeZ).2
          simpa only [hr, requestExit, hZY] using hheadZ
        exact D.lastContact.eq_terminal_of_terminal_mem hexitY

/-- For a hanging parent the source-faithful last-contact normalization
removes the selected tail altogether: the final parent contact is already
the selected request exit, so the normalized signed suffix has no steps. -/
theorem SplitGroundedReducedForwardConflictLastContact.hanging_suffix_steps_eq_nil
    {T : Set V} {Y : Gamma.DPath}
    (D : SplitGroundedReducedForwardConflictLastContact
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := HangingLastControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)) T Y)
    (hYL : Y ∈ (HangingLastInput (L := L) (hL := hL)).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y) :
    ((selectedRequestTrace
      (HangingLastIndexed (L := L) (hL := hL) (hground := hground)) S
      (HangingLastControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest D.owner.1)).erasedRoute.suffixFrom
        D.lastContact.vertex D.lastContact.vertex_mem_chain).steps = [] := by
  exact D.lastContact.suffixFrom_steps_eq_nil_of_eq_terminal
    (D.lastContact_eq_exit (hnotFresh := hnotFresh) hYL hhang)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.lastContact_mem_apexCarrier
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.lastContact_eq_exit_or_mem_tail
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.lastContact_eq_exit
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictLastContact.hanging_suffix_steps_eq_nil

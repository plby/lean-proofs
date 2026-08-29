/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedRouteSuffix
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingBackwardDescent

/-!
# The own-parent last contact in a fresh-avoiding selected route

After rank descent, the only forward-tail exchange which remains is owned
by the same request as the exposed parent.  The retained forward edge gives
a literal contact between that request's loop-erased signed route and the
parent.  Since the signed vertex chain is finite, it has a final such
contact.  The suffix compressor begins there and still ends at the request
exit.

This module constructs that actual last contact.  It does not assume that
the discarded parent tail is boundary-free; that separate obligation is
kept visible for the reduced-boundary transfer.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict
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

private abbrev LastContactIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev LastContactControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

/-- A self-owned forward-tail conflict determines a genuine final contact
of the selected signed route with the exposed parent. -/
theorem splitGroundedFreshAvoiding_selfForwardTail_exists_lastContact
    (state : L.SplitGroundedFreshAvoidingRootState
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (u : V)
    (owner : ActiveControlRequestAt
      (LastContactIndexed (L := L) (hL := hL) (hground := hground)) S
      (LastContactControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (f : V × V)
    (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
    (_conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
      (LastContactIndexed (L := L) (hL := hL) (hground := hground)) S
      (LastContactControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (retained : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (LastContactIndexed (L := L) (hL := hL) (hground := hground)) S
        (LastContactControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path)
    (same_tail : u = f.1)
    (_owner_eq : owner.1 = state.control.1) :
    Nonempty
      ((selectedRequestTrace
          (LastContactIndexed (L := L) (hL := hL) (hground := hground)) S
          (LastContactControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).erasedRoute.LastContact
        state.parent.support) := by
  let U := LastContactIndexed (L := L) (hL := hL) (hground := hground)
  let K := LastContactControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let T := selectedRequestTrace U S K (chosenRequest owner.1)
  let E := T.erasedRoute
  have hfDirection : f ∈ (selectedErasedCompression U S K
      (chosenRequest owner.1)).path.directionEdges .forward :=
    retainedForwardEdgesAt_subset_directionEdges ∅ _ retained
  have hfEdge : f ∈ (selectedErasedCompression U S K
      (chosenRequest owner.1)).path.edgeSet := by
    rw [(selectedErasedCompression U S K
      (chosenRequest owner.1)).path.edgeSet_eq_directionEdges_union]
    exact Or.inl hfDirection
  have hfChain : f.1 ∈ E.vertexChain := by
    have hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
        SignedEdge.Valid (Gamma := Gamma) s := by
      intro s hs
      exact T.valid s (E.steps_sublist.subset hs)
    have hends := E.compressionOfValid_edge_endpoints_mem_vertexChain
      hvalid (e := f) (by
        change f ∈ (T.erasedCompression).path.edgeSet
        simpa only [T, E, selectedErasedCompression,
          PopularAuxiliary.Input.EndpointTrace.erasedCompression] using
          hfEdge)
    exact hends.1
  have hfParent : f.1 ∈ state.parent.support := by
    rw [← same_tail]
    exact state.rootPath_support
      (state.rootPath.edgeSet_subset_support_prod parent_edge).1
  obtain ⟨i, hi⟩ := List.get_of_mem hfChain
  have hcontact : ∃ i : Fin E.vertexChain.length,
      E.vertexChain[i] ∈ state.parent.support := by
    refine ⟨i, ?_⟩
    change E.vertexChain.get i ∈ state.parent.support
    rw [hi]
    exact hfParent
  exact E.exists_lastContact state.parent.support hcontact

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_selfForwardTail_exists_lastContact

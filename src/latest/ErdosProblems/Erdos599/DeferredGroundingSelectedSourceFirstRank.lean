/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstFork
import ErdosProblems.Erdos599.GroundingSelectedOwnerRankCore

/-!
# Rank orientation of source-first endpoint transfers

At a nontrivial saturated fork, restoring the old source owner competes with
the first forward edge of the selected suffix.  If the maximal required
point on the discarded owner is the exit of another selected request, that
request is necessarily later in the canonical request order.  Indeed, its
endpoint exposes the discarded owner.  Were it earlier, the first forward
edge of the current suffix would depart from a component exposed by an
earlier selected route, contradicting strong freshness.

Thus the genuine old-request transfer graph is well founded in the forward
incidence direction.  More strongly, an endpoint transfer forces the later
request's source saturation to end at its prescribed terminal, so two
dependency edges cannot be composed.  There is therefore no forward ray to
compile.  This does not assert that every required point has an old request,
nor does it postulate a simultaneous choice of the remaining transactions.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

namespace ReservedStrongSelectedStartingLastContact.SourceSaturation

/-- Every vertex of the saturated selected suffix still belongs to the
decoded carrier of the original auxiliary request path. -/
theorem normalizedSuffix_vertexSet_subset_selected_decodedVertexCarrier
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.normalizedSuffix.path.vertexSet ⊆
      (popularAuxiliaryInput L hL.legal).decodedVertexCarrier
        (strongSelectedPath U S K r) := by
  intro x hx
  apply GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
    U S K r
  have hxStarting : x ∈ X.normalizedSuffix.path.vertexSet :=
    D.normalizedSuffix_vertexSet_subset_startingSuffix hx
  rw [X.normalizedSuffix_vertexSet_eq_remainingChain] at hxStarting
  have hxWhole : x ∈
      (selectedRequestTrace U S K r).erasedRoute.vertexChain :=
    (selectedRequestTrace U S K r).erasedRoute
      |>.suffixFrom_vertexChain_subset X.lastContact.vertex
        X.lastContact.vertex_mem_chain hxStarting
  exact (selectedRequestTrace U S K r).erasedRoute
    |>.vertexChain_subset_compressionOfValid_vertexSet
      (fun {_s} hs ↦ (selectedRequestTrace U S K r).valid _
        ((selectedRequestTrace U S K r).erasedRoute.steps_sublist.subset hs))
      hxWhole

/-- The selected suffix contact belongs to the decoded carrier of the
original auxiliary request path. -/
theorem contact_mem_selected_decodedVertexCarrier
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) :
    D.contact.vertex ∈
      (popularAuxiliaryInput L hL.legal).decodedVertexCarrier
        (strongSelectedPath U S K r) := by
  apply D.normalizedSuffix_vertexSet_subset_selected_decodedVertexCarrier
  exact Set.mem_of_eq_of_mem D.normalizedSuffix_initial.symm
    D.normalizedSuffix.path.initial_mem_vertexSet

/-- The request producing a genuine strict source-first fork exposes its
sacrificed source owner.  The witness is the saturation contact itself. -/
theorem LastSourceFirstPrefix.owner_exposed_by_request
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    D.owner ∈ exposedLadderPaths J (strongSelectedPath U S K r) := by
  have hownerLadder : D.owner ∈
      (popularAuxiliaryInput L hL.legal).ladder.paths := by
    simpa only [popularAuxiliaryInput, limitWarp] using F.owner_mem_limitWarp
  have hpathSource : (strongSelectedPath U S K r).start ∈
      (popularAuxiliaryInput L hL.legal).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  exact PopularAuxiliary.Input.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (popularAuxiliaryInput L hL.legal)
    (popularAuxiliary_proxyPathsFaithful L hL)
    (strongSelectedPath U S K r) hpathSource hownerLadder
    D.contact_mem_selected_decodedVertexCarrier D.contact_mem_owner

/-- The maximal required point of an old request exposes the sacrificed
source owner to that request's auxiliary path. -/
theorem LastSourceFirstPrefix.owner_exposed_by_exitRequest
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (request : Request J S.cut)
    (hexit : requestExit request = F.boundary) :
    D.owner ∈ exposedLadderPaths J (strongSelectedPath U S K request) := by
  have hownerLadder : D.owner ∈
      (popularAuxiliaryInput L hL.legal).ladder.paths := by
    simpa only [popularAuxiliaryInput, limitWarp] using F.owner_mem_limitWarp
  have hpathSource : (strongSelectedPath U S K request).start ∈
      (popularAuxiliaryInput L hL.legal).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨request, rfl⟩
  exact PopularAuxiliary.Input.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (popularAuxiliaryInput L hL.legal)
    (popularAuxiliary_proxyPathsFaithful L hL)
    (strongSelectedPath U S K request) hpathSource hownerLadder
    (GroundingErasedCarrierRank.requestExit_mem_strongSelectedPath_decodedVertexCarrier
      U S K request)
    (by rw [hexit]; exact F.boundary_mem_owner)

/-- A finite saturated suffix supplies an actual selected forward edge
whose tail is the saturation contact. -/
theorem exists_selectedForwardEdge_from_contact_of_finiteSuffix
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X)
    (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q) :
    ∃ z : V, (D.contact.vertex, z) ∈
      (selectedErasedCompression U S K r).path.directionEdges .forward := by
  have hdir : Q.firstLink.direction = .forward :=
    finiteSuffix_firstLink_forward D Q hQ
  obtain ⟨z, hz⟩ :=
    FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      Q.firstLink.path Q.firstLink.path.start_mem_support
        Q.firstLink.nontrivial
  have hfirstMem : Q.firstLink ∈ (AltPath.finite Q).links := by
    simp only [AltPath.links, FiniteTrace.links, Set.mem_range]
    exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
  have hQInitial : Q.initial = D.contact.vertex := by
    have h := D.normalizedSuffix_initial
    rw [hQ] at h
    simpa only [AltPath.initial] using h
  have hstart : Q.firstLink.path.start = D.contact.vertex := by
    calc
      Q.firstLink.path.start = Q.firstLink.entry := by
        simp only [Link.entry, hdir]
      _ = Q.initial := rfl
      _ = D.contact.vertex := hQInitial
  refine ⟨z, ?_⟩
  apply X.normalizedSuffix_directionEdges_subset_selected .forward
  apply D.normalizedSuffix_directionEdges_subset_startingSuffix .forward
  rw [hQ]
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  exact ⟨Q.firstLink, hfirstMem, hdir, by simpa only [hstart] using hz⟩

/-- A request whose exit is the displaced maximal source-first point of a
nontrivial fork is strictly later than the request producing that fork. -/
theorem LastSourceFirstPrefix.requestRank_lt_of_exitRequest_of_finiteSuffix
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q)
    (request : Request J S.cut)
    (hexit : requestExit request = F.boundary) :
    GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S request := by
  have hrequestNe : r ≠ request := by
    intro hrequest
    subst request
    have hterminal : Q.terminal = requestExit r := by
      have h := D.normalizedSuffix_terminal
      rw [hQ] at h
      exact Option.some.inj h
    have hterminalSuffix : Q.terminal ∈
        D.normalizedSuffix.path.vertexSet := by
      rw [hQ]
      exact Q.terminal_mem_vertexSet
    have hterminalCarrier : Q.terminal ∈ X.sourceGroundedCarrier := by
      refine ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩, ?_⟩
      rw [hterminal, hexit]
      exact F.boundary_mem_owner
    have hterminalContact :=
      D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
        hterminalSuffix hterminalCarrier
    exact F.contact_before.2
      (hterminalContact.symm.trans (hterminal.trans hexit))
  rcases lt_trichotomy
      (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S request) with
      hlt | heq | hgt
  · exact hlt
  · exact False.elim (hrequestNe
      ((GroundingAssembly.requestRank U S).injective heq))
  · obtain ⟨z, hz⟩ :=
      D.exists_selectedForwardEdge_from_contact_of_finiteSuffix Q hQ
    exact False.elim
      (selectedOwnerCore_later_no_forwardTail
        U S K (popularAuxiliary_proxyPathsFaithful L hL)
        request r hgt D.owner (F.owner_exposed_by_exitRequest request hexit)
        hz D.contact_mem_owner)

/-- The two selected transactions on an actual old-request transfer are
vertex-disjoint after source saturation.  Strong freshness confines any
overlap to the later request apex.  In the old-cut case that apex carrier is
the singleton maximal boundary point, while the earlier suffix cannot
return to that strictly later point of its source-grounded owner. -/
theorem LastSourceFirstPrefix.disjoint_normalizedSuffix_selectedRoute_of_oldExit
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (Q : FiniteTrace Gamma.graph)
    (hQ : D.normalizedSuffix.path = .finite Q)
    (request : Request J S.cut)
    (hapex : requestAuxVertex request = .old F.boundary)
    (hexit : requestExit request = F.boundary) :
    Disjoint D.normalizedSuffix.path.vertexSet
      (selectedErasedCompression U S K request).path.vertexSet := by
  rw [Set.disjoint_left]
  intro x hxSuffix hxRequest
  have hrank :=
    F.requestRank_lt_of_exitRequest_of_finiteSuffix Q hQ request hexit
  have hxEarlier : x ∈
      (popularAuxiliaryInput L hL.legal).decodedVertexCarrier
        (strongSelectedPath U S K r) :=
    D.normalizedSuffix_vertexSet_subset_selected_decodedVertexCarrier hxSuffix
  have hxLater : x ∈
      (popularAuxiliaryInput L hL.legal).decodedVertexCarrier
        (strongSelectedPath U S K request) :=
    GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K request hxRequest
  have hxApex :=
    GroundingErasedCarrierRank.strongSelectedPath_decodedVertexCarrier_inter_subset_apex
      U S K (popularAuxiliary_proxyPathsFaithful L hL) r request hrank
        ⟨hxLater, hxEarlier⟩
  have hxBoundary : x = F.boundary := by
    rw [hapex] at hxApex
    simpa [PopularAuxiliary.Input.gadgetCarrier] using hxApex
  have hxGrounded : x ∈ X.sourceGroundedCarrier := by
    refine ⟨D.owner, ⟨D.owner_mem, D.owner_source⟩, ?_⟩
    rw [hxBoundary]
    exact F.boundary_mem_owner
  have hxContact :=
    D.eq_contact_of_mem_normalizedSuffix_of_mem_sourceGroundedCarrier
      hxSuffix hxGrounded
  exact F.contact_before.2 (hxContact.symm.trans hxBoundary)

/-- The actual old-request fork dependency.  Its witnesses are the
canonical starting-last-contact state, source saturation, maximal required
owner prefix, and the nontrivial finite selected suffix. -/
def OldRequestForkDependency
    (r request : Request J S.cut) : Prop :=
  ∃ (X : ReservedStrongSelectedStartingLastContact
        (L := L) (hL := hL) (S := S) r)
      (D : SourceSaturation X)
      (F : LastSourceFirstPrefix D)
      (Q : FiniteTrace Gamma.graph),
    D.normalizedSuffix.path = .finite Q ∧
      requestAuxVertex request = .old F.boundary ∧
      requestExit request = F.boundary

/-- Every actual dependency edge is strictly increasing in canonical
request rank. -/
theorem oldRequestForkDependency_rank_lt
    {r request : Request J S.cut}
    (h : OldRequestForkDependency
      (L := L) (hL := hL) (S := S) r request) :
    GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S request := by
  obtain ⟨X, D, F, Q, hQ, _hapex, hexit⟩ := h
  exact F.requestRank_lt_of_exitRequest_of_finiteSuffix Q hQ request hexit

/-- Two genuine old-request forks cannot point to the same later request.
If they did, their maximal boundary points, and hence their limiting target
owners, would coincide.  Whichever producing request is later would then
have a selected forward departure from an owner already exposed by the
earlier request, contradicting strong freshness. -/
theorem oldRequestForkDependency_leftUnique :
    Relator.LeftUnique (OldRequestForkDependency
      (L := L) (hL := hL) (S := S)) := by
  intro r r' request hr hr'
  obtain ⟨X, D, F, Q, hQ, _hapex, hexit⟩ := hr
  obtain ⟨Y, E, G, R, hR, _hapex', hexit'⟩ := hr'
  have hboundary : F.boundary = G.boundary :=
    hexit.symm.trans hexit'
  have howner : D.owner = E.owner :=
    F.owner_eq_of_boundary_eq G hboundary
  rcases lt_trichotomy
      (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S r') with hlt | heq | hgt
  · obtain ⟨z, hz⟩ :=
      E.exists_selectedForwardEdge_from_contact_of_finiteSuffix R hR
    exact False.elim
      (selectedOwnerCore_later_no_forwardTail
        U S K (popularAuxiliary_proxyPathsFaithful L hL)
        r r' hlt D.owner F.owner_exposed_by_request hz
        (howner ▸ E.contact_mem_owner))
  · exact (GroundingAssembly.requestRank U S).injective heq
  · obtain ⟨z, hz⟩ :=
      D.exists_selectedForwardEdge_from_contact_of_finiteSuffix Q hQ
    exact False.elim
      (selectedOwnerCore_later_no_forwardTail
        U S K (popularAuxiliary_proxyPathsFaithful L hL)
        r' r hgt E.owner G.owner_exposed_by_request hz
        (howner.symm ▸ D.contact_mem_owner))

/-- Two finite initial subpaths of the same limiting component with the
same endpoint are literally the same finite path. -/
private theorem initialSubpath_eq_of_finish_eq
    (P : Gamma.DPath) (p q : FinitePath Gamma.graph)
    (hpStart : p.start = P.initial) (hqStart : q.start = P.initial)
    (hpEdges : p.edgeSet ⊆ P.edgeSet)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    (hfinish : p.finish = q.finish) :
    p = q := by
  have hpOccurs :=
    initialSubpath_finish_occursAt_length P p hpStart hpEdges
  have hqOccurs :=
    initialSubpath_finish_occursAt_length P q hqStart hqEdges
  have hpOccurs' : GroundingCut.OccursAt P p.walk.length q.finish := by
    simpa only [hfinish] using hpOccurs
  have hlength : p.walk.length = q.walk.length :=
    GroundingCutDecoder.occursAt_index_injective hpOccurs' hqOccurs
  have hpq : p.IsPrefixOf q :=
    initialSubpath_isPrefixOf_of_length_le P p q
      hpStart hqStart hpEdges hqEdges hlength.le
  have hqp : q.IsPrefixOf p :=
    initialSubpath_isPrefixOf_of_length_le P q p
      hqStart hpStart hqEdges hpEdges hlength.ge
  apply FinitePath.eq_of_start_finish_edgeSet_eq p q
  · exact hpStart.trans hqStart.symm
  · exact hfinish
  · apply Set.Subset.antisymm
    · exact p.walk.edgeSet_subset_of_support_prefix q.walk hpq
    · exact q.walk.edgeSet_subset_of_support_prefix p.walk hqp

/-- The own-start last-contact datum of one selected request is intrinsic:
different choices of the witnessing structure have the same last contact
and the same retained source prefix. -/
theorem reservedStrongSelectedStartingLastContact_unique
    {r : Request J S.cut}
    (X Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r) :
    X = Y := by
  have hposition : X.lastContact.position = Y.lastContact.position :=
    X.lastContact.position_eq_of_subset_of_vertex_mem Y.lastContact
      Set.Subset.rfl Y.lastContact.vertex_mem
  have hcontact : X.lastContact = Y.lastContact := by
    cases hX : X.lastContact with
    | mk i hi hlast =>
      cases hY : Y.lastContact with
      | mk j hj hlast' =>
        simp only [hX, hY] at hposition
        subst j
        rfl
  have hprefix : X.oldPrefix = Y.oldPrefix := by
    apply initialSubpath_eq_of_finish_eq
      (reservedStrongSelectedStartingRecord r).record
      X.oldPrefix Y.oldPrefix X.oldPrefix_start Y.oldPrefix_start
      X.oldPrefix_edges Y.oldPrefix_edges
    exact X.oldPrefix_finish.trans
      ((congrArg ErasedSignedRoute.LastContact.vertex hcontact).trans
        Y.oldPrefix_finish.symm)
  cases X
  cases Y
  simp_all

/-- Source saturation of one fixed request also has an intrinsic owner.
After uniqueness of the own-start truncation, both saturation contacts are
the last occurrence of the same source-grounded carrier; warp disjointness
then identifies their displayed owners. -/
theorem sourceSaturation_owner_unique
    {r : Request J S.cut}
    {X Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) (E : SourceSaturation Y) :
    D.owner = E.owner := by
  have hXY : X = Y :=
    reservedStrongSelectedStartingLastContact_unique X Y
  subst Y
  have hcontact : D.contact.vertex = E.contact.vertex :=
    D.contact.vertex_eq_of_subset_of_vertex_mem E.contact
      Set.Subset.rfl E.contact.vertex_mem
  exact DWeb.IsWarp.eq_of_mem_support X.truncatedWarp_isWarp
    D.owner_mem E.owner_mem D.contact_mem_owner
      (hcontact ▸ E.contact_mem_owner)

/-- One producing request has at most one old-request dependency target.
The two final-contact operations make its sacrificed owner intrinsic; the
maximal source-first point on that owner is intrinsic as well, and the old
auxiliary apex identifies its request.  Combined with left uniqueness, the
depth-one dependency graph is therefore a partial matching. -/
theorem oldRequestForkDependency_rightUnique :
    Relator.RightUnique (OldRequestForkDependency
      (L := L) (hL := hL) (S := S)) := by
  intro r request request' hr hr'
  obtain ⟨X, D, F, Q, hQ, hapex, _hexit⟩ := hr
  obtain ⟨Y, E, G, R, hR, hapex', _hexit'⟩ := hr'
  have howner : D.owner = E.owner :=
    sourceSaturation_owner_unique D E
  have hboundary : F.boundary = G.boundary :=
    F.boundary_eq_of_owner_eq G howner
  apply GroundingSelection.requestAuxVertex_injective
  calc
    requestAuxVertex request = .old F.boundary := hapex
    _ = .old G.boundary := congrArg _ hboundary
    _ = requestAuxVertex request' := hapex'.symm

/-- An old-request fork dependency cannot itself have a successor.

Indeed, if `r` displaces the exit of `request`, that exit lies on the
source-grounded owner displayed by the first fork.  This owner is a genuine
limiting component and is different from every selected starting record.
Consequently it belongs to the truncated reference warp of *any* last-contact
state for `request`.  The prescribed terminal of the selected route is
therefore already in the source-grounded carrier.  Source saturation must
take that terminal as its final contact, leaving the zero-edge suffix.  Such
a state cannot supply the nontrivial finite alternating suffix required by a
second fork.

Thus the apparent forward-infinite dependency case does not produce a ray:
the canonical final-contact operation collapses it after one transfer. -/
theorem oldRequestForkDependency_no_successor
    {r request next : Request J S.cut}
    (h : OldRequestForkDependency
      (L := L) (hL := hL) (S := S) r request) :
    ¬ OldRequestForkDependency
      (L := L) (hL := hL) (S := S) request next := by
  obtain ⟨X, D, F, Q, hQ, _hapex, hexit⟩ := h
  rintro ⟨Y, E, G, R, hR, _hapexNext, _hexitNext⟩
  have hownerY : D.owner ∈ Y.truncatedWarp :=
    Y.mem_truncatedWarp_of_mem_limitWarp_of_ne_record
      F.owner_mem_limitWarp (F.owner_ne_startingRecord request)
  have hownerGrounded : D.owner ∈ Y.sourceGroundedOwners :=
    ⟨hownerY, D.owner_source⟩
  have hexitCarrier : requestExit request ∈ Y.sourceGroundedCarrier := by
    refine ⟨D.owner, hownerGrounded, ?_⟩
    rw [hexit]
    exact F.boundary_mem_owner
  have hcontact : E.contact.vertex = requestExit request :=
    E.contact.eq_terminal_of_terminal_mem hexitCarrier
  have hnil : E.remainingSuffix.steps = [] :=
    E.contact.suffixFrom_steps_eq_nil_of_eq_terminal hcontact
  have htrivial : E.normalizedSuffix.path =
      .trivial (requestExit request) := by
    rw [SourceSaturation.normalizedSuffix]
    simp only [ErasedSignedRoute.compressionOfValid, hnil, dif_pos]
    congr
  rw [htrivial] at hR
  cases hR

/-- In particular there is no forward-infinite old-request dependency
chain.  The contradiction already occurs between its first two edges; no
limit or ray realization is involved. -/
theorem oldRequestForkDependency_no_forward_chain :
    ¬ ∃ f : ℕ → Request J S.cut, ∀ n,
      OldRequestForkDependency
        (L := L) (hL := hL) (S := S) (f n) (f (n + 1)) := by
  rintro ⟨f, hstep⟩
  exact oldRequestForkDependency_no_successor (hstep 0) (hstep 1)

/-- The old-request fork dependency has no reverse-infinite chain.  This
is the exact global termination invariant supplied by the canonical
selection order.  The stronger theorem above also rules out two consecutive
forward dependency edges. -/
theorem oldRequestForkDependency_wellFounded :
    WellFounded (OldRequestForkDependency
      (L := L) (hL := hL) (S := S)) :=
  (InvImage.wf (GroundingAssembly.requestRank U S) wellFounded_lt).mono
    (fun _ _ h ↦ oldRequestForkDependency_rank_lt h)

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.requestRank_lt_of_exitRequest_of_finiteSuffix
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkDependency_leftUnique
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.reservedStrongSelectedStartingLastContact_unique
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.sourceSaturation_owner_unique
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkDependency_rightUnique
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkDependency_no_successor
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkDependency_no_forward_chain
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.oldRequestForkDependency_wellFounded

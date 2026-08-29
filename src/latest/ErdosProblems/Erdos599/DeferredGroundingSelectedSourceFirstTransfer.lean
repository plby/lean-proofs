/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstOwner

/-!
# Transfer of an old request at a displaced source-first point

Suppose the final source-first point `m` on a sacrificed source-grounded
owner is itself the exit of another selected request.  For that request the
owner cannot remain an anonymous competing branch.  Either it is the
request's own starting record, or it survives in the request's truncated
reference warp.  In the first case own-start last-contact normalization ends
at `m`; in the second case source saturation ends at `m` and selects exactly
the sacrificed owner.  In both cases the remaining selected suffix has no
edge.

This is the literal augmenting transfer behind the old-request branch.  It
does not assume a simultaneous matching or coverage statement.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

namespace ReservedStrongSelectedStartingLastContact.SourceSaturation

/-- The exact endpoint transfer for a request whose exit is the maximal
required point on another source-grounded owner.  The two constructors are
the genuine canonical alternatives: own starting record, or a member of the
truncated reference warp selected by source saturation. -/
inductive LastSourceFirstPrefix.RequestExitTransfer
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (request : Request J S.cut) : Type u
  | ownStarting
      (Y : ReservedStrongSelectedStartingLastContact
        (L := L) (hL := hL) (S := S) request)
      (exit_eq : requestExit request = F.boundary)
      (owner_eq : D.owner =
        (reservedStrongSelectedStartingRecord request).record)
      (contact_eq : Y.lastContact.vertex = F.boundary)
      (remaining_steps_eq_nil : Y.remainingErasedRoute.steps = [])
  | sourceSaturated
      (Y : ReservedStrongSelectedStartingLastContact
        (L := L) (hL := hL) (S := S) request)
      (E : SourceSaturation Y)
      (exit_eq : requestExit request = F.boundary)
      (owner_mem : D.owner ∈ Y.truncatedWarp)
      (contact_eq : E.contact.vertex = F.boundary)
      (owner_eq : E.owner = D.owner)
      (remaining_steps_eq_nil : E.remainingSuffix.steps = [])

/-- The owner of a displayed source-first restoration point is an actual
limiting component, rather than the temporary prefix inserted when the
request's own starting record was truncated. -/
theorem LastSourceFirstPrefix.owner_mem_limitWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    D.owner ∈ L.limitWarp := by
  have hbRelevant : F.boundary ∈ reservedStrongSelectedRelevantBB
      (L := L) (hL := hL) (S := S) :=
    reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
  have hcases : D.owner = (.inl X.oldPrefix : Gamma.DPath) ∨
      D.owner ∈ L.limitWarp \
        {(reservedStrongSelectedStartingRecord r).record} := by
    simpa only [ReservedStrongSelectedStartingLastContact.truncatedWarp,
      Set.mem_insert_iff] using D.owner_mem
  rcases hcases with hprefix | hold
  · have hbPrefix : F.boundary ∈ X.oldPrefix.support := by
      have hbPrefix' : F.boundary ∈
          DirectedPath.Path.support
            (Sum.inl X.oldPrefix : Gamma.DPath) := by
        rw [← hprefix]
        exact F.boundary_mem_owner
      exact hbPrefix'
    exact False.elim <| Set.disjoint_left.mp
      (reservedStrongSelectedStartingRecord_disjoint_relevantBB r)
      hbRelevant (X.oldPrefix_support hbPrefix)
  · exact hold.1

/-- An old request at the maximal required point performs an actual
endpoint transfer.  If its starting record is the displayed owner, its
own-start repair ends there.  Otherwise that owner is source-grounded in
the truncated warp, hence source saturation is forced to choose it and to
end there.  The selected suffix after the transfer is empty in either
case. -/
theorem LastSourceFirstPrefix.exists_requestExitTransfer
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (request : Request J S.cut)
    (hexit : requestExit request = F.boundary) :
    Nonempty (F.RequestExitTransfer request) := by
  obtain ⟨Y⟩ := exists_reservedStrongSelectedStartingLastContact
    (L := L) (hL := hL) (S := S) request
  by_cases howner : D.owner =
      (reservedStrongSelectedStartingRecord request).record
  · have hboundaryRecord : F.boundary ∈
        (reservedStrongSelectedStartingRecord request).record.support := by
      rw [← howner]
      exact F.boundary_mem_owner
    have hcontact : Y.lastContact.vertex = F.boundary := by
      rw [← hexit]
      exact Y.lastContact.eq_terminal_of_terminal_mem
        (by simpa only [hexit] using hboundaryRecord)
    exact ⟨.ownStarting Y hexit howner hcontact
      (Y.lastContact.suffixFrom_steps_eq_nil_of_eq_terminal
        (hcontact.trans hexit.symm))⟩
  · have hownerLimit : D.owner ∈ L.limitWarp := F.owner_mem_limitWarp
    have hownerY : D.owner ∈ Y.truncatedWarp :=
      Y.mem_truncatedWarp_of_mem_limitWarp_of_ne_record hownerLimit howner
    have hownerGrounded : D.owner ∈ Y.sourceGroundedOwners :=
      ⟨hownerY, D.owner_source⟩
    have hboundaryCarrier : F.boundary ∈ Y.sourceGroundedCarrier :=
      ⟨D.owner, hownerGrounded, F.boundary_mem_owner⟩
    obtain ⟨E⟩ := Y.exists_sourceSaturation
    have hcontact : E.contact.vertex = F.boundary := by
      rw [← hexit]
      exact E.contact.eq_terminal_of_terminal_mem
        (by simpa only [hexit] using hboundaryCarrier)
    have hownerEq : E.owner = D.owner := by
      apply DWeb.IsWarp.eq_of_mem_support Y.truncatedWarp_isWarp
        E.owner_mem hownerY E.contact_mem_owner
      rw [hcontact]
      exact F.boundary_mem_owner
    exact ⟨.sourceSaturated Y E hexit hownerY hcontact hownerEq
      (E.contact.suffixFrom_steps_eq_nil_of_eq_terminal
        (hcontact.trans hexit.symm))⟩

/-- Distinct requests of the final strong selector have distinct actual
auxiliary sources.  This is a consequence of the selected auxiliary warp,
not an extra matching assumption. -/
theorem reservedStrongSelectedSource_injective :
    Function.Injective
      (reservedStrongSelectedSource
        (L := L) (hL := hL) (S := S)) := by
  intro request request' hsource
  let P := strongSelectedWarp (popularAuxiliaryIndexed L hL) S
    (reservedGroundedCarrierControls L hL S)
  have hpath : strongSelectedPath (popularAuxiliaryIndexed L hL) S
        (reservedGroundedCarrierControls L hL S) request =
      strongSelectedPath (popularAuxiliaryIndexed L hL) S
        (reservedGroundedCarrierControls L hL S) request' := by
    apply P.eq_of_start_eq ⟨request, rfl⟩ ⟨request', rfl⟩
    exact congrArg Subtype.val hsource
  apply GroundingSelection.requestAuxVertex_injective
  rw [← strongSelectedPath_finish (popularAuxiliaryIndexed L hL) S
      (reservedGroundedCarrierControls L hL S) request,
    hpath,
    strongSelectedPath_finish (popularAuxiliaryIndexed L hL) S
      (reservedGroundedCarrierControls L hL S) request']

/-- Consequently the chosen grounded starting record is injective on final
strong-selected requests.  The proof uses uniqueness of the bookkeeping
stage represented by one record and injectivity of the deferred auxiliary
source index. -/
theorem reservedStrongSelectedStartingRecord_injective :
    Function.Injective (fun request : Request J S.cut ↦
      (reservedStrongSelectedStartingRecord request).record) := by
  intro request request' hrecord
  let A := reservedStrongSelectedStartingRecord request
  let B := reservedStrongSelectedStartingRecord request'
  have hrecordAB : A.record = B.record := by
    simpa only [A, B] using hrecord
  have hchosen : L.chosen A.stage = some B.record := by
    rw [A.chosen, hrecordAB]
  have hstage : A.stage = B.stage :=
    (bookkeeping L).chosen_stage_unique hL.legal.validBookkeeping
      hchosen B.chosen
  have hindex : auxiliarySourceIndex L hL.legal
        (reservedStrongSelectedSource request) =
      auxiliarySourceIndex L hL.legal
        (reservedStrongSelectedSource request') :=
    A.source_index.trans (hstage.trans B.source_index.symm)
  exact reservedStrongSelectedSource_injective
    (auxiliarySourceIndex_injective L hL.legal hindex)

/-- No selected starting record can be the owner of a displayed required
source-first point: the former avoids the entire relevant boundary and the
latter contains such a point. -/
theorem LastSourceFirstPrefix.owner_ne_startingRecord
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (request : Request J S.cut) :
    D.owner ≠ (reservedStrongSelectedStartingRecord request).record := by
  intro howner
  have hbRelevant : F.boundary ∈ reservedStrongSelectedRelevantBB
      (L := L) (hL := hL) (S := S) :=
    reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
  have hbRecord : F.boundary ∈
      (reservedStrongSelectedStartingRecord request).record.support := by
    rw [← howner]
    exact F.boundary_mem_owner
  exact Set.disjoint_left.mp
    (reservedStrongSelectedStartingRecord_disjoint_relevantBB request)
      hbRelevant hbRecord

/-- At a genuine source-first owner point the own-start alternative is
impossible: every selected starting record avoids the relevant boundary.
Thus the old request always performs the second, source-saturated transfer
on the displayed target owner. -/
theorem LastSourceFirstPrefix.exists_sourceSaturated_requestExitTransfer
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (request : Request J S.cut)
    (hexit : requestExit request = F.boundary) :
    ∃ (Y : ReservedStrongSelectedStartingLastContact
          (L := L) (hL := hL) (S := S) request)
        (E : SourceSaturation Y),
      D.owner ∈ Y.truncatedWarp ∧
        E.contact.vertex = F.boundary ∧
        E.owner = D.owner ∧
        E.remainingSuffix.steps = [] := by
  obtain ⟨A⟩ := F.exists_requestExitTransfer request hexit
  cases A with
  | ownStarting _ _ owner_eq =>
      exact False.elim (F.owner_ne_startingRecord request owner_eq)
  | sourceSaturated Y E _ owner_mem contact_eq owner_eq hnil =>
      exact ⟨Y, E, owner_mem, contact_eq, owner_eq, hnil⟩

namespace LastSourceFirstPrefix.RequestExitTransfer

/-- The named old request really exits at the owner-cluster boundary. -/
theorem exit_eq
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request) :
    requestExit request = F.boundary := by
  cases A with
  | ownStarting _ h => exact h
  | sourceSaturated _ _ h => exact h

/-- Exact cross-owner carrier condition for two old-request transfers with
different maximal required points.  Their two selected starting records,
the two target owners, and every starting--target pair are all distinct.
These are precisely the four carrier inequalities needed to unite their
finite prefix transactions. -/
theorem distinct_starting_and_target_carriers
    {r s : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) s}
    {D : SourceSaturation X} {E : SourceSaturation Y}
    {F : LastSourceFirstPrefix D} {G : LastSourceFirstPrefix E}
    {request request' : Request J S.cut}
    (A : F.RequestExitTransfer request)
    (B : G.RequestExitTransfer request')
    (hboundary : F.boundary ≠ G.boundary) :
    (reservedStrongSelectedStartingRecord request).record ≠
        (reservedStrongSelectedStartingRecord request').record ∧
      (reservedStrongSelectedStartingRecord request).record ≠ E.owner ∧
      D.owner ≠
        (reservedStrongSelectedStartingRecord request').record ∧
      D.owner ≠ E.owner := by
  have hrequest : request ≠ request' := by
    intro hEq
    subst request'
    exact hboundary (A.exit_eq.symm.trans B.exit_eq)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun hrecords ↦ hrequest
      (reservedStrongSelectedStartingRecord_injective hrecords)
  · exact fun hEq ↦ G.owner_ne_startingRecord request hEq.symm
  · exact F.owner_ne_startingRecord request'
  · intro howner
    exact hboundary (F.boundary_eq_of_owner_eq G howner)

/-- Only the new finite source prefixes contributed by one endpoint
transfer.  The untouched limiting components are deliberately omitted so
that different transactions can be united without duplicating them. -/
def prefixWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request) : Set Gamma.DPath :=
  match A with
  | .ownStarting Y _ _ _ _ => {(.inl Y.oldPrefix : Gamma.DPath)}
  | .sourceSaturated Y E _ _ _ _ _ =>
      {(.inl Y.oldPrefix : Gamma.DPath),
        (.inl E.ownerPrefix : Gamma.DPath)}

private theorem deferred_limitWarp_isWarp
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :
    Gamma.IsWarp L.limitWarp := by
  simpa only [popularAuxiliaryInput, limitWarp] using
    (popularAuxiliaryInput L hL.legal).ladder.disjoint

private theorem startingRecord_mem_limitWarp
    (request : Request J S.cut) :
    (reservedStrongSelectedStartingRecord request).record ∈ L.limitWarp := by
  simpa only [popularAuxiliaryInput, limitWarp] using
    (reservedStrongSelectedStartingRecord request).record_mem_ladder

private theorem finitePrefixes_disjoint_of_carriers
    (hL : IsKappaHindrance L)
    {P Q : Gamma.DPath}
    (hP : P ∈ L.limitWarp) (hQ : Q ∈ L.limitWarp) (hne : P ≠ Q)
    (p q : FinitePath Gamma.graph)
    (hp : p.support ⊆ P.support) (hq : q.support ⊆ Q.support) :
    Disjoint p.support q.support :=
  (deferred_limitWarp_isWarp L hL hP hQ hne).mono hp hq

/-- The one- or two-prefix contribution of a single old-request transfer is
itself a warp.  In the two-prefix case the selected starting record and the
target owner are distinct because only the latter contains a relevant
source-first point. -/
theorem prefixWarp_isWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request) :
    Gamma.IsWarp A.prefixWarp := by
  cases A with
  | ownStarting Y =>
      intro p hp q hq hpq
      simp only [prefixWarp, Set.mem_singleton_iff] at hp hq
      exact False.elim (hpq (hp.trans hq.symm))
  | sourceSaturated Y E _ _ _ owner_eq _ =>
      intro p hp q hq hpq
      simp only [prefixWarp, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact False.elim (hpq rfl)
      · apply finitePrefixes_disjoint_of_carriers
          hL
          (startingRecord_mem_limitWarp request) F.owner_mem_limitWarp
          (F.owner_ne_startingRecord request).symm
          Y.oldPrefix E.ownerPrefix Y.oldPrefix_support
        rw [← owner_eq]
        exact E.prefix_support
      · exact (finitePrefixes_disjoint_of_carriers
          hL
          (startingRecord_mem_limitWarp request) F.owner_mem_limitWarp
          (F.owner_ne_startingRecord request).symm
          Y.oldPrefix E.ownerPrefix Y.oldPrefix_support (by
            rw [← owner_eq]
            exact E.prefix_support)).symm
      · exact False.elim (hpq rfl)

/-- Every prefix member remembers one of its two genuine limiting carriers:
the selected starting record, or the target source owner. -/
theorem prefixWarp_member_carrier
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request)
    {p : Gamma.DPath} (hp : p ∈ A.prefixWarp) :
    (p.support ⊆
        (reservedStrongSelectedStartingRecord request).record.support) ∨
      p.support ⊆ D.owner.support := by
  cases A with
  | ownStarting Y _ owner_eq _ _ =>
      simp only [prefixWarp, Set.mem_singleton_iff] at hp
      subst p
      exact Or.inl Y.oldPrefix_support
  | sourceSaturated Y E _ _ _ owner_eq _ =>
      simp only [prefixWarp, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact Or.inl Y.oldPrefix_support
      · right
        rw [← owner_eq]
        exact E.prefix_support

/-- Two old-request transactions at different maximal source-first points
have pairwise disjoint finite-prefix contributions.  This is the exact
two-splice coexistence theorem: it follows from the selected-source
injectivity and boundary avoidance, rather than from a postulated matching. -/
theorem disjoint_prefixWarp_of_boundary_ne
    {r s : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) s}
    {D : SourceSaturation X} {E : SourceSaturation Y}
    {F : LastSourceFirstPrefix D} {G : LastSourceFirstPrefix E}
    {request request' : Request J S.cut}
    (A : F.RequestExitTransfer request)
    (B : G.RequestExitTransfer request')
    (hboundary : F.boundary ≠ G.boundary) :
    Disjoint (Gamma.vertexSet A.prefixWarp)
      (Gamma.vertexSet B.prefixWarp) := by
  obtain ⟨hSS, hSE, hDS, hDE⟩ :=
    A.distinct_starting_and_target_carriers B hboundary
  rw [Set.disjoint_left]
  intro x hxA hxB
  obtain ⟨p, hpA, hxp⟩ := hxA
  obtain ⟨q, hqB, hxq⟩ := hxB
  rcases A.prefixWarp_member_carrier hpA with hpS | hpD <;>
    rcases B.prefixWarp_member_carrier hqB with hqS | hqE
  · exact Set.disjoint_left.mp
      (deferred_limitWarp_isWarp L hL
        (startingRecord_mem_limitWarp request)
        (startingRecord_mem_limitWarp request') hSS)
        (hpS hxp) (hqS hxq)
  · exact Set.disjoint_left.mp
      (deferred_limitWarp_isWarp L hL
        (startingRecord_mem_limitWarp request) G.owner_mem_limitWarp hSE)
        (hpS hxp) (hqE hxq)
  · exact Set.disjoint_left.mp
      (deferred_limitWarp_isWarp L hL F.owner_mem_limitWarp
        (startingRecord_mem_limitWarp request') hDS)
        (hpD hxp) (hqS hxq)
  · exact Set.disjoint_left.mp
      (deferred_limitWarp_isWarp L hL F.owner_mem_limitWarp
        G.owner_mem_limitWarp hDE)
        (hpD hxp) (hqE hxq)

/-- Hence the literal union of the two finite prefix transactions is a
warp. -/
theorem union_prefixWarp_isWarp_of_boundary_ne
    {r s : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) s}
    {D : SourceSaturation X} {E : SourceSaturation Y}
    {F : LastSourceFirstPrefix D} {G : LastSourceFirstPrefix E}
    {request request' : Request J S.cut}
    (A : F.RequestExitTransfer request)
    (B : G.RequestExitTransfer request')
    (hboundary : F.boundary ≠ G.boundary) :
    Gamma.IsWarp (A.prefixWarp ∪ B.prefixWarp) := by
  intro p hp q hq hpq
  rcases hp with hpA | hpB <;> rcases hq with hqA | hqB
  · exact A.prefixWarp_isWarp hpA hqA hpq
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.mp
      (A.disjoint_prefixWarp_of_boundary_ne B hboundary)
        ⟨p, hpA, hxp⟩ ⟨q, hqB, hxq⟩
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.mp
      (A.disjoint_prefixWarp_of_boundary_ne B hboundary).symm
        ⟨p, hpB, hxp⟩ ⟨q, hqA, hxq⟩
  · exact B.prefixWarp_isWarp hpB hqB hpq

/-- The literal reference warp after the endpoint transfer.  In the
own-start case this is the ordinary own-prefix truncation; in the other
case it is the source-saturated prefix replacement. -/
def transferWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request) : Set Gamma.DPath :=
  match A with
  | .ownStarting Y _ _ _ _ => Y.truncatedWarp
  | .sourceSaturated _ E _ _ _ _ _ => E.saturatedWarp

/-- The endpoint transfer is an actual warp in both canonical branches. -/
theorem transferWarp_isWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request) :
    Gamma.IsWarp A.transferWarp := by
  cases A with
  | ownStarting Y => exact Y.truncatedWarp_isWarp
  | sourceSaturated _ E => exact E.saturatedWarp_isWarp

/-- Any source prefix to the maximal required owner point reaches every
required source-first point on that owner.  This is the common path argument
used by both endpoint-transfer branches. -/
theorem reaches_every_owner_boundary_of_prefix
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    (p : FinitePath Gamma.graph)
    (hpStart : p.start = D.owner.initial)
    (hpSource : p.start ∈ Gamma.source)
    (hpFinish : p.finish = F.boundary)
    (hpEdges : p.edgeSet ⊆ D.owner.edgeSet)
    {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ D.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ p.edgeSet) a z := by
  obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix D.owner hzOwner
  have hfinishBefore : GroundingCut.BeforeEq D.owner q.finish p.finish := by
    simpa only [hqFinish, hpFinish] using F.maximal hz hzOwner
  have hlen : q.walk.length ≤ p.walk.length :=
    initialSubpath_length_le_of_beforeEq_finish D.owner q p
      hqStart hpStart hqEdges hpEdges hfinishBefore
  have hprefix : q.IsPrefixOf p :=
    initialSubpath_isPrefixOf_of_length_le D.owner q p
      hqStart hpStart hqEdges hpEdges hlen
  have hedge : q.edgeSet ⊆ p.edgeSet :=
    q.walk.edgeSet_subset_of_support_prefix p.walk hprefix
  refine ⟨q.start, ?_, ?_⟩
  · rw [hqStart, ← hpStart]
    exact hpSource
  · have hwalk := Alternating.Walk.reflTransGen_edgeSet q.walk
    simpa only [hqFinish] using
      Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ q.edgeSet)
        (p := fun x y ↦ (x, y) ∈ p.edgeSet)
        (fun _ _ he ↦ hedge he) q.start q.finish hwalk

/-- The transferred reference warp roots every required source-first point
on the sacrificed owner.  Thus the old-request branch resolves all
same-owner obligations at once; it does not merely root the named exit. -/
theorem roots_every_owner_boundary
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request)
    {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ D.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ Alternating.familyEdges A.transferWarp) a z := by
  cases A with
  | ownStarting Y _ owner_eq contact_eq _ =>
      have hpStart : Y.oldPrefix.start = D.owner.initial := by
        rw [owner_eq]
        exact Y.oldPrefix_start
      have hpFinish : Y.oldPrefix.finish = F.boundary :=
        Y.oldPrefix_finish.trans contact_eq
      have hpEdges : Y.oldPrefix.edgeSet ⊆ D.owner.edgeSet := by
        rw [owner_eq]
        exact Y.oldPrefix_edges
      obtain ⟨a, ha, hreach⟩ :=
        reaches_every_owner_boundary_of_prefix F Y.oldPrefix
          hpStart Y.oldPrefix_source hpFinish hpEdges hz hzOwner
      refine ⟨a, ha, Relation.ReflTransGen.mono ?_ a z hreach⟩
      intro x y hxy
      simp only [transferWarp, Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨(.inl Y.oldPrefix : Gamma.DPath), Set.mem_insert _ _, hxy⟩
  | sourceSaturated Y E _ _ contact_eq owner_eq _ =>
      have hpStart : E.ownerPrefix.start = D.owner.initial := by
        rw [← owner_eq]
        exact E.prefix_start
      have hpFinish : E.ownerPrefix.finish = F.boundary :=
        E.prefix_finish.trans contact_eq
      have hpEdges : E.ownerPrefix.edgeSet ⊆ D.owner.edgeSet := by
        rw [← owner_eq]
        exact E.prefix_edges
      obtain ⟨a, ha, hreach⟩ :=
        reaches_every_owner_boundary_of_prefix F E.ownerPrefix
          hpStart E.prefix_source hpFinish hpEdges hz hzOwner
      refine ⟨a, ha, Relation.ReflTransGen.mono ?_ a z hreach⟩
      intro x y hxy
      simp only [transferWarp, Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨(.inl E.ownerPrefix : Gamma.DPath), Set.mem_insert _ _, hxy⟩

/-- The endpoint transfer never sacrifices the globally reserved record.
In the saturated branch it is not the removed owner because that owner
contains a relevant-boundary point, whereas the reserved record is disjoint
from the entire relevant boundary. -/
theorem canonicalReservedRecord_mem_transferWarp
    {r : Request J S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} {F : LastSourceFirstPrefix D}
    {request : Request J S.cut}
    (A : F.RequestExitTransfer request) :
    (canonicalReservedRecord L hL S).record ∈ A.transferWarp := by
  let R := canonicalReservedRecord L hL S
  have hRLimit : R.record ∈ L.limitWarp := R.limit_inessential.1
  have hRStartNe : R.record ≠
      (reservedStrongSelectedStartingRecord request).record :=
    canonicalReservedRecord_ne_reservedStrongSelectedStartingRecord request
  have hownerNe : R.record ≠ D.owner := by
    intro hEq
    have hbRelevant : F.boundary ∈ reservedStrongSelectedRelevantBB
        (L := L) (hL := hL) (S := S) :=
      reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
    have hbRecord : F.boundary ∈ R.record.support := by
      rw [hEq]
      exact F.boundary_mem_owner
    exact Set.disjoint_left.mp
      canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
        hbRelevant hbRecord
  cases A with
  | ownStarting Y =>
      exact Y.mem_truncatedWarp_of_mem_limitWarp_of_ne_record
        hRLimit hRStartNe
  | sourceSaturated Y E _ _ _ owner_eq _ =>
      have hRY : R.record ∈ Y.truncatedWarp :=
        Y.mem_truncatedWarp_of_mem_limitWarp_of_ne_record hRLimit hRStartNe
      exact Set.mem_insert_of_mem _ ⟨hRY, by
        simpa only [Set.mem_singleton_iff, owner_eq] using hownerNe⟩

end LastSourceFirstPrefix.RequestExitTransfer

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_requestExitTransfer
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.RequestExitTransfer.roots_every_owner_boundary
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.RequestExitTransfer.canonicalReservedRecord_mem_transferWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.reservedStrongSelectedStartingRecord_injective
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.RequestExitTransfer.distinct_starting_and_target_carriers
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.exists_sourceSaturated_requestExitTransfer
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.RequestExitTransfer.union_prefixWarp_isWarp_of_boundary_ne

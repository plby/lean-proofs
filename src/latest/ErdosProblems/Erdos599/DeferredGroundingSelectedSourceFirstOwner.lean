/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstOrder
import ErdosProblems.Erdos599.GroundingBBGeometry
import ErdosProblems.Erdos599.CountableAssignment
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# The actual owner of a displaced deferred source-first sink

The strict tail left by source-owner saturation is not an anonymous old
terminal.  Membership in the final relevant boundary identifies the
displaced point in one of the construction's genuine roles.  A finite
auxiliary source identifies the sacrificed owner with the corresponding
deferred recorded (and hence limiting-inessential) path.  An old cut point
retains its request.  A blocking point identifies the sacrificed owner with
the exact retained fragment parent; in a normalized web an escaping blocker
cannot be another ambient source and therefore carries the literal virtual
escape.  The only remaining blocking case is the named finite fragment
ending in the essential terminal cut.
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

/-- The one globally reserved record is not the starting record of any
actual final strong-selected request.  The proof uses the represented
auxiliary source, so it applies uniformly to finite and proxy records. -/
theorem canonicalReservedRecord_ne_reservedStrongSelectedStartingRecord
    (r : Request (popularAuxiliaryInput L hL.legal) S.cut) :
    (canonicalReservedRecord L hL S).record ≠
      (reservedStrongSelectedStartingRecord r).record := by
  intro hrecordEq
  let R := canonicalReservedRecord L hL S
  let A := reservedStrongSelectedStartingRecord r
  apply reservedStrongSelectedPath_start_ne_reservedSource r
  change (reservedStrongSelectedSource r).1 = R.auxiliarySource.1
  rcases R.source_represents with ⟨p, hRp, hRsource⟩ |
      ⟨i, hRi, hRsource⟩ <;>
    rcases A.represents with ⟨q, hAq, hAsource⟩ |
      ⟨j, hAj, hAsource⟩
  · have hpq : p = q := by
      have hpaths : (Sum.inl p : Gamma.DPath) = Sum.inl q :=
        hRp.symm.trans (hrecordEq.trans hAq)
      exact Sum.inl.inj hpaths
    rw [hAsource, hRsource, hpq]
  · have hfalse : (Sum.inl p : Gamma.DPath) = (J).proxyPath j :=
      hRp.symm.trans (hrecordEq.trans hAj)
    obtain ⟨ray, hproxy⟩ := (J).proxy_isRay j
    rw [hproxy] at hfalse
    cases hfalse
  · have hfalse : (J).proxyPath i = (Sum.inl q : Gamma.DPath) :=
      hRi.symm.trans (hrecordEq.trans hAq)
    obtain ⟨ray, hproxy⟩ := (J).proxy_isRay i
    rw [hproxy] at hfalse
    cases hfalse
  · have hij : i = j := by
      apply Subtype.ext
      have hpaths : (J).proxyPath i = (J).proxyPath j :=
        hRi.symm.trans (hrecordEq.trans hAj)
      simpa only [popularAuxiliaryInput, infinitePath] using hpaths
    rw [hAsource, hRsource, hij]

/-- The construction-side identity of a source-first boundary point which
lies strictly after the saturation contact on the sacrificed source owner. -/
inductive StrictSourceFirstOwnerOutcome
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) (b : V) : Prop
  | finiteRecord
      (source : (J).lambda.source)
      (source_value : source.1 =
        PopularAuxiliary.Input.LambdaVertex.old b)
      (record : DeferredAuxiliarySourceRecord L hL.legal source)
      (owner_eq : D.owner = record.record)
      (owner_terminal : Gamma.terminal? D.owner = some b)
      (owner_inessential :
        D.owner ∈ Gamma.inessentialPaths L.limitWarp)
      (finiteOwner : FinitePath Gamma.graph)
      (owner_eq_finite : D.owner = .inl finiteOwner)
      (prefix_length_lt_owner :
        D.ownerPrefix.walk.length < finiteOwner.walk.length)
  | oldRequest
      (request : Request J S.cut)
      (apex_eq : requestAuxVertex request = .old b)
      (exit_eq : requestExit request = b)
  | virtualEscape
      (fragment : (J).Fragment)
      (fragment_mem : fragment ∈
        (reservedStrongSelectedPruningData
          (L := L) (hL := hL) (S := S)).relevantG0)
      (owner_eq : D.owner = fragment.parent)
      (blocker_eq : GroundingCut.blockingPoint J S.cut fragment = b)
      (meetsEscape : fragment.MeetsEscape J S.cut)
      (escape : GroundingInputRelevantDecoder.RelevantVirtualEscape
        J S.cut b)
  | essentialTerminalFragment
      (fragment : (J).Fragment)
      (fragment_mem : fragment ∈
        (reservedStrongSelectedPruningData
          (L := L) (hL := hL) (S := S)).relevantG0)
      (owner_eq : D.owner = fragment.parent)
      (blocker_eq : GroundingCut.blockingPoint J S.cut fragment = b)
      (not_meetsEscape : ¬ fragment.MeetsEscape J S.cut)
      (fragment_terminal : fragment.path.terminal? = some b)
      (terminalCut_mem : b ∈ (J).terminalCut)
      (owner_essential : D.owner ∈ (J).essentialLadder)
      (owner_terminal : Gamma.terminal? D.owner = some b)
      (finiteOwner : FinitePath Gamma.graph)
      (owner_eq_finite : D.owner = .inl finiteOwner)
      (prefix_length_lt_owner :
        D.ownerPrefix.walk.length < finiteOwner.walk.length)

private theorem owner_mem_limitWarp
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support) :
    D.owner ∈ L.limitWarp := by
  have hbRelevant : b ∈ reservedStrongSelectedRelevantBB
      (L := L) (hL := hL) (S := S) :=
    reservedStrongSelectedSourceFirstBB_subset_relevantBB hb
  have hcases : D.owner = (.inl X.oldPrefix : Gamma.DPath) ∨
      D.owner ∈ L.limitWarp \
        {(reservedStrongSelectedStartingRecord r).record} := by
    simpa only [ReservedStrongSelectedStartingLastContact.truncatedWarp,
      Set.mem_insert_iff] using D.owner_mem
  rcases hcases with hprefix | hold
  · have hbPrefix : b ∈ X.oldPrefix.support := by
      have hbPrefix' :
          b ∈ DirectedPath.Path.support
            (Sum.inl X.oldPrefix : Gamma.DPath) := by
        rw [← hprefix]
        exact hbOwner
      exact hbPrefix'
    exact False.elim <| Set.disjoint_left.mp
      (reservedStrongSelectedStartingRecord_disjoint_relevantBB r)
      hbRelevant (X.oldPrefix_support hbPrefix)
  · exact hold.1

private theorem owner_eq_of_common_limit_vertex
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support)
    (Y : Gamma.DPath) (hY : Y ∈ L.limitWarp) (hbY : b ∈ Y.support) :
    D.owner = Y := by
  have hwarp : Gamma.IsWarp L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using (J).ladder.disjoint
  exact DWeb.IsWarp.eq_of_mem_support hwarp
    (D.owner_mem_limitWarp hb hbOwner) hY hbOwner hbY

private theorem strict_boundary_not_source
    (hGamma : Gamma.IsNormalized)
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hbOwner : b ∈ D.owner.support)
    (hstrict : GroundingCut.Before D.owner D.contact.vertex b) :
    b ∉ Gamma.source := by
  intro hbSource
  have hbInitial : b = D.owner.initial :=
    Alternating.path_eq_initial_of_mem_support_of_mem_source
      hGamma D.owner hbOwner hbSource
  have hinitialBefore : GroundingCut.BeforeEq D.owner
      D.owner.initial D.contact.vertex :=
    GroundingFragmentWarp.initial_beforeEq_of_mem D.contact_mem_owner
  have hcontactInitial : D.contact.vertex = D.owner.initial :=
    GroundingCutDecoder.beforeEq_antisymm
      (by simpa only [hbInitial] using hstrict.1) hinitialBefore
  exact hstrict.2 (hcontactInitial.trans hbInitial.symm)

/-- A strict point which is the terminal of the sacrificed owner gives a
literal finite owner and a strict natural-number bound on the retained
prefix. -/
private theorem finite_owner_and_prefix_lt_of_terminal
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hstrict : GroundingCut.Before D.owner D.contact.vertex b)
    (hterminal : Gamma.terminal? D.owner = some b) :
    ∃ p : FinitePath Gamma.graph,
      D.owner = .inl p ∧
        D.ownerPrefix.walk.length < p.walk.length := by
  cases howner : D.owner with
  | inl p =>
      have hterminal' := hterminal
      rw [howner] at hterminal'
      change some p.finish = some b at hterminal'
      have hpFinish : p.finish = b := Option.some.inj hterminal'
      have hbefore : GroundingCut.Before D.owner
          D.ownerPrefix.finish p.finish := by
        simpa only [D.prefix_finish, hpFinish] using hstrict
      have hlength := initialSubpath_length_lt_of_before_finish
        D.owner D.ownerPrefix p D.prefix_start (by
          rw [howner]
          change p.start = p.start
          rfl) D.prefix_edges (by
            rw [howner]
            change p.edgeSet ⊆ p.edgeSet
            exact Set.Subset.rfl) hbefore
      exact ⟨p, rfl, hlength⟩
  | inr ray =>
      have hterminal' := hterminal
      rw [howner] at hterminal'
      change (none : Option V) = some b at hterminal'
      have hfalse : (none : Option V) = some b := by
        exact hterminal'
      cases hfalse

/-- The last required source-first point on one finite sacrificed owner.
Its source prefix simultaneously reaches every required point of that owner,
and its length is strictly larger than the prefix retained by saturation. -/
structure LastSourceFirstPrefix
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) where
  boundary : V
  boundary_mem : boundary ∈ reservedStrongSelectedSourceFirstBB
    (L := L) (hL := hL) (S := S)
  boundary_mem_owner : boundary ∈ D.owner.support
  sourcePrefix : FinitePath Gamma.graph
  sourcePrefix_start : sourcePrefix.start = D.owner.initial
  sourcePrefix_source : sourcePrefix.start ∈ Gamma.source
  sourcePrefix_finish : sourcePrefix.finish = boundary
  sourcePrefix_support : sourcePrefix.support ⊆ D.owner.support
  sourcePrefix_edges : sourcePrefix.edgeSet ⊆ D.owner.edgeSet
  maximal : ∀ {z : V},
    z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S) →
    z ∈ D.owner.support →
      GroundingCut.BeforeEq D.owner z boundary
  contact_before : GroundingCut.Before D.owner D.contact.vertex boundary
  retained_length_lt :
    D.ownerPrefix.walk.length < sourcePrefix.walk.length

/-- A single strict required point on a finite owner determines a final one.
Replacing the retained owner prefix by this displayed prefix therefore
restores every source-first obligation on that owner in one finite step. -/
theorem exists_lastSourceFirstPrefix
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) (p : FinitePath Gamma.graph)
    (howner : D.owner = .inl p) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support)
    (hstrict : GroundingCut.Before D.owner D.contact.vertex b) :
    Nonempty (LastSourceFirstPrefix D) := by
  classical
  let T := reservedStrongSelectedSourceFirstBB
    (L := L) (hL := hL) (S := S)
  let contacts : Finset (Fin p.walk.support.length) :=
    Finset.univ.filter fun i ↦ p.walk.support[i] ∈ T
  have hbP : b ∈ p.walk.support := by
    have hbOwner' := hbOwner
    rw [howner] at hbOwner'
    exact hbOwner'
  obtain ⟨ib, hib⟩ := List.get_of_mem hbP
  have hibContact : ib ∈ contacts := by
    simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
    change p.walk.support.get ib ∈ T
    simpa only [hib] using hb
  let imax : Fin p.walk.support.length :=
    contacts.max' ⟨ib, hibContact⟩
  have himaxContact : imax ∈ contacts :=
    Finset.max'_mem contacts ⟨ib, hibContact⟩
  let m : V := p.walk.support[imax]
  have hmT : m ∈ T := by
    have h := himaxContact
    simp only [contacts, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    exact h
  have hmP : m ∈ p.walk.support := List.getElem_mem imax.2
  have hmOwner : m ∈ D.owner.support := by
    rw [howner]
    exact hmP
  have hmax : ∀ {z : V}, z ∈ T → z ∈ D.owner.support →
      GroundingCut.BeforeEq D.owner z m := by
    intro z hzT hzOwner
    have hzP : z ∈ p.walk.support := by
      rw [howner] at hzOwner
      exact hzOwner
    obtain ⟨iz, hiz⟩ := List.get_of_mem hzP
    have hizContact : iz ∈ contacts := by
      simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
      change p.walk.support.get iz ∈ T
      simpa only [hiz] using hzT
    have hizLe : iz ≤ imax := Finset.le_max' contacts iz hizContact
    rw [howner]
    exact ⟨iz.1, imax.1, ⟨iz.2, hiz⟩, ⟨imax.2, rfl⟩, hizLe⟩
  have hbBeforeMax : GroundingCut.BeforeEq D.owner b m :=
    hmax hb hbOwner
  have hcontactBeforeEq : GroundingCut.BeforeEq D.owner
      D.contact.vertex m :=
    GroundingFragmentResidualOrder.beforeEq_trans hstrict.1 hbBeforeMax
  have hcontactNe : D.contact.vertex ≠ m := by
    intro hcontactM
    have hbBeforeContact : GroundingCut.BeforeEq D.owner b D.contact.vertex := by
      simpa only [hcontactM] using hbBeforeMax
    exact hstrict.2
      (GroundingCutDecoder.beforeEq_antisymm hstrict.1 hbBeforeContact)
  have hcontactBefore : GroundingCut.Before D.owner
      D.contact.vertex m := ⟨hcontactBeforeEq, hcontactNe⟩
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix D.owner hmOwner
  have hfinishBefore : GroundingCut.Before D.owner
      D.ownerPrefix.finish q.finish := by
    simpa only [D.prefix_finish, hqFinish] using hcontactBefore
  have hlength : D.ownerPrefix.walk.length < q.walk.length :=
    initialSubpath_length_lt_of_before_finish D.owner D.ownerPrefix q
      D.prefix_start hqStart D.prefix_edges hqEdges hfinishBefore
  exact ⟨{
    boundary := m
    boundary_mem := hmT
    boundary_mem_owner := hmOwner
    sourcePrefix := q
    sourcePrefix_start := hqStart
    sourcePrefix_source := hqStart ▸ D.owner_source
    sourcePrefix_finish := hqFinish
    sourcePrefix_support := hqSupport
    sourcePrefix_edges := hqEdges
    maximal := fun hzT hzOwner ↦ hmax hzT hzOwner
    contact_before := hcontactBefore
    retained_length_lt := hlength }⟩

/-- The displayed final prefix is not merely an endpoint certificate: its
edge set reaches every required source-first point on the sacrificed owner.
Thus retaining this one prefix restores all same-owner obligations at once. -/
theorem LastSourceFirstPrefix.reaches_every_owner_boundary
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ D.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ F.sourcePrefix.edgeSet) a z := by
  obtain ⟨q, hqStart, hqFinish, _hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix D.owner hzOwner
  have hfinishBefore : GroundingCut.BeforeEq D.owner
      q.finish F.sourcePrefix.finish := by
    simpa only [hqFinish, F.sourcePrefix_finish] using
      F.maximal hz hzOwner
  have hlen : q.walk.length ≤ F.sourcePrefix.walk.length :=
    initialSubpath_length_le_of_beforeEq_finish D.owner q F.sourcePrefix
      hqStart F.sourcePrefix_start hqEdges F.sourcePrefix_edges hfinishBefore
  have hprefix : q.IsPrefixOf F.sourcePrefix :=
    initialSubpath_isPrefixOf_of_length_le D.owner q F.sourcePrefix
      hqStart F.sourcePrefix_start hqEdges F.sourcePrefix_edges hlen
  have hedge : q.edgeSet ⊆ F.sourcePrefix.edgeSet :=
    q.walk.edgeSet_subset_of_support_prefix F.sourcePrefix.walk hprefix
  refine ⟨q.start, ?_, ?_⟩
  · rw [hqStart, ← F.sourcePrefix_start]
    exact F.sourcePrefix_source
  · have hwalk := Alternating.Walk.reflTransGen_edgeSet q.walk
    simpa only [hqFinish] using
      Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ q.edgeSet)
        (p := fun x y ↦ (x, y) ∈ F.sourcePrefix.edgeSet)
        (fun _ _ he ↦ hedge he) q.start q.finish hwalk

/-- Two finite restoration states which choose the same required point
necessarily belong to the same limiting owner.  This is the injectivity
half of the owner--boundary matching used by the simultaneous transaction. -/
theorem LastSourceFirstPrefix.owner_eq_of_boundary_eq
    {r s : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) s}
    {D : SourceSaturation X} {E : SourceSaturation Y}
    (F : LastSourceFirstPrefix D) (G : LastSourceFirstPrefix E)
    (hboundary : F.boundary = G.boundary) :
    D.owner = E.owner := by
  have hD : D.owner ∈ L.limitWarp :=
    D.owner_mem_limitWarp F.boundary_mem F.boundary_mem_owner
  have hE : E.owner ∈ L.limitWarp :=
    E.owner_mem_limitWarp G.boundary_mem G.boundary_mem_owner
  have hcommonD : F.boundary ∈ D.owner.support :=
    F.boundary_mem_owner
  have hcommonE : F.boundary ∈ E.owner.support := by
    rw [hboundary]
    exact G.boundary_mem_owner
  have hwarp : Gamma.IsWarp L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using (J).ladder.disjoint
  exact DWeb.IsWarp.eq_of_mem_support hwarp hD hE hcommonD hcommonE

/-- Conversely, maximality makes the restoration point intrinsic to its
owner: two restoration states for the same owner choose the same last
required source-first point. -/
theorem LastSourceFirstPrefix.boundary_eq_of_owner_eq
    {r s : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {Y : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) s}
    {D : SourceSaturation X} {E : SourceSaturation Y}
    (F : LastSourceFirstPrefix D) (G : LastSourceFirstPrefix E)
    (howner : D.owner = E.owner) :
    F.boundary = G.boundary := by
  have hGmemD : G.boundary ∈ D.owner.support := by
    rw [howner]
    exact G.boundary_mem_owner
  have hFmemE : F.boundary ∈ E.owner.support := by
    rw [← howner]
    exact F.boundary_mem_owner
  have hGF : GroundingCut.BeforeEq D.owner G.boundary F.boundary :=
    F.maximal G.boundary_mem hGmemD
  have hFG' : GroundingCut.BeforeEq E.owner F.boundary G.boundary :=
    G.maximal F.boundary_mem hFmemE
  have hFG : GroundingCut.BeforeEq D.owner F.boundary G.boundary := by
    simpa only [howner] using hFG'
  exact GroundingCutDecoder.beforeEq_antisymm hFG hGF

/-- Replace the sacrificed owner by the one maximal source prefix which
restores all of its required source-first points.  This is the owner side
of the finite sink trade; every other truncated-warp component is kept. -/
def LastSourceFirstPrefix.restoredWarp
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    Set Gamma.DPath :=
  insert (.inl F.sourcePrefix : Gamma.DPath)
    (X.truncatedWarp \ {D.owner})

/-- The exact finite owner restoration is again a warp. -/
theorem LastSourceFirstPrefix.restoredWarp_isWarp
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    Gamma.IsWarp F.restoredWarp := by
  apply DWeb.IsWarp.insert_finite_of_disjoint Gamma
    (DWeb.IsWarp.sdiff_singleton Gamma X.truncatedWarp_isWarp D.owner)
      F.sourcePrefix
  rw [Set.disjoint_left]
  intro x hxPrefix hxRest
  obtain ⟨p, hpRest, hxp⟩ := hxRest
  have hne : D.owner ≠ p := by
    intro hEq
    subst p
    exact hpRest.2 (Set.mem_singleton D.owner)
  exact Set.disjoint_left.mp
    (X.truncatedWarp_isWarp D.owner_mem hpRest.1 hne)
      (F.sourcePrefix_support hxPrefix) hxp

/-- Owner restoration changes no source initial. -/
theorem LastSourceFirstPrefix.initialSet_restoredWarp
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    Gamma.initialSet F.restoredWarp = Gamma.initialSet X.truncatedWarp := by
  rw [LastSourceFirstPrefix.restoredWarp,
    Gamma.initialSet_insert_finite,
    DWeb.IsWarp.initialSet_sdiff_singleton Gamma
      X.truncatedWarp_isWarp D.owner_mem,
    F.sourcePrefix_start]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | hx)
    · exact ⟨D.owner, D.owner_mem, rfl⟩
    · exact hx.1
  · intro hx
    by_cases hxeq : x = D.owner.initial
    · exact Or.inl hxeq
    · exact Or.inr ⟨hx, hxeq⟩

/-- The global reserved record is an untouched whole member of the finite
owner-restoration warp.  The selected starting record is different by its
represented auxiliary source, while the sacrificed owner is different
because it contains the displayed relevant-boundary point and the reserved
record is disjoint from the whole relevant boundary. -/
theorem LastSourceFirstPrefix.canonicalReservedRecord_mem_restoredWarp
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    (canonicalReservedRecord L hL S).record ∈ F.restoredWarp := by
  let R := canonicalReservedRecord L hL S
  have hRLimit : R.record ∈ L.limitWarp := R.limit_inessential.1
  have hRStartNe : R.record ≠
      (reservedStrongSelectedStartingRecord r).record :=
    canonicalReservedRecord_ne_reservedStrongSelectedStartingRecord r
  have hRX : R.record ∈ X.truncatedWarp :=
    X.mem_truncatedWarp_of_mem_limitWarp_of_ne_record hRLimit hRStartNe
  have hownerNe : D.owner ≠ R.record := by
    intro hEq
    have hbRelevant : F.boundary ∈ reservedStrongSelectedRelevantBB
        (L := L) (hL := hL) (S := S) :=
      reservedStrongSelectedSourceFirstBB_subset_relevantBB F.boundary_mem
    have hbRecord : F.boundary ∈ R.record.support := by
      rw [← hEq]
      exact F.boundary_mem_owner
    exact Set.disjoint_left.mp
      canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
        hbRelevant hbRecord
  exact Set.mem_insert_of_mem _ ⟨hRX, by
    simpa only [Set.mem_singleton_iff] using hownerNe.symm⟩

/-- The transaction replaces precisely the sacrificed owner's terminal by
the chosen last required source-first point. -/
theorem LastSourceFirstPrefix.terminalFrontier_restoredWarp
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D) :
    Gamma.terminalFrontier F.restoredWarp =
      insert F.boundary
        (Gamma.terminalFrontier (X.truncatedWarp \ {D.owner})) := by
  rw [LastSourceFirstPrefix.restoredWarp,
    Gamma.terminalFrontier_insert_finite, F.sourcePrefix_finish]

/-- In the restored relation every required source-first point on the
sacrificed owner has a literal ambient-source root. -/
theorem LastSourceFirstPrefix.restoredWarp_roots_owner_boundaries
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    {D : SourceSaturation X} (F : LastSourceFirstPrefix D)
    {z : V}
    (hz : z ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hzOwner : z ∈ D.owner.support) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ Alternating.familyEdges F.restoredWarp) a z := by
  obtain ⟨a, ha, hreach⟩ := F.reaches_every_owner_boundary hz hzOwner
  refine ⟨a, ha, ?_⟩
  apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ F.sourcePrefix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ Alternating.familyEdges F.restoredWarp)
      ?_ a z hreach
  intro x y hxy
  simp only [Alternating.familyEdges, Set.mem_iUnion]
  exact ⟨(.inl F.sourcePrefix : Gamma.DPath), Set.mem_insert _ _, hxy⟩

private theorem finiteSource_owner_record
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support)
    (hbFinite : b ∈ (J).finiteSource) :
    ∃ (source : (J).lambda.source)
        (record : DeferredAuxiliarySourceRecord L hL.legal source),
      source.1 = .old b ∧ D.owner = record.record ∧
        Gamma.terminal? D.owner = some b ∧
        D.owner ∈ Gamma.inessentialPaths L.limitWarp := by
  let source : (J).lambda.source :=
    ⟨PopularAuxiliary.Input.LambdaVertex.old b,
      ((J).mem_lambda_source_old b).2 hbFinite⟩
  let record := deferredAuxiliarySourceRecord L hL.legal source
  have hrecordLimit : record.record ∈ L.limitWarp := by
    simpa only [popularAuxiliaryInput, limitWarp] using
      record.record_mem_ladder
  have hrecordTerminal : Gamma.terminal? record.record = some b := by
    rcases record.represents with hfinite | hproxy
    · obtain ⟨p, hrecord, hsource⟩ := hfinite
      have hfinish : p.finish = b := by
        have hbfinish : b = p.finish := by
          change (PopularAuxiliary.Input.LambdaVertex.old b : (J).LV) =
            .old p.finish at hsource
          injection hsource
        exact hbfinish.symm
      rw [hrecord]
      change some p.finish = some b
      simp only [hfinish]
    · obtain ⟨i, _hrecord, hsource⟩ := hproxy
      change (PopularAuxiliary.Input.LambdaVertex.old b : (J).LV) =
        .proxy i at hsource
      cases hsource
  have hbRecord : b ∈ record.record.support :=
    Gamma.terminal_mem_support hrecordTerminal
  have hownerEq : D.owner = record.record :=
    D.owner_eq_of_common_limit_vertex hb hbOwner record.record
      hrecordLimit hbRecord
  refine ⟨source, record, rfl, hownerEq, ?_, ?_⟩
  · simpa only [hownerEq] using hrecordTerminal
  · simpa only [hownerEq] using record.limit_inessential

/-- Classify the strict-after-contact branch of
`sourceFirstBoundary_rooted_or_strictOwnerTail` by the actual final deferred
boundary owner.  No terminal or owner identity is forgotten. -/
theorem strictSourceFirstOwnerOutcome
    (hGamma : Gamma.IsNormalized)
    {r : Request (popularAuxiliaryInput L hL.legal) S.cut}
    {X : ReservedStrongSelectedStartingLastContact
      (L := L) (hL := hL) (S := S) r}
    (D : SourceSaturation X) {b : V}
    (hb : b ∈ reservedStrongSelectedSourceFirstBB
      (L := L) (hL := hL) (S := S))
    (hbOwner : b ∈ D.owner.support)
    (hstrict : GroundingCut.Before D.owner D.contact.vertex b) :
    StrictSourceFirstOwnerOutcome D b := by
  let data := reservedStrongSelectedPruningData
    (L := L) (hL := hL) (S := S)
  have hbRelevant : b ∈ data.relevantBB :=
    reservedStrongSelectedSourceFirstBB_subset_relevantBB hb
  rcases hbRelevant with hbCV | hbBL
  · rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit hbCV with
      hbFinite | ⟨request, hapex, hexit⟩
    · obtain ⟨source, record, hsource, howner, hterminal, hinessential⟩ :=
        D.finiteSource_owner_record hb hbOwner hbFinite
      obtain ⟨p, hpOwner, hpLength⟩ :=
        D.finite_owner_and_prefix_lt_of_terminal hstrict hterminal
      exact .finiteRecord source hsource record howner hterminal hinessential
        p hpOwner hpLength
    · exact .oldRequest request hapex hexit
  · obtain ⟨P, hP, hblock⟩ := hbBL
    have hblockSupport : b ∈ P.path.support := by
      rw [← hblock]
      exact GroundingCut.blockingPoint_mem_support J S.cut P hP.1.2
    have hbParent : b ∈ P.parent.support := P.support_subset hblockSupport
    have hparentLimit : P.parent ∈ L.limitWarp := by
      simpa only [popularAuxiliaryInput, limitWarp] using P.parent_mem
    have hownerEq : D.owner = P.parent :=
      D.owner_eq_of_common_limit_vertex hb hbOwner P.parent
        hparentLimit hbParent
    by_cases hescape : P.MeetsEscape J S.cut
    · rcases reservedStrongSelected_sourceFirst_escapeBlocker_source_or_virtual
        hb P hP hblock hescape with hbSource | hvirtual
      · exact False.elim
          (D.strict_boundary_not_source hGamma hbOwner hstrict hbSource)
      · exact .virtualEscape P hP hownerEq hblock hescape
          hvirtual.some
    · rcases hP.2 with _hescape | ⟨t, hterminal, htCut⟩
      · exact False.elim (hescape _hescape)
      · have hblockTerminal :
          GroundingCut.blockingPoint J S.cut P = t :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            J S.cut P hescape hterminal
        have htb : t = b := hblockTerminal.symm.trans hblock
        rw [htb] at hterminal htCut
        have hbCut : b ∈ (J).terminalCut := htCut
        obtain ⟨Y, hYEssential, hYTerminal⟩ := htCut
        have hYLimit : Y ∈ L.limitWarp := by
          simpa only [popularAuxiliaryInput,
            PopularAuxiliary.Input.essentialLadder, limitWarp] using
              hYEssential.1
        have hbY : b ∈ Y.support :=
          Gamma.terminal_mem_support hYTerminal
        have hownerY : D.owner = Y :=
          D.owner_eq_of_common_limit_vertex hb hbOwner Y hYLimit hbY
        have hownerEssential : D.owner ∈ (J).essentialLadder := by
          rw [hownerY]
          exact hYEssential
        have hownerTerminal : Gamma.terminal? D.owner = some b := by
          rw [hownerY]
          exact hYTerminal
        obtain ⟨p, hpOwner, hpLength⟩ :=
          D.finite_owner_and_prefix_lt_of_terminal hstrict hownerTerminal
        exact .essentialTerminalFragment P hP hownerEq hblock
          hescape hterminal hbCut hownerEssential hownerTerminal
            p hpOwner hpLength

end ReservedStrongSelectedStartingLastContact.SourceSaturation

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.strictSourceFirstOwnerOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.restoredWarp_roots_owner_boundaries
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.ReservedStrongSelectedStartingLastContact.SourceSaturation.LastSourceFirstPrefix.canonicalReservedRecord_mem_restoredWarp

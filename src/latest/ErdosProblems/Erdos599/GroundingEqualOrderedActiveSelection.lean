/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalStrictCollision

/-!
# Ordered collision-carrier selection for the equal branch

Decoded-carrier disjointness prevents two inserted routes from sharing a
vertex, but it does not protect an untouched prefix of a grounded ladder
parent.  The ordered active closure needs the stronger asymmetric invariant:
every later selected auxiliary path avoids the complete collision carrier of
every earlier selected path.  Since one collision carrier is countable, the
usual Fodor argument still retains stationarily many indices.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingEqualOrderedActiveSelection

open DirectedPath Stationary
open GroundingEqualActiveSelection
open GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Greedy activity using the full earlier collision carrier. -/
noncomputable def IsOrderedActiveWarpPath
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : WarpPath P → Prop :=
  WellFounded.fix
    (InvImage.wf (warpPathIndex U P) wellFounded_lt)
    (fun p previous ↦
      ∀ q (hq : warpPathIndex U P q < warpPathIndex U P p),
        previous q hq → Disjoint p.1.support (collisionCarrier L q.1))

theorem isOrderedActiveWarpPath_iff
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P) :
    IsOrderedActiveWarpPath L U P p ↔
      ∀ q (_hq : warpPathIndex U P q < warpPathIndex U P p),
        IsOrderedActiveWarpPath L U P q →
          Disjoint p.1.support (collisionCarrier L q.1) := by
  unfold IsOrderedActiveWarpPath
  rw [WellFounded.fix_eq
    (InvImage.wf (warpPathIndex U P) wellFounded_lt)
    (fun p previous ↦
      ∀ q (hq : warpPathIndex U P q < warpPathIndex U P p),
        previous q hq → Disjoint p.1.support (collisionCarrier L q.1)) p]

theorem exists_orderedActive_earlier_collision_of_not_active
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P)
    (hp : ¬ IsOrderedActiveWarpPath L U P p) :
    ∃ q : WarpPath P,
      warpPathIndex U P q < warpPathIndex U P p ∧
      IsOrderedActiveWarpPath L U P q ∧
      (p.1.support ∩ collisionCarrier L q.1).Nonempty := by
  rw [isOrderedActiveWarpPath_iff] at hp
  push Not at hp
  obtain ⟨q, hqp, hactive, hnotdisjoint⟩ := hp
  rw [Set.not_disjoint_iff] at hnotdisjoint
  exact ⟨q, hqp, hactive, hnotdisjoint⟩

def orderedActiveWarpPaths
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : Set (FinitePath L.lambda.graph) :=
  {p | ∃ hp : p ∈ P.paths, IsOrderedActiveWarpPath L U P ⟨p, hp⟩}

theorem orderedActiveWarpPaths_starts_in_source
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) :
    ∀ {p}, p ∈ orderedActiveWarpPaths L U P →
      p.start ∈ L.lambda.source := by
  rintro p ⟨hp, _⟩
  exact P.starts_in_source hp

def orderedActiveWarpIndices
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : Set (Below kappa) :=
  Popular.initialIndicesOf U (orderedActiveWarpPaths L U P)
    (orderedActiveWarpPaths_starts_in_source L U P)

theorem warpPathIndex_mem_orderedActiveWarpIndices
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P)
    (hp : IsOrderedActiveWarpPath L U P p) :
    warpPathIndex U P p ∈ orderedActiveWarpIndices L U P := by
  let hpA : p.1 ∈ orderedActiveWarpPaths L U P := ⟨p.2, hp⟩
  refine ⟨p.1, hpA, ?_⟩
  apply congrArg U.f
  exact Subtype.ext rfl

/-- The full-carrier ordered selector remains stationary. -/
theorem orderedActiveWarpIndices_isStationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source)) :
    IsStationaryBelow kappa (orderedActiveWarpIndices L U P) := by
  classical
  let allIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U P.paths P.starts_in_source
  let selectedIndices : Set (Below kappa) :=
    orderedActiveWarpIndices L U P
  let rejectedIndices : Set (Below kappa) := allIndices \ selectedIndices
  by_contra hselected
  have hrejected : IsStationaryBelow kappa rejectedIndices :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable hP hselected
  let chosenPath : (a : Below kappa) → a ∈ allIndices →
      FinitePath L.lambda.graph := fun _a ha ↦ Classical.choose ha
  have chosenPath_mem (a : Below kappa) (ha : a ∈ allIndices) :
      chosenPath a ha ∈ P.paths :=
    Classical.choose (Classical.choose_spec ha)
  have chosenPath_index (a : Below kappa) (ha : a ∈ allIndices) :
      U.f ⟨(chosenPath a ha).start,
        P.starts_in_source (chosenPath_mem a ha)⟩ = a :=
    Classical.choose_spec (Classical.choose_spec ha)
  let chosenWarpPath (a : Below kappa) (ha : a ∈ allIndices) :
      WarpPath P := ⟨chosenPath a ha, chosenPath_mem a ha⟩
  have chosenWarpPath_inactive (a : Below kappa)
      (ha : a ∈ rejectedIndices) :
      ¬ IsOrderedActiveWarpPath L U P (chosenWarpPath a ha.1) := by
    intro hactive
    apply ha.2
    have hmem := warpPathIndex_mem_orderedActiveWarpIndices
      L U P (chosenWarpPath a ha.1) hactive
    have hindex : warpPathIndex U P (chosenWarpPath a ha.1) = a :=
      chosenPath_index a ha.1
    exact hindex ▸ hmem
  let ownerPath (a : Below kappa) (ha : a ∈ rejectedIndices) :
      WarpPath P :=
    Classical.choose (exists_orderedActive_earlier_collision_of_not_active
      L U P (chosenWarpPath a ha.1) (chosenWarpPath_inactive a ha))
  have ownerPath_earlier (a : Below kappa) (ha : a ∈ rejectedIndices) :
      warpPathIndex U P (ownerPath a ha) <
        warpPathIndex U P (chosenWarpPath a ha.1) :=
    (Classical.choose_spec
      (exists_orderedActive_earlier_collision_of_not_active
        L U P (chosenWarpPath a ha.1)
          (chosenWarpPath_inactive a ha))).1
  have ownerPath_collision (a : Below kappa)
      (ha : a ∈ rejectedIndices) :
      ((chosenWarpPath a ha.1).1.support ∩
        collisionCarrier L (ownerPath a ha).1).Nonempty :=
    (Classical.choose_spec
      (exists_orderedActive_earlier_collision_of_not_active
        L U P (chosenWarpPath a ha.1)
          (chosenWarpPath_inactive a ha))).2.2
  let ownerIndex : Below kappa → Below kappa := fun a ↦
    if ha : a ∈ rejectedIndices then
      warpPathIndex U P (ownerPath a ha) else a
  have hregressive : IsRegressiveOn rejectedIndices ownerIndex := by
    intro a ha
    rw [show ownerIndex a = warpPathIndex U P (ownerPath a ha) by
      simp [ownerIndex, ha]]
    exact lt_of_lt_of_eq (ownerPath_earlier a ha)
      (chosenPath_index a ha.1)
  obtain ⟨i, hi⟩ := pressingDown U.uncountable U.regular
    hrejected hregressive
  obtain ⟨a, haRejected, hai⟩ := hi.nonempty
  let q : WarpPath P := ownerPath a haRejected
  have hqindex : warpPathIndex U P q = i := by
    have howner : ownerIndex a =
        warpPathIndex U P (ownerPath a haRejected) := by
      simp [ownerIndex, haRejected]
    exact howner.symm.trans hai
  have hmeetingStationary : IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        {p | p ∈ P.paths ∧
          (p.support ∩ collisionCarrier L q.1).Nonempty}
        (fun {_p} hp ↦ P.starts_in_source hp.1)) := by
    apply hi.mono
    rintro b ⟨hbRejected, hbi⟩
    let r : WarpPath P := ownerPath b hbRejected
    have hrindex : warpPathIndex U P r = i := by
      have howner : ownerIndex b =
          warpPathIndex U P (ownerPath b hbRejected) := by
        simp [ownerIndex, hbRejected]
      exact howner.symm.trans hbi
    have hrq : r = q :=
      warpPath_eq_of_index_eq U hU P (hrindex.trans hqindex.symm)
    let p : WarpPath P := chosenWarpPath b hbRejected.1
    have hpmeet :
        (p.1.support ∩ collisionCarrier L q.1).Nonempty := by
      simpa [p, r, hrq] using ownerPath_collision b hbRejected
    let hpMeet : p.1 ∈ {p | p ∈ P.paths ∧
        (p.support ∩ collisionCarrier L q.1).Nonempty} :=
      ⟨p.2, hpmeet⟩
    refine ⟨p.1, hpMeet, ?_⟩
    have hs :
        (⟨p.1.start, P.starts_in_source hpMeet.1⟩ : L.lambda.source) =
          ⟨p.1.start, P.starts_in_source p.2⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans (chosenPath_index b hbRejected.1)
  exact (P.initialIndices_meeting_nonstationary U
    (collisionCarrier_countable L hfaith q.1)) hmeetingStationary

def orderedActiveSubwarp
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : Popular.XSWarp L.lambda S where
  paths := orderedActiveWarpPaths L U P
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact P.disjoint hp hq hpq
  starts_in_source := orderedActiveWarpPaths_starts_in_source L U P
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact P.ends_in_target hp

theorem orderedActiveSubwarp_paths_subset
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) :
    (orderedActiveSubwarp L U P).paths ⊆ P.paths := by
  rintro p ⟨hp, _⟩
  exact hp

theorem orderedActiveSubwarp_orderedAvoidance
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S)
    {p q : FinitePath L.lambda.graph}
    (hp : p ∈ (orderedActiveSubwarp L U P).paths)
    (hq : q ∈ (orderedActiveSubwarp L U P).paths)
    (hqp : warpPathIndex U P ⟨q, hq.1⟩ <
      warpPathIndex U P ⟨p, hp.1⟩) :
    Disjoint p.support (collisionCarrier L q) :=
  (isOrderedActiveWarpPath_iff L U P ⟨p, hp.1⟩).1 hp.2
    ⟨q, hq.1⟩ hqp hq.2

theorem decodedCarriers_disjoint_of_support_avoids_collisionCarrier
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (p q : FinitePath L.lambda.graph)
    (hpstart : p.start ∈ L.lambda.source)
    (hqstart : q.start ∈ L.lambda.source)
    (havoid : Disjoint p.support (collisionCarrier L q)) :
    Disjoint (L.decodedVertexCarrier p) (L.decodedVertexCarrier q) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  obtain ⟨a, hap, haCarrier⟩ :=
    support_meets_collisionCarrier_of_decodedCarrier_overlap
      L hfaith p q hpstart hqstart ⟨x, hxp, hxq⟩
  exact Set.disjoint_left.1 havoid hap haCarrier

theorem orderedActiveSubwarp_decodedCarriers_pairwiseDisjoint
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S) :
    (orderedActiveSubwarp L U P).paths.PairwiseDisjoint
      L.decodedVertexCarrier := by
  rintro p hp q hq hpq
  have hindex_ne :
      warpPathIndex U P ⟨p, hp.1⟩ ≠ warpPathIndex U P ⟨q, hq.1⟩ := by
    intro heq
    have hpq' : (⟨p, hp.1⟩ : WarpPath P) = ⟨q, hq.1⟩ :=
      warpPath_eq_of_index_eq U hU P heq
    exact hpq (congrArg Subtype.val hpq')
  rcases lt_or_gt_of_ne hindex_ne with hpqlt | hqplt
  · exact (decodedCarriers_disjoint_of_support_avoids_collisionCarrier
      L hfaith q p (P.starts_in_source hq.1)
        (P.starts_in_source hp.1)
        (orderedActiveSubwarp_orderedAvoidance L U P hq hp hpqlt)).symm
  · exact decodedCarriers_disjoint_of_support_avoids_collisionCarrier
      L hfaith p q (P.starts_in_source hp.1)
        (P.starts_in_source hq.1)
        (orderedActiveSubwarp_orderedAvoidance L U P hp hq hqplt)

theorem orderedActiveSubwarp_initialIndices_isStationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source)) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf U (orderedActiveSubwarp L U P).paths
        (orderedActiveSubwarp L U P).starts_in_source) := by
  have hactive := orderedActiveWarpIndices_isStationary
    L hfaith U hU P hP
  apply hactive.mono
  rintro a ⟨p, hp, hpa⟩
  refine ⟨p, hp, ?_⟩
  have hs :
      (⟨p.start, (orderedActiveSubwarp L U P).starts_in_source hp⟩ :
          L.lambda.source) =
        ⟨p.start, orderedActiveWarpPaths_starts_in_source L U P hp⟩ :=
    Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

end GroundingEqualOrderedActiveSelection

namespace DWeb

open _root_.Erdos599.DirectedPath
open Stationary

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualOrderedActiveSelection

variable {kappa : Cardinal.{u}}

/-- Reserved diagonal data with the stronger ordinally ordered avoidance
invariant needed to ground earlier parent prefixes. -/
structure OrderedReservedStationaryDiagonalEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    extends L.ReservedStationaryDiagonalEqualSelection hL P where
  base_orderedAvoidance : ∀ {p q}
      (hp : p ∈ base.paths) (hq : q ∈ base.paths),
    (L.popularAuxiliaryIndexed hL).f
        ⟨q.start, base.starts_in_source hq⟩ <
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start, base.starts_in_source hp⟩ →
    Disjoint p.support
      (collisionCarrier (L.popularAuxiliaryInput hL.legal) q)

namespace OrderedReservedStationaryDiagonalEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {P : Popular.XSWarp
    (L.popularAuxiliaryInput hL.legal).lambda
    (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- A later selected route avoids every ladder component exposed by an
earlier selected route. -/
theorem later_decodedCarrier_disjoint_earlier_exposedParent
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    {p q : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ S.base.paths) (hq : q ∈ S.base.paths)
    (hqp : (L.popularAuxiliaryIndexed hL).f
        ⟨q.start, S.base.starts_in_source hq⟩ <
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start, S.base.starts_in_source hp⟩)
    {Y : Gamma.DPath}
    (hY : Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
      (L.popularAuxiliaryInput hL.legal) q) :
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier p)
      Y.support := by
  apply decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (L.popularAuxiliaryInput hL.legal)
    (L.popularAuxiliary_proxyPathsFaithful hL) p q
    (S.base.starts_in_source hp) hY
  exact S.base_orderedAvoidance hp hq hqp

/-- The ordered avoidance invariant descends to the final
strict-collision-free route family. -/
theorem routes_orderedAvoidance
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    {p q : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ S.routes.paths) (hq : q ∈ S.routes.paths)
    (hqp : (L.popularAuxiliaryIndexed hL).f
        ⟨q.start, S.routes.starts_in_source hq⟩ <
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start, S.routes.starts_in_source hp⟩) :
    Disjoint p.support
      (collisionCarrier (L.popularAuxiliaryInput hL.legal) q) := by
  have hpBase : p ∈ S.base.paths := S.routes_subset_base hp
  have hqBase : q ∈ S.base.paths := S.routes_subset_base hq
  apply S.base_orderedAvoidance hpBase hqBase
  simpa only [] using hqp

/-- On the final stationary family, a later decoded route is disjoint from
every limiting-ladder component exposed by an earlier route. -/
theorem routes_later_decodedCarrier_disjoint_earlier_exposedParent
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    {p q : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ S.routes.paths) (hq : q ∈ S.routes.paths)
    (hqp : (L.popularAuxiliaryIndexed hL).f
        ⟨q.start, S.routes.starts_in_source hq⟩ <
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start, S.routes.starts_in_source hp⟩)
    {Y : Gamma.DPath}
    (hY : Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
      (L.popularAuxiliaryInput hL.legal) q) :
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier p)
      Y.support := by
  apply decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (L.popularAuxiliaryInput hL.legal)
    (L.popularAuxiliary_proxyPathsFaithful hL) p q
    (S.routes.starts_in_source hp) hY
  exact S.routes_orderedAvoidance hp hq hqp

/-- Every final route has the canonical finite source prefix in the ambient
equal subwarp used by the strict-collision construction. -/
theorem route_has_rootPrefix
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    Nonempty (L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) :=
  L.exists_canonicalErasedRouteRootPrefix hL
    ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
    ⟨q.1, S.routes_subset_equalBase q.2⟩

/-- Later final routes cannot delete an earlier route's canonical grounded
parent prefix: their whole decoded carriers avoid that parent. -/
theorem laterRoute_decodedCarrier_disjoint_rootPrefix_parent
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (p q : WarpPath S.routes)
    (hqp : (L.popularAuxiliaryIndexed hL).f
        ⟨q.1.start, S.routes.starts_in_source q.2⟩ <
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.1.start, S.routes.starts_in_source p.2⟩)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) :
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier p.1)
      R.parent.support := by
  exact S.routes_later_decodedCarrier_disjoint_earlier_exposedParent
    p.2 q.2 hqp R.parent_exposed

/-- The first selected route, in source-index order, whose decoded carrier
meets one fixed grounded root parent. -/
structure FirstRootParentCollision
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) where
  owner : WarpPath S.routes
  owner_contact :
    ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier owner.1 ∩
      R.parent.support).Nonempty
  owner_index_le_route :
    warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes owner ≤
      warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q
  earlier_disjoint : ∀ r : WarpPath S.routes,
    warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes owner →
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier r.1)
      R.parent.support

/-- The route itself meets its root parent at the canonical initial vertex,
so the first collision owner exists by well-foundedness of source indices. -/
theorem exists_firstRootParentCollision
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) :
    Nonempty (FirstRootParentCollision S q R) := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let Q := U.equalSubwarp S.base
  let qQ : WarpPath Q := ⟨q.1, S.routes_subset_equalBase q.2⟩
  let C : Set (WarpPath S.routes) :=
    {r | (J.decodedVertexCarrier r.1 ∩ R.parent.support).Nonempty}
  have hqC : q ∈ C := by
    let x := (canonicalErasedRoute J Q qQ).initial
    refine ⟨x, ?_, ?_⟩
    · exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        J Q qQ (canonicalErasedRoute J Q qQ).initial_mem_vertexSet
    · have hfinish : R.path.finish = x := by
        simpa only [x, J, Q, qQ] using R.finish_eq
      rw [← hfinish]
      exact R.support_subset R.path.finish_mem_support
  let rank : WarpPath S.routes → Stationary.Below kappa :=
    warpPathIndex U S.routes
  obtain ⟨owner, hownerC, hminimal⟩ :=
    (InvImage.wf rank wellFounded_lt).has_min C ⟨q, hqC⟩
  refine ⟨{
    owner := owner
    owner_contact := hownerC
    owner_index_le_route := ?_
    earlier_disjoint := ?_ }⟩
  · exact le_of_not_gt (hminimal q hqC)
  · intro r hr
    rw [Set.disjoint_left]
    intro x hxr hxR
    exact hminimal r ⟨x, hxr, hxR⟩ hr

/-- The canonical route family cut off immediately before an ordinal source
index. -/
def routesBeforeIndex
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target where
  paths := {p | ∃ hp : p ∈ S.routes.paths,
    warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes ⟨p, hp⟩ < a}
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact S.routes.disjoint hp hq hpq
  starts_in_source := by
    rintro p ⟨hp, _⟩
    exact S.routes.starts_in_source hp
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact S.routes.ends_in_target hp

namespace FirstRootParentCollision

/-- Before its first collision owner is inserted, the whole grounded root
prefix survives the canonical repaired relation. -/
theorem rootPrefix_edgeSet_subset_repaired_beforeOwner
    {S : L.OrderedReservedStationaryDiagonalEqualSelection hL P}
    {q : WarpPath S.routes}
    {R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩}
    (C : FirstRootParentCollision S q R) :
    R.path.edgeSet ⊆ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex S
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes C.owner)) := by
  apply R.path_edgeSet_subset_repaired_of_decodedCarriers_disjoint_parent
  intro r
  obtain ⟨hr, hrIndex⟩ := r.2
  exact C.earlier_disjoint ⟨r.1, hr⟩ hrIndex

end FirstRootParentCollision

end OrderedReservedStationaryDiagonalEqualSelection

/-- Target-pure stationary equality admits a reserved diagonal selection
with full earlier-carrier avoidance. -/
theorem exists_orderedReservedStationaryDiagonalEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Nonempty (L.OrderedReservedStationaryDiagonalEqualSelection hL P) := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  obtain ⟨q, hq, Q, hQsubset, hQpure, hQstationary,
      hQdisjoint, hQavoid⟩ :=
    L.exists_reserved_targetPure_stationary_equalSubwarp
      hL P hpure hstat
  let R := U.equalSubwarp Q
  let B := orderedActiveSubwarp J U R
  have hBstationary : IsStationaryBelow kappa
      (Popular.initialIndicesOf U B.paths B.starts_in_source) :=
    orderedActiveSubwarp_initialIndices_isStationary J
      (L.popularAuxiliary_proxyPathsFaithful hL) U
      (L.popularAuxiliaryIndexed_sourceIndexed hL) R hQstationary
  have hBR : B.paths ⊆ R.paths :=
    orderedActiveSubwarp_paths_subset J U R
  have hBQ : B.paths ⊆ Q.paths :=
    hBR.trans (U.equalPaths_subset Q)
  have hBsubset : B.paths ⊆ (U.equalSubwarp P).paths :=
    hBQ.trans hQsubset
  have hBequalStationary : IsStationaryBelow kappa
      (Popular.initialIndicesOf U (U.equalSubwarp B).paths
        (U.equalSubwarp B).starts_in_source) :=
    GroundingEqualActiveSelection.equalSubwarp_initialIndices_isStationary_of_subset
      U Q B hBR hBstationary
  exact ⟨{
      base := B
      base_subset_equal := hBsubset
      base_targetPure := fun p hp ↦ hQpure p (hBQ hp)
      base_decodedDisjoint :=
        orderedActiveSubwarp_decodedCarriers_pairwiseDisjoint J
          (L.popularAuxiliary_proxyPathsFaithful hL) U
          (L.popularAuxiliaryIndexed_sourceIndexed hL) R
      routes_stationary :=
        L.strictCollisionFreeSubwarp_initialIndices_isStationary hL
          (U.equalSubwarp B) hBequalStationary
      reserved := q
      reserved_mem_equal := hq
      base_avoids_reserved := fun p hp ↦ hQavoid p (hBQ hp)
      base_orderedAvoidance := by
        intro p q' hp hq' hqp
        have hpR : p ∈ B.paths := hp
        have hqR : q' ∈ B.paths := hq'
        apply orderedActiveSubwarp_orderedAvoidance J U R hpR hqR
        simpa only [warpPathIndex] using hqp }⟩

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.GroundingEqualOrderedActiveSelection.orderedActiveWarpIndices_isStationary
#print axioms Erdos599.GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_orderedAvoidance
#print axioms Erdos599.GroundingEqualOrderedActiveSelection.orderedActiveSubwarp_decodedCarriers_pairwiseDisjoint
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.routes_orderedAvoidance
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.laterRoute_decodedCarrier_disjoint_rootPrefix_parent
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.exists_firstRootParentCollision
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.FirstRootParentCollision.rootPrefix_edgeSet_subset_repaired_beforeOwner
#print axioms Erdos599.DWeb.KappaLadder.exists_orderedReservedStationaryDiagonalEqualSelection

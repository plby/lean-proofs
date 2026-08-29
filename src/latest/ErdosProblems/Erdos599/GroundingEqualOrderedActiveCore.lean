/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualActiveSelection

/-!
# Ordered collision-carrier selection core

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

end Erdos599


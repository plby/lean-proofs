/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentCarrier
import ErdosProblems.Erdos599.JoinedFamilyOwnerThinning

/-!
# First-hit stationary thinning for Assertion 8.20

For every initial index in the hanging-fragment subfan, choose a path, cut it
at its first visit to the union of all eligible fragment carriers, and choose
a carrier piece containing that first-hit vertex.  The owner is the parent
ladder component of that piece.

All paths with one owner meet that owner's countable parent carrier, which
avoids the request apex.  The generic owner-thinning lemma therefore gives a
stationary subfamily with distinct parent components.  Using first-hit owners,
rather than arbitrary collided fragments, is essential for the later proof
that the predecessor splices are pairwise disjoint.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingFragmentThinning

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type u) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The exact exceptional subfan occurring in the concrete fragment
collision predicate. -/
def collisionFan {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) :
    Popular.JoinedFamily L.lambda {requestAuxVertex r} :=
  PopularSwitching.restrictPaths (requestFan S r)
    {p | GroundingConcreteControls.hangingFragmentCollision
      L S.cut r p}

/-- Initial ordinal indices of the exact fragment-collision subfan. -/
def collisionIndices {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) :
    Set (Below kappa) :=
  Popular.initialIndicesOf U (collisionFan S r).paths
    (collisionFan S r).starts_in_source

/-- Canonical first-hit data attached to an exceptional initial index. -/
structure FirstHitOwner {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (a : Below kappa) where
  path : FinitePath L.lambda.graph
  path_mem : path ∈ (collisionFan S r).paths
  index_eq : U.f ⟨path.start,
    (collisionFan S r).starts_in_source path_mem⟩ = a
  piece : GroundingFragmentCarrier.Piece L S r
  firstHit_finish_mem_piece :
    (path.firstHit (GroundingFragmentCarrier.carrier S r)
      (GroundingFragmentCarrier.collision_meets_carrier
        S r path_mem.2)).finish ∈ piece.carrier

/-- The selected first-hit prefix stored by an owner. -/
noncomputable def FirstHitOwner.prefix
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    {a : Below kappa} (d : FirstHitOwner S r a) :
    FinitePath L.lambda.graph :=
  d.path.firstHit (GroundingFragmentCarrier.carrier S r)
    (GroundingFragmentCarrier.collision_meets_carrier
      S r d.path_mem.2)

theorem FirstHitOwner.prefix_finish_mem_piece
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    {a : Below kappa} (d : FirstHitOwner S r a) :
    d.prefix.finish ∈ d.piece.carrier :=
  d.firstHit_finish_mem_piece

theorem FirstHitOwner.prefix_support_subset
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    {a : Below kappa} (d : FirstHitOwner S r a) :
    d.prefix.support ⊆ d.path.support :=
  d.path.firstHit_support_subset
    (GroundingFragmentCarrier.carrier S r)
    (GroundingFragmentCarrier.collision_meets_carrier
      S r d.path_mem.2)

/-- Every exceptional initial index admits first-hit owner data. -/
theorem firstHitOwner_nonempty
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    {a : Below kappa} (ha : a ∈ collisionIndices S r) :
    Nonempty (FirstHitOwner S r a) := by
  obtain ⟨p, hp, hpa⟩ := ha
  let hm := GroundingFragmentCarrier.collision_meets_carrier
    S r hp.2
  have hfinish :
      (p.firstHit (GroundingFragmentCarrier.carrier S r) hm).finish ∈
        GroundingFragmentCarrier.carrier S r :=
    p.firstHit_finish_mem (GroundingFragmentCarrier.carrier S r) hm
  obtain ⟨W, hW⟩ :=
    GroundingFragmentCarrier.exists_piece_of_mem_carrier hfinish
  exact ⟨{
    path := p
    path_mem := hp
    index_eq := hpa
    piece := W
    firstHit_finish_mem_piece := hW }⟩

/-- Choose first-hit data exactly where it exists. -/
noncomputable def firstHitOwner?
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (a : Below kappa) : Option (FirstHitOwner S r a) := by
  classical
  exact if h : Nonempty (FirstHitOwner S r a) then
    some (Classical.choice h)
  else none

theorem firstHitOwner?_eq_some_of_mem
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    {a : Below kappa} (ha : a ∈ collisionIndices S r) :
    ∃ d : FirstHitOwner S r a, firstHitOwner? S r a = some d := by
  let hn := firstHitOwner_nonempty S r ha
  rw [firstHitOwner?, dif_pos hn]
  exact ⟨Classical.choice hn, rfl⟩

/-- The totalized parent-component owner.  It is `none` only away from the
indices for which first-hit data were selected. -/
noncomputable def firstHitParent?
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (a : Below kappa) : Option Gamma.DPath :=
  match firstHitOwner? S r a with
  | none => none
  | some d => some d.piece.fragment.parent

/-- The carrier associated to a totalized parent owner. -/
def ownerCarrier {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) :
    Option Gamma.DPath → Set (LV L)
  | none => ∅
  | some Y => GroundingFragmentCarrier.parentCarrier S r Y

theorem ownerCarrier_countable
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (Y : Option Gamma.DPath) : (ownerCarrier S r Y).Countable := by
  cases Y with
  | none => exact Set.countable_empty
  | some Y => exact GroundingFragmentCarrier.parentCarrier_countable S r Y

theorem ownerCarrier_disjoint_requestAuxVertex
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (Y : Option Gamma.DPath) :
    Disjoint (ownerCarrier S r Y) {requestAuxVertex r} := by
  cases Y with
  | none => exact Set.empty_disjoint _
  | some Y =>
      exact GroundingFragmentCarrier.parentCarrier_disjoint_requestAuxVertex
        S r Y

/-- On an exceptional index, its chosen first-hit endpoint belongs to the
countable carrier of its totalized parent owner. -/
theorem firstHitOwner_represented
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    {a : Below kappa} (ha : a ∈ collisionIndices S r) :
    ∃ d : FirstHitOwner S r a,
      d.path ∈ (collisionFan S r).paths ∧
      U.f ⟨d.path.start,
        (collisionFan S r).starts_in_source d.path_mem⟩ = a ∧
      ∃ z ∈ ownerCarrier S r (firstHitParent? S r a),
        z ∈ d.path.support := by
  obtain ⟨d, hd⟩ := firstHitOwner?_eq_some_of_mem S r ha
  refine ⟨d, d.path_mem, d.index_eq, d.prefix.finish, ?_, ?_⟩
  · simp only [ownerCarrier, firstHitParent?, hd]
    exact ⟨d.piece, rfl, d.prefix_finish_mem_piece⟩
  · exact d.prefix_support_subset d.prefix.finish_mem_support

/-- Source-faithful stationary thinning for Assertion 8.20: the retained
indices have pairwise distinct first-hit parent components. -/
theorem exists_stationary_firstHitParent_transversal
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (hstationary : IsStationaryBelow kappa (collisionIndices S r)) :
    ∃ B : Set (Below kappa),
      B ⊆ collisionIndices S r ∧ IsStationaryBelow kappa B ∧
        Set.InjOn (firstHitParent? S r) B := by
  apply Popular.exists_stationary_owner_transversal U
    (collisionFan S r) hstationary
    (firstHitParent? S r) (ownerCarrier S r)
    (ownerCarrier_countable S r)
    (ownerCarrier_disjoint_requestAuxVertex S r)
  intro a ha
  obtain ⟨d, _hdmem, hda, z, hzCarrier, hzPath⟩ :=
    firstHitOwner_represented S r ha
  exact ⟨d.path, d.path_mem, hda, z, hzCarrier, hzPath⟩

end GroundingFragmentThinning
end Erdos599

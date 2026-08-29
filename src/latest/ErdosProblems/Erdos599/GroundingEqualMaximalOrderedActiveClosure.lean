/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualOrderedActiveSelection
import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply

/-!
# Ordered active closure of the maximal equal-route reservoir

The decoded-disjoint maximal reservoir supplies global coverage, while the
ordered active selector supplies the asymmetric preservation invariant
needed by the sequential switch.  Applying the selector to the maximal
reservoir has two useful features:

* it is still stationary because it contains the stationary equal seed;
* every rejected reservoir route collides directly with an active route of
  strictly smaller source index.

Thus rejected routes need no recursive inactive-owner chain.  They can be
used as routing metadata and charged immediately to a selected active
control.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualOrderedActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev MaximalWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  ReservedMaximalDecodedActiveSupply.toXSWarp M

/-- The ordered active part of a maximal decoded collision-avoiding
reservoir. -/
def maximalOrderedActiveSubwarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target :=
  orderedActiveSubwarp (EqualInput L hL)
    (L.popularAuxiliaryIndexed hL) (MaximalWarp M)

@[simp] theorem mem_maximalOrderedActiveSubwarp_paths
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (p : FinitePath (EqualInput L hL).lambda.graph) :
    p ∈ (maximalOrderedActiveSubwarp hL M).paths ↔
      ∃ hp : p ∈ (MaximalWarp M).paths,
        IsOrderedActiveWarpPath (EqualInput L hL)
          (L.popularAuxiliaryIndexed hL) (MaximalWarp M) ⟨p, hp⟩ := by
  rfl

/-- Initial indices are monotone under literal inclusion of auxiliary
warps.  This proof-local form also aligns the dependent source-membership
witnesses. -/
private theorem initialIndices_mono_of_paths_subset
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Set (EqualInput L hL).LV}
    (P Q : Popular.XSWarp (EqualInput L hL).lambda S)
    (hPQ : P.paths ⊆ Q.paths) :
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        P.paths P.starts_in_source ⊆
      Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        Q.paths Q.starts_in_source := by
  rintro a ⟨p, hp, hpa⟩
  let hpQ : p ∈ Q.paths := hPQ hp
  refine ⟨p, hpQ, ?_⟩
  have hs :
      (⟨p.start, Q.starts_in_source hpQ⟩ :
          (EqualInput L hL).lambda.source) =
        ⟨p.start, P.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg (L.popularAuxiliaryIndexed hL).f hs).trans hpa

/-- The maximal reservoir has stationary source indices because it contains
the stationary equal seed. -/
theorem maximalDecodedSupply_initialIndices_isStationary
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hQstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source))
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (hQM : Q.paths ⊆ M.paths) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        (MaximalWarp M).paths (MaximalWarp M).starts_in_source) := by
  apply hQstat.mono
  apply initialIndices_mono_of_paths_subset
  intro p hp
  exact hQM ((L.popularAuxiliaryIndexed hL).equalPaths_subset Q hp)

/-- The ordered active part of the maximal reservoir remains stationary. -/
theorem maximalOrderedActiveSubwarp_initialIndices_isStationary
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (Q : Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target)
    (hQstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source))
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (hQM : Q.paths ⊆ M.paths) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        (maximalOrderedActiveSubwarp hL M).paths
        (maximalOrderedActiveSubwarp hL M).starts_in_source) := by
  exact orderedActiveSubwarp_initialIndices_isStationary
    (EqualInput L hL) (L.popularAuxiliary_proxyPathsFaithful hL)
    (L.popularAuxiliaryIndexed hL)
    (L.popularAuxiliaryIndexed_sourceIndexed hL) (MaximalWarp M)
    (maximalDecodedSupply_initialIndices_isStationary Q hQstat M hQM)

/-- One reservoir route together with its direct active owner.  An active
route owns itself.  A rejected route is charged to an active route of
strictly smaller source index and records the literal collision carrier
contact. -/
structure MaximalOrderedActiveOwner
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (p : WarpPath (MaximalWarp M)) where
  owner : WarpPath (MaximalWarp M)
  owner_active : IsOrderedActiveWarpPath (EqualInput L hL)
    (L.popularAuxiliaryIndexed hL) (MaximalWarp M) owner
  self_or_earlierCollision : owner = p ∨
    warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M) owner <
        warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M) p ∧
      (p.1.support ∩ collisionCarrier (EqualInput L hL) owner.1).Nonempty

/-- Every maximal-reservoir route has a direct active owner. -/
theorem exists_maximalOrderedActiveOwner
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (p : WarpPath (MaximalWarp M)) :
    Nonempty (MaximalOrderedActiveOwner hL M p) := by
  by_cases hp : IsOrderedActiveWarpPath (EqualInput L hL)
      (L.popularAuxiliaryIndexed hL) (MaximalWarp M) p
  · exact ⟨⟨p, hp, Or.inl rfl⟩⟩
  · obtain ⟨r, hrp, hrActive, hcontact⟩ :=
      exists_orderedActive_earlier_collision_of_not_active
        (EqualInput L hL) (L.popularAuxiliaryIndexed hL)
        (MaximalWarp M) p hp
    exact ⟨⟨r, hrActive, Or.inr ⟨hrp, hcontact⟩⟩⟩

/-- Active reservoir routes retain the full later-avoids-earlier collision
carrier invariant. -/
theorem maximalOrderedActiveSubwarp_orderedAvoidance
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {p r : FinitePath (EqualInput L hL).lambda.graph}
    (hp : p ∈ (maximalOrderedActiveSubwarp hL M).paths)
    (hr : r ∈ (maximalOrderedActiveSubwarp hL M).paths)
    (hrp : warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M)
        ⟨r, hr.1⟩ <
      warpPathIndex (L.popularAuxiliaryIndexed hL) (MaximalWarp M)
        ⟨p, hp.1⟩) :
    Disjoint p.support (collisionCarrier (EqualInput L hL) r) :=
  orderedActiveSubwarp_orderedAvoidance
    (EqualInput L hL) (L.popularAuxiliaryIndexed hL)
    (MaximalWarp M) hp hr hrp

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.maximalDecodedSupply_initialIndices_isStationary
#print axioms Erdos599.DWeb.KappaLadder.maximalOrderedActiveSubwarp_initialIndices_isStationary
#print axioms Erdos599.DWeb.KappaLadder.exists_maximalOrderedActiveOwner
#print axioms Erdos599.DWeb.KappaLadder.maximalOrderedActiveSubwarp_orderedAvoidance

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualRouteRoot
import ErdosProblems.Erdos599.GroundingEqualOrderedActiveCore

/-!
# Ordered active closure of the grounded split maximal supply

The Zorn reservoir supplies coverage.  Reapplying the full collision-carrier
selector to that reservoir gives a stationary active family in which every
later route avoids every earlier decoded footprint.  Rejected reservoir
routes have a direct earlier active collision owner.
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

private abbrev SplitMaximalOrderedInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- Ordered active part of a maximal grounded split reservoir. -/
def splitMaximalOrderedActiveSubwarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitKappaHindrance)
    {q : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) q)) :
    Popular.XSWarp
      (SplitMaximalOrderedInput L hL).lambda
      (SplitMaximalOrderedInput L hL).lambda.target :=
  orderedActiveSubwarp (SplitMaximalOrderedInput L hL)
    (L.splitPopularAuxiliaryIndexed hL)
    (splitMaximalEqualWarp (hL := hL) M)

@[simp] theorem mem_splitMaximalOrderedActiveSubwarp_paths
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) q))
    (p : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph) :
    p ∈ (splitMaximalOrderedActiveSubwarp hL M).paths ↔
      ∃ hp : p ∈ (splitMaximalEqualWarp (hL := hL) M).paths,
        IsOrderedActiveWarpPath (SplitMaximalOrderedInput L hL)
          (L.splitPopularAuxiliaryIndexed hL)
          (splitMaximalEqualWarp (hL := hL) M) ⟨p, hp⟩ := by
  rfl

/-- Every active route still has a grounded source index. -/
theorem splitMaximalOrderedActiveSubwarp_routes_ground
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) q)) :
    ∀ p, ∀ hp : p ∈ (splitMaximalOrderedActiveSubwarp hL M).paths,
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start,
          (splitMaximalOrderedActiveSubwarp hL M).starts_in_source hp⟩ ∈
        L.phiGround := by
  intro p hp
  have hpM : p ∈ (splitMaximalEqualWarp (hL := hL) M).paths := hp.1
  have hground :=
    splitMaximalEqualWarp_routes_ground (hL := hL) M p hpM
  have hs :
      (⟨p.start,
          (splitMaximalOrderedActiveSubwarp hL M).starts_in_source hp⟩ :
        (SplitMaximalOrderedInput L hL).lambda.source) =
      ⟨p.start,
        (splitMaximalEqualWarp (hL := hL) M).starts_in_source hpM⟩ :=
    Subtype.ext rfl
  exact (congrArg (L.splitPopularAuxiliaryIndexed hL).f hs) ▸ hground

/-- The maximal reservoir is stationary because it contains the selected
stationary equal subwarp. -/
theorem splitMaximalSupply_initialIndices_isStationary
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {P : Popular.XSWarp
      (SplitMaximalOrderedInput L hL).lambda
      (SplitMaximalOrderedInput L hL).lambda.target}
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {S.reserved.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) S.reserved))
    (hSM : S.routes.paths ⊆ M.paths) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        (splitMaximalEqualWarp (hL := hL) M).paths
        (splitMaximalEqualWarp (hL := hL) M).starts_in_source) := by
  apply S.equal_indices_stationary.mono
  rintro a ⟨p, hpEqual, hpa⟩
  have hpS : p ∈ S.routes.paths :=
    (L.splitPopularAuxiliaryIndexed hL).equalPaths_subset S.routes hpEqual
  let hpM : p ∈ (splitMaximalEqualWarp (hL := hL) M).paths := hSM hpS
  refine ⟨p, hpM, ?_⟩
  have hs :
      (⟨p.start,
          (splitMaximalEqualWarp (hL := hL) M).starts_in_source hpM⟩ :
        (SplitMaximalOrderedInput L hL).lambda.source) =
      ⟨p.start,
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
          |>.starts_in_source hpEqual⟩ := Subtype.ext rfl
  exact (congrArg (L.splitPopularAuxiliaryIndexed hL).f hs).trans hpa

/-- The ordered active part of the maximal supply remains stationary. -/
theorem splitMaximalOrderedActiveSubwarp_initialIndices_isStationary
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {P : Popular.XSWarp
      (SplitMaximalOrderedInput L hL).lambda
      (SplitMaximalOrderedInput L hL).lambda.target}
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {S.reserved.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) S.reserved))
    (hSM : S.routes.paths ⊆ M.paths) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        (splitMaximalOrderedActiveSubwarp hL M).paths
        (splitMaximalOrderedActiveSubwarp hL M).starts_in_source) :=
  orderedActiveSubwarp_initialIndices_isStationary
    (SplitMaximalOrderedInput L hL)
    (L.splitPopularAuxiliary_proxyPathsFaithful hL)
    (L.splitPopularAuxiliaryIndexed hL)
    (L.splitPopularAuxiliaryIndexed_sourceIndexed hL)
    (splitMaximalEqualWarp (hL := hL) M)
    (splitMaximalSupply_initialIndices_isStationary S M hSM)

/-- Active maximal routes retain the full later-avoids-earlier invariant. -/
theorem splitMaximalOrderedActiveSubwarp_orderedAvoidance
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) q))
    {p r : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph}
    (hp : p ∈ (splitMaximalOrderedActiveSubwarp hL M).paths)
    (hr : r ∈ (splitMaximalOrderedActiveSubwarp hL M).paths)
    (hrp :
      (L.splitPopularAuxiliaryIndexed hL).f
          ⟨r.start,
            (splitMaximalOrderedActiveSubwarp hL M).starts_in_source hr⟩ <
        (L.splitPopularAuxiliaryIndexed hL).f
          ⟨p.start,
            (splitMaximalOrderedActiveSubwarp hL M).starts_in_source hp⟩) :
    Disjoint p.support
      (collisionCarrier (SplitMaximalOrderedInput L hL) r) := by
  apply orderedActiveSubwarp_orderedAvoidance
    (SplitMaximalOrderedInput L hL)
    (L.splitPopularAuxiliaryIndexed hL)
    (splitMaximalEqualWarp (hL := hL) M) hp hr
  simpa only [warpPathIndex] using hrp

/-- Every rejected reservoir route has a direct earlier active owner. -/
theorem splitMaximal_exists_activeOwner
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (SplitMaximalOrderedInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitMaximalOrderedInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (SplitMaximalOrderedInput L hL) q))
    (p : WarpPath (splitMaximalEqualWarp (hL := hL) M)) :
    (IsOrderedActiveWarpPath (SplitMaximalOrderedInput L hL)
      (L.splitPopularAuxiliaryIndexed hL)
      (splitMaximalEqualWarp (hL := hL) M) p) ∨
    ∃ r : WarpPath (splitMaximalEqualWarp (hL := hL) M),
      warpPathIndex (L.splitPopularAuxiliaryIndexed hL)
          (splitMaximalEqualWarp (hL := hL) M) r <
        warpPathIndex (L.splitPopularAuxiliaryIndexed hL)
          (splitMaximalEqualWarp (hL := hL) M) p ∧
      IsOrderedActiveWarpPath (SplitMaximalOrderedInput L hL)
        (L.splitPopularAuxiliaryIndexed hL)
        (splitMaximalEqualWarp (hL := hL) M) r ∧
      (p.1.support ∩
        collisionCarrier (SplitMaximalOrderedInput L hL) r.1).Nonempty := by
  by_cases hp : IsOrderedActiveWarpPath (SplitMaximalOrderedInput L hL)
      (L.splitPopularAuxiliaryIndexed hL)
      (splitMaximalEqualWarp (hL := hL) M) p
  · exact Or.inl hp
  · exact Or.inr
      (exists_orderedActive_earlier_collision_of_not_active
        (SplitMaximalOrderedInput L hL)
        (L.splitPopularAuxiliaryIndexed hL)
        (splitMaximalEqualWarp (hL := hL) M) p hp)

end DWeb.KappaLadder
end Erdos599

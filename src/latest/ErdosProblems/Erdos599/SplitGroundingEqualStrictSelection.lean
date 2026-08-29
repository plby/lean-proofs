/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualStrictCollision
import ErdosProblems.Erdos599.SplitGroundingEqualSelection

/-!
# Strict-collision-free split equal selection

The source-faithful reserved selection is first restricted to equal routes
and then pruned by the nonstationary strict hanging-owner set.  All carrier
avoidance and grounded-source properties survive this restriction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Stationary

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev SplitStrictSelectionInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (SplitStrictSelectionInput L hL).lambda
    (SplitStrictSelectionInput L hL).lambda.target}

/-- The stationary selected family after equal restriction and strict-owner
pruning. -/
def strictRoutes (S : L.SplitReservedStationaryEqualSelection hL P) :
    Popular.XSWarp
      (SplitStrictSelectionInput L hL).lambda
      (SplitStrictSelectionInput L hL).lambda.target :=
  L.splitStrictCollisionFreeSubwarp hL
    ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)

theorem strictRoutes_subset_equalRoutes
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    S.strictRoutes.paths ⊆
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes).paths :=
  L.splitStrictCollisionFreeSubwarp_paths_subset hL _

theorem strictRoutes_subset_routes
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    S.strictRoutes.paths ⊆ S.routes.paths :=
  S.strictRoutes_subset_equalRoutes.trans
    ((L.splitPopularAuxiliaryIndexed hL).equalPaths_subset S.routes)

theorem strictRoutes_targetPure
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    ∀ p ∈ S.strictRoutes.paths,
      (SplitStrictSelectionInput L hL).IsTargetPure p := by
  intro p hp
  exact S.routes_targetPure p (S.strictRoutes_subset_routes hp)

theorem strictRoutes_ground
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    ∀ p, ∀ hp : p ∈ S.strictRoutes.paths,
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.strictRoutes.starts_in_source hp⟩ ∈ L.phiGround := by
  intro p hp
  have hpRoutes := S.strictRoutes_subset_routes hp
  have hground := S.routes_ground p hpRoutes
  have hs :
      (⟨p.start, S.strictRoutes.starts_in_source hp⟩ :
        (SplitStrictSelectionInput L hL).lambda.source) =
      ⟨p.start, S.routes.starts_in_source hpRoutes⟩ :=
    Subtype.ext rfl
  exact (congrArg (L.splitPopularAuxiliaryIndexed hL).f hs) ▸ hground

theorem strictRoutes_initialIndices_isStationary
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        S.strictRoutes.paths S.strictRoutes.starts_in_source) :=
  L.splitStrictCollisionFreeSubwarp_initialIndices_isStationary hL
    ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
    S.equal_indices_stationary

theorem strictRoutes_decodedCarriers_pairwiseDisjoint
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    S.strictRoutes.paths.PairwiseDisjoint
      (SplitStrictSelectionInput L hL).decodedVertexCarrier := by
  intro p hp q hq hpq
  exact S.decodedCarriers_pairwiseDisjoint
    (S.strictRoutes_subset_routes hp)
    (S.strictRoutes_subset_routes hq) hpq

theorem strictRoutes_avoid_reserved
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    ∀ p ∈ S.strictRoutes.paths,
      Disjoint p.support
        (GroundingEqualActiveSelection.collisionCarrier
          (SplitStrictSelectionInput L hL) S.reserved) := by
  intro p hp
  exact S.routes_avoid_reserved p (S.strictRoutes_subset_routes hp)

theorem strictRoute_has_targetComponent
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (p : WarpPath S.strictRoutes) :
    Nonempty (L.SplitEqualTargetComponent hL S.routes p.1
      (S.strictRoutes_subset_equalRoutes p.2)) :=
  L.exists_splitEqualTargetComponent hL S.routes p.1
    (S.strictRoutes_subset_equalRoutes p.2)

theorem strictRoute_has_no_strict_collision
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (p : WarpPath S.strictRoutes) :
    IsEmpty (L.SplitStrictBackwardCollision hL
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
      ⟨p.1, S.strictRoutes_subset_equalRoutes p.2⟩) :=
  L.splitStrictCollisionFreeSubwarp_has_no_strict_collision hL _ p

end SplitReservedStationaryEqualSelection
end DWeb.KappaLadder
end Erdos599

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingAuxiliary
import ErdosProblems.Erdos599.GroundingSelectedNonstationarity

/-!
# Deferred grounded records left after control-aware selection
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

theorem selectedWarp_initialIndices_subset_phi
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) :
    Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).paths
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).starts_in_source
      ⊆ phi L := by
  let U := popularAuxiliaryIndexed L hL
  rintro a ⟨p, hp, hpa⟩
  have hsource := auxiliarySourceIndex_mem_phi L hL.legal
    ⟨p.start, (GroundingAssembly.selectedWarp U S K).starts_in_source hp⟩
  rw [auxiliarySourceIndex_eq_sourceIndex L hL.legal] at hsource
  exact hpa ▸ hsource

theorem stationary_diff_selectedWarp
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S)
    {A : Set (Ladder.Stage kappa)}
    (hA : Stationary.IsStationaryBelow kappa A) :
    Stationary.IsStationaryBelow kappa
      (A \ Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).paths
        (GroundingAssembly.selectedWarp
          (popularAuxiliaryIndexed L hL) S K).starts_in_source) :=
  PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    hL.legal.regular hL.legal.uncountable hA
    (GroundingAssembly.selectedWarp_initialIndices_nonstationary
      (popularAuxiliaryIndexed L hL) S K)

/-- The separator switch consumes only a nonstationary family of indices,
so stationarily many deferred grounded records remain. -/
theorem phiGround_diff_selectedWarp_isStationary
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL))
    (K : GroundingSelection.Controls S) :
    Stationary.IsStationaryBelow kappa
      (phiGround L \
        Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
          (GroundingAssembly.selectedWarp
            (popularAuxiliaryIndexed L hL) S K).paths
          (GroundingAssembly.selectedWarp
            (popularAuxiliaryIndexed L hL) S K).starts_in_source) :=
  stationary_diff_selectedWarp L hL S K
    (IsKappaHindrance.phiGround_isStationary L hL)

end Deferred
end KappaLadder
end DWeb
end Erdos599

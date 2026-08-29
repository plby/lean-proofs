/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSelectedNonstationarity
import ErdosProblems.Erdos599.SplitGroundingAuxiliary

/-!
# Stationary records left after the split grounding selection

The control-aware request recursion selects an auxiliary warp whose initial
index set is nonstationary.  This file specializes that conclusion to the
sound split auxiliary and performs the last stationary-ideal subtraction in
Assertion 8.22.  In particular, every stationary grounded branch retains
stationarily many record stages not used by the selected switching paths.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every initial index of the recursively selected split-auxiliary warp is
an actual obstruction stage of the ladder. -/
theorem splitSelectedWarp_initialIndices_subset_phi
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S) :
    Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
        (GroundingAssembly.selectedWarp
          (L.splitPopularAuxiliaryIndexed hL) S K).paths
        (GroundingAssembly.selectedWarp
          (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source
      ⊆ L.phi := by
  let U := L.splitPopularAuxiliaryIndexed hL
  rintro a ⟨p, hp, hpa⟩
  have hsource :
      L.splitAuxiliarySourceIndex hL.legal
        ⟨p.start,
          (GroundingAssembly.selectedWarp U S K).starts_in_source hp⟩
        ∈ L.phi :=
    L.splitAuxiliarySourceIndex_mem_phi hL.legal _
  rw [L.splitAuxiliarySourceIndex_eq_sourceIndex hL.legal] at hsource
  exact hpa ▸ hsource

/-- Removing the selected switching indices from any stationary family of
split-ladder stages leaves a stationary family. -/
theorem stationary_diff_splitSelectedWarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S)
    {A : Set (Ladder.Stage kappa)}
    (hA : Stationary.IsStationaryBelow kappa A) :
    Stationary.IsStationaryBelow kappa
      (A \
        Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          (GroundingAssembly.selectedWarp
            (L.splitPopularAuxiliaryIndexed hL) S K).paths
          (GroundingAssembly.selectedWarp
            (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source) := by
  exact PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    hL.legal.regular hL.legal.uncountable hA
      (GroundingAssembly.selectedWarp_initialIndices_nonstationary
        (L.splitPopularAuxiliaryIndexed hL) S K)

/-- Assertion 8.22's final stationary calculation for grounded obstruction
records.  These are precisely the candidate records which remain unreached
once the geometric switch/prune construction has been supplied. -/
theorem phiGround_diff_splitSelectedWarp_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (S : Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    Stationary.IsStationaryBelow kappa
      (L.phiGround \
        Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          (GroundingAssembly.selectedWarp
            (L.splitPopularAuxiliaryIndexed hL) S K).paths
          (GroundingAssembly.selectedWarp
            (L.splitPopularAuxiliaryIndexed hL) S K).starts_in_source) :=
  L.stationary_diff_splitSelectedWarp hL S K hground

end KappaLadder
end DWeb
end Erdos599

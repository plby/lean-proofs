/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSimultaneousDecode

/-!
# The unused grounded record in Assertion 8.22

The strengthened simultaneous selector still ends in the request copy of
the popular cut.  Consequently non-strong-popularity makes its set of
initial ordinal indices nonstationary.  Since the grounded obstruction
stages are stationary, at least one grounded record is not used as the
initial record of a selected request path.  This is the stationary
bookkeeping input to the final inessential-component argument.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open Stationary

universe u

namespace GroundingSimultaneousDecode

variable {V I : Type u} {Gamma : DWeb V}

/-- The length-zero paths at source vertices which already belong to a
specified cut.  These paths account for the source vertices omitted from
the request copy of the cut in Assertion 8.22. -/
def sourceCutWarp (Gamma : DWeb V) (C : Set V) : Popular.XSWarp Gamma C where
  paths := (fun x ↦ DirectedPath.FinitePath.trivial Gamma.graph x) ''
    (Gamma.source ∩ C)
  disjoint := by
    rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hpq
    change Disjoint
      (DirectedPath.FinitePath.trivial Gamma.graph x).support
      (DirectedPath.FinitePath.trivial Gamma.graph y).support
    rw [DirectedPath.FinitePath.support_trivial,
      DirectedPath.FinitePath.support_trivial]
    apply Set.disjoint_singleton.2
    intro hxy
    apply hpq
    subst y
    rfl
  starts_in_source := by
    rintro p ⟨x, hx, rfl⟩
    simpa using hx.1
  ends_in_target := by
    rintro p ⟨x, hx, rfl⟩
    simpa using hx.2

/-- The ordinal index of a source vertex already in the cut occurs among
the initial indices of the corresponding length-zero warp. -/
theorem source_mem_sourceCutWarp_initialIndices
    {kappa : Cardinal.{u}} (U : Popular.KappaIndexed Gamma kappa)
    (C : Set V) (x : Gamma.source) (hxC : x.1 ∈ C) :
    U.f x ∈ Popular.initialIndicesOf U (sourceCutWarp Gamma C).paths
      (sourceCutWarp Gamma C).starts_in_source := by
  let p := DirectedPath.FinitePath.trivial Gamma.graph x.1
  have hp : p ∈ (sourceCutWarp Gamma C).paths := by
    exact ⟨x.1, ⟨x.2, hxC⟩, rfl⟩
  refine ⟨p, hp, ?_⟩
  congr 1

/-- Source vertices which already lie in a non-strongly-popular cut also
use a nonstationary set of ordinal indices. -/
theorem sourceCutWarp_initialIndices_nonstationary
    {kappa : Cardinal.{u}} (U : Popular.KappaIndexed Gamma kappa)
    (S : Popular.PopularSeparator U) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U (sourceCutWarp Gamma S.cut).paths
        (sourceCutWarp Gamma S.cut).starts_in_source) := by
  exact PopularSwitching.initialIndices_nonstationary_of_warp_to_subset
    U (sourceCutWarp Gamma S.cut) Subset.rfl S.not_strongly_popular

/-- The strengthened selected request warp uses a nonstationary set of
source indices.  The proof depends only on the exact request-cut endpoint
of the selector, and hence is unaffected by the extra collision guards. -/
theorem strongSelectedWarp_initialIndices_nonstationary
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U (strongSelectedWarp U S K).paths
        (strongSelectedWarp U S K).starts_in_source) := by
  exact PopularSwitching.initialIndices_nonstationary_of_warp_to_subset
    U (strongSelectedWarp U S K)
      GroundingSelection.requestCut_subset_cut S.not_strongly_popular

end GroundingSimultaneousDecode

namespace DWeb.KappaLadder

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A grounded obstruction stage which is not the source index of any
strengthened selected request path.  This is the precise ``unreached
grounded record'' supplied by the final stationary-set subtraction in
Assertion 8.22. -/
theorem exists_groundedStage_not_mem_strongSelectedInitialIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    ∃ a : Ladder.Stage kappa,
      a ∈ L.phiGround ∧
        a ∉ Popular.initialIndicesOf
          (L.popularAuxiliaryIndexed hL)
          (GroundingSimultaneousDecode.strongSelectedWarp
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)).paths
          (GroundingSimultaneousDecode.strongSelectedWarp
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)).starts_in_source := by
  let N := Popular.initialIndicesOf
    (L.popularAuxiliaryIndexed hL)
    (GroundingSimultaneousDecode.strongSelectedWarp
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)).paths
    (GroundingSimultaneousDecode.strongSelectedWarp
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)).starts_in_source
  have hground : IsStationaryBelow kappa L.phiGround :=
    KappaLadder.IsKappaHindrance.phiGround_isStationary
      L hL hL.legal.regular hL.legal.uncountable
  have hN : ¬ IsStationaryBelow kappa N :=
    GroundingSimultaneousDecode.strongSelectedWarp_initialIndices_nonstationary
      (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S)
  have hdiff : IsStationaryBelow kappa (L.phiGround \ N) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hground hN
  obtain ⟨a, haGround, haN⟩ := hdiff.nonempty
  exact ⟨a, haGround, haN⟩

/-- The stationary choice used in Assertion 8.22 avoids both ways in which
a grounded source can fail to become a selected request: it is neither the
initial source of a selected request path nor a source vertex already lying
in the cut. -/
theorem exists_groundedStage_not_mem_selected_or_cutSourceInitialIndices
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    ∃ a : Ladder.Stage kappa,
      a ∈ L.phiGround ∧
      a ∉ Popular.initialIndicesOf
        (L.popularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)).paths
        (GroundingSimultaneousDecode.strongSelectedWarp
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S)).starts_in_source ∧
      a ∉ Popular.initialIndicesOf
        (L.popularAuxiliaryIndexed hL)
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.popularAuxiliaryInput hL.legal).lambda S.cut).paths
        (GroundingSimultaneousDecode.sourceCutWarp
          (L.popularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source := by
  let Nselected := Popular.initialIndicesOf
    (L.popularAuxiliaryIndexed hL)
    (GroundingSimultaneousDecode.strongSelectedWarp
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)).paths
    (GroundingSimultaneousDecode.strongSelectedWarp
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)).starts_in_source
  let NcutSource := Popular.initialIndicesOf
    (L.popularAuxiliaryIndexed hL)
    (GroundingSimultaneousDecode.sourceCutWarp
      (L.popularAuxiliaryInput hL.legal).lambda S.cut).paths
    (GroundingSimultaneousDecode.sourceCutWarp
      (L.popularAuxiliaryInput hL.legal).lambda S.cut).starts_in_source
  have hground : IsStationaryBelow kappa L.phiGround :=
    KappaLadder.IsKappaHindrance.phiGround_isStationary
      L hL hL.legal.regular hL.legal.uncountable
  have hselected : ¬ IsStationaryBelow kappa Nselected :=
    GroundingSimultaneousDecode.strongSelectedWarp_initialIndices_nonstationary
      (L.popularAuxiliaryIndexed hL) S (L.groundedConcreteControls hL S)
  have hcutSource : ¬ IsStationaryBelow kappa NcutSource :=
    GroundingSimultaneousDecode.sourceCutWarp_initialIndices_nonstationary
      (L.popularAuxiliaryIndexed hL) S
  have hfirst : IsStationaryBelow kappa (L.phiGround \ Nselected) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hground hselected
  have hsecond :
      IsStationaryBelow kappa ((L.phiGround \ Nselected) \ NcutSource) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      hL.legal.regular hL.legal.uncountable hfirst hcutSource
  obtain ⟨a, ⟨haGround, haSelected⟩, haCutSource⟩ := hsecond.nonempty
  exact ⟨a, haGround, haSelected, haCutSource⟩

end DWeb.KappaLadder

end Erdos599

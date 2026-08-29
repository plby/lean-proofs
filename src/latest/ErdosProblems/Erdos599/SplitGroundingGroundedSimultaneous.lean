/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAssertion819
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorGeometry
import ErdosProblems.Erdos599.SplitGroundingGroundedUnused
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparator818
import ErdosProblems.Erdos599.GroundingAssertion822Output

/-!
# Simultaneous switch for the grounded split separator

This module instantiates the generic component-compatible selector with the
strict 8.19 and exact 8.20 controls proved for the grounded split auxiliary.
All incidence, stopping, and antichain facts are then inherited from the
generic erased-switch construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingSimultaneousDecode
open GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The genuine grounded split control package: strict hanging-component
collisions from 8.19 and hanging-fragment collisions from 8.20. -/
noncomputable def splitGroundedControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    GroundingSelection.Controls S :=
  L.splitGroundedAssertion819StrictControls hL hground S
    (GroundingFragmentAssertion820.hangingFragmentWarpData S)

/-- The grounded switch stopped at an ambient boundary. -/
abbrev splitGroundedSelectedSwitchedEdgesAt
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (L.splitGroundedControls hL hground S) T

theorem splitGroundedSelectedSwitchedEdgesAt_subset_adj
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) :
    L.splitGroundedSelectedSwitchedEdgesAt hL hground S T ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  erasedSelectedSwitchedEdgesAt_subset_adj
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedControls hL hground S) T

theorem splitGroundedSelectedSwitchedEdgesAt_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) :
    Relator.BiUnique
      (fun x y ↦
        (x, y) ∈ L.splitGroundedSelectedSwitchedEdgesAt hL hground S T) :=
  erasedSelectedSwitchedEdgesAt_biUnique
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedControls hL hground S) T
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)

theorem splitGroundedSelectedSwitchedEdgesAt_reachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (T : Set V) :
    IsReachabilityAntichain
      (L.splitGroundedSelectedSwitchedEdgesAt hL hground S T) T := by
  intro b hb c _hc hbc
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (boundary_noOutgoing_switchedAt
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedControls hL hground S) T hb) hbc

/-- Every selected request path avoids the strict 8.19 family and the exact
8.20 fragment family used to construct the grounded controls. -/
theorem splitGroundedStrongSelectedPath_avoids_strict_and_fragment
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    let p := strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (L.splitGroundedControls hL hground S) r
    ¬ L.splitGroundedAssertion819StrictCollisionPath
        hL hground S r p ∧
      ¬ GroundingConcreteControls.hangingFragmentCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p := by
  dsimp only
  have hp := strongSelectedPath_mem_controlledRequestFan
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedControls hL hground S) r
  exact ⟨fun h ↦ hp.2 (Or.inl h), fun h ↦ hp.2 (Or.inr h)⟩

/-- Every literal hanging contact left after grounded strict pruning is an
equal-stage match for the selected path's own grounded source index. -/
theorem splitGroundedStrongSelectedPath_hangingCollision_equalMatch
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hcollision : GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r
        (strongSelectedPath
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
            (L.splitGroundedControls hL hground S) r)) :
    let p := strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
        (L.splitGroundedControls hL hground S) r
    let hp : p.start ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source :=
      (strongSelectedWarp
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (L.splitGroundedControls hL hground S)).starts_in_source ⟨r, rfl⟩
    Nonempty (L.SplitGroundedAssertion819EqualMatch hL hground S r
      ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, hp⟩)) := by
  dsimp only
  let p := strongSelectedPath
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedControls hL hground S) r
  have hpControlled := strongSelectedPath_mem_controlledRequestFan
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
      (L.splitGroundedControls hL hground S) r
  let hpCollision : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths :=
    ⟨hpControlled.1.1.1, hcollision⟩
  have hnot :=
    (L.splitGroundedStrongSelectedPath_avoids_strict_and_fragment
      hL hground S r).1
  have hmatch :=
    L.splitGroundedAssertion819EqualMatch_of_collision_of_not_strict
      hL hground S r p hpCollision hnot
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source hpCollision⟩ :
        (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start,
        (strongSelectedWarp
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
            (L.splitGroundedControls hL hground S)).starts_in_source
              ⟨r, rfl⟩⟩ := Subtype.ext rfl
  simpa only [congrArg
    (L.splitGroundedPopularAuxiliaryIndexed hL hground).f hs] using hmatch

/-- Exact grounded 8.22 packaging once every point of the selected boundary
has been rooted away from the stationary omitted source. -/
theorem splitGroundedAssertion822Output_of_frontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (R : L.SplitGroundedUnusedRecord hL hground S
      (L.splitGroundedControls hL hground S))
    (T : Set V)
    (hTsubset : T ⊆ GroundingCut.BB
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.splitGroundedSelectedSwitchedEdgesAt hL hground S T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut
    (L.splitGroundedSelectedSwitchedEdgesAt hL hground S T)
    (Gamma.source \ {R.record.initial}) T
    (L.splitGroundedSelectedSwitchedEdgesAt_subset_adj hL hground S T)
    (L.splitGroundedSelectedSwitchedEdgesAt_biUnique hL hground S T)
    Set.sdiff_subset hTsubset hTseparator
    (L.splitGroundedSelectedSwitchedEdgesAt_reachabilityAntichain
      hL hground S T)
    hroot R.record.initial R.grounded
  simp

/-- The literal `BB` is already an ambient separator by grounded split 8.18,
so source-rooting it supplies the complete 8.22 output. -/
theorem splitGroundedAssertion822Output_of_BB_rooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (R : L.SplitGroundedUnusedRecord hL hground S
      (L.splitGroundedControls hL hground S))
    (hroot : ∀ t ∈ GroundingCut.BB
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.splitGroundedSelectedSwitchedEdgesAt hL hground S
              (GroundingCut.BB
                (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) := by
  apply L.splitGroundedAssertion822Output_of_frontierGeometry
    hL hground S R
    (GroundingCut.BB (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    Subset.rfl
    (L.splitGroundedAssertion8_18 hL.legal S.cut S.separates)
  intro t ht
  exact hroot t ht

end KappaLadder
end DWeb
end Erdos599

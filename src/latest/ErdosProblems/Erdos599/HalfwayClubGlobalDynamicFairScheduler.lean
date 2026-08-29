/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClubDynamicFairScheduler
import ErdosProblems.Erdos599.HalfwayClubGlobalReferenceLimit

/-!
# Dynamic fair resolution for the global ladder reference

The global imaginary reference is a subwarp of the limiting ladder warp,
but need not have finite character.  This module is the global-reference
variant of `HalfwayClubDynamicFairScheduler`: source coverage at proper
limits is supplied by the ladder's hit-closure theorem.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}
variable {Sigma : Set (Ladder.Stage (succ kappa))}
variable {closedStage : Ladder.Stage (succ kappa) → Set V}

private abbrev globalClubSlice
    (L : Gamma.KappaLadder (succ kappa))
    (Sigma : Set (Ladder.Stage (succ kappa))) : Sigma → Set V :=
  fun s ↦ L.frontier s.1

private abbrev globalClubClosure
    (Sigma : Set (Ladder.Stage (succ kappa)))
    (closedStage : Ladder.Stage (succ kappa) → Set V) : Sigma → Set V :=
  fun s ↦ closedStage s.1

private abbrev globalClubPersistent
    (L : Gamma.KappaLadder (succ kappa)) : Set V :=
  L.limitRoof \ L.limitStrictRoof

namespace DynamicResolutionRecursor

/-- The dynamic recursor with proper limits certified from membership of
the reference warp in the actual limiting ladder warp. -/
noncomputable def ofMovingClubGlobalReference
    (M : AllRealTerminalMovingCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (slice := globalClubSlice L Sigma)
      (closure := globalClubClosure Sigma closedStage))
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (globalClubSlice L Sigma) (globalClubClosure Sigma closedStage))
    (bootstrap : V)
    (hbootstrap : bootstrap ∈ seed.blueprint.realPart.terminals)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    (hclosed : Monotone closedStage) (hkappa : aleph0 ≤ kappa) :
    DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (slice := globalClubSlice L Sigma)
      (closure := globalClubClosure Sigma closedStage) where
  kappa_infinite := hkappa
  seed := seed
  bootstrap := bootstrap
  bootstrap_terminal := hbootstrap
  successor := SchedulerSuccessor.ofMovingCompiler M
  properLimit := properLimitCompilerOfClubGlobalReference hL hHit hSigma
    hGamma hYwarp hYlimit hclosed hkappa

/-- Proper-limit geometry for the complete dynamic chain, using global
reference hit-continuity rather than finite character. -/
noncomputable def clubGlobalReferenceProperBoundary
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (slice := globalClubSlice L Sigma)
      (closure := globalClubClosure Sigma closedStage))
    [Nonempty (RegularCardinal.Stage kappa)]
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    (hclosed : Monotone closedStage) :
    ResolutionChain.ProperRelationLimitBoundary D.dynamicChain := by
  exact ResolutionChain.properRelationLimitBoundaryOfClubGlobalReference
    D.dynamicChain hL hHit hSigma hGamma hYwarp hYlimit hclosed
    D.kappa_infinite dynamicIndex_card_le

/-- The all-real final boundary obtained after every dynamically born real
terminal has been served. -/
noncomputable def clubGlobalReferenceFinalBoundary
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (slice := globalClubSlice L Sigma)
      (closure := globalClubClosure Sigma closedStage))
    [Nonempty (RegularCardinal.Stage kappa)]
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    (hclosed : Monotone closedStage) :
    ResolutionChain.FinalRelationLimitBoundary D.dynamicChain := by
  exact ResolutionChain.finalRelationLimitBoundaryOfClubCompletion
    D.dynamicChain
    (D.clubGlobalReferenceProperBoundary hL hHit hSigma hGamma hYwarp
      hYlimit hclosed)
    hGamma D.kappa_infinite
    (ResolutionChain.successfulResolutionEnumeration_eventuallyCompleted
      D.successfulDynamicEnumeration)

/-- Complete fair all-real limit for the source's global reference warp. -/
noncomputable def clubGlobalReferenceFairResolutionLimit
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (slice := globalClubSlice L Sigma)
      (closure := globalClubClosure Sigma closedStage))
    [Nonempty (RegularCardinal.Stage kappa)]
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    (hclosed : Monotone closedStage) :
    ResolutionChain.FairResolutionLimit D.dynamicChain D.seed := by
  exact ResolutionChain.FairResolutionLimit.ofSuccessfulEnumeration
    (D.clubGlobalReferenceFinalBoundary hL hHit hSigma hGamma hYwarp
      hYlimit hclosed)
    D.successfulDynamicEnumeration

/-- Canonical form constructing nonemptiness of the run index from the
dynamic recursor's zero stage. -/
noncomputable def clubGlobalReferenceFairResolutionLimitCanonical
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := globalClubPersistent L) (B := Gamma.target)
      (slice := globalClubSlice L Sigma)
      (closure := globalClubClosure Sigma closedStage))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    (hclosed : Monotone closedStage) :
    letI : Nonempty (RegularCardinal.Stage kappa) := ⟨D.zeroStage⟩
    ResolutionChain.FairResolutionLimit D.dynamicChain D.seed := by
  letI : Nonempty (RegularCardinal.Stage kappa) := ⟨D.zeroStage⟩
  exact D.clubGlobalReferenceFairResolutionLimit hL hHit hSigma hGamma
    hYwarp hYlimit hclosed

end DynamicResolutionRecursor
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599

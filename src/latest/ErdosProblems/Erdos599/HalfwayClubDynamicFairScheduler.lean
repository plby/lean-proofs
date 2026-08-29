/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedDynamicScheduler
import ErdosProblems.Erdos599.MovingSchedulerSuccessor
import ErdosProblems.Erdos599.HalfwayClubIndexedLimitProvider

/-!
# Concrete club-indexed dynamic fair resolution

This module composes the moving all-real-terminal successor, the bounded
club-indexed proper-limit compiler, and the dynamic born-terminal queue.
The final all-real relation boundary is then derived from the same club
geometry and the proved successful enumeration.
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

private abbrev clubSlice
    (L : Gamma.KappaLadder (succ kappa))
    (Sigma : Set (Ladder.Stage (succ kappa))) : Sigma → Set V :=
  fun s ↦ L.frontier s.1

private abbrev clubClosure
    (Sigma : Set (Ladder.Stage (succ kappa)))
    (closedStage : Ladder.Stage (succ kappa) → Set V) : Sigma → Set V :=
  fun s ↦ closedStage s.1

private abbrev clubPersistent
    (L : Gamma.KappaLadder (succ kappa)) : Set V :=
  L.limitRoof \ L.limitStrictRoof

namespace DynamicResolutionRecursor

/-- The actual dynamic recursor over a chosen club of deferred-ladder
stages. -/
noncomputable def ofMovingClub
    (M : AllRealTerminalMovingCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (slice := clubSlice L Sigma)
      (closure := clubClosure Sigma closedStage))
    (seed : IndexedTerminalResolutionState
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (clubSlice L Sigma) (clubClosure Sigma closedStage))
    (bootstrap : V)
    (hbootstrap : bootstrap ∈ seed.blueprint.realPart.terminals)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) (hkappa : aleph0 ≤ kappa) :
    DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (slice := clubSlice L Sigma)
      (closure := clubClosure Sigma closedStage) where
  kappa_infinite := hkappa
  seed := seed
  bootstrap := bootstrap
  bootstrap_terminal := hbootstrap
  successor := SchedulerSuccessor.ofMovingCompiler M
  properLimit := properLimitCompilerOfClub hL hHit hSigma hGamma
    hYwarp hYfinite hclosed hkappa

/-- Cardinal bound for the complete dynamic run index. -/
theorem dynamicIndex_card_le :
    lift.{u} #(RegularCardinal.Stage kappa) ≤ lift.{u + 1} kappa := by
  simp only [Stationary.mk_below, Cardinal.lift_lift]
  exact le_rfl

/-- Proper-limit geometry at the supremum of the complete dynamic chain. -/
noncomputable def clubProperBoundary
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (slice := clubSlice L Sigma)
      (closure := clubClosure Sigma closedStage))
    [Nonempty (RegularCardinal.Stage kappa)]
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) :
    ResolutionChain.ProperRelationLimitBoundary D.dynamicChain := by
  exact ResolutionChain.properRelationLimitBoundaryOfClub D.dynamicChain
    hL hHit hSigma hGamma hYwarp hYfinite hclosed D.kappa_infinite
    dynamicIndex_card_le

/-- Final all-real boundary, derived from the dynamic fairness theorem. -/
noncomputable def clubFinalBoundary
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (slice := clubSlice L Sigma)
      (closure := clubClosure Sigma closedStage))
    [Nonempty (RegularCardinal.Stage kappa)]
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) :
    ResolutionChain.FinalRelationLimitBoundary D.dynamicChain := by
  let E := D.successfulDynamicEnumeration
  exact ResolutionChain.finalRelationLimitBoundaryOfClubCompletion
    D.dynamicChain
    (D.clubProperBoundary hL hHit hSigma hGamma hYwarp hYfinite hclosed)
    hGamma D.kappa_infinite
    (ResolutionChain.successfulResolutionEnumeration_eventuallyCompleted E)

/-- Complete fair all-real limit of the dynamic club-indexed run. -/
noncomputable def clubFairResolutionLimit
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (slice := clubSlice L Sigma)
      (closure := clubClosure Sigma closedStage))
    [Nonempty (RegularCardinal.Stage kappa)]
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) :
    ResolutionChain.FairResolutionLimit D.dynamicChain D.seed := by
  exact ResolutionChain.FairResolutionLimit.ofSuccessfulEnumeration
    (D.clubFinalBoundary hL hHit hSigma hGamma hYwarp hYfinite hclosed)
    D.successfulDynamicEnumeration

/-- Same output with the nonempty run-index instance constructed from the
dynamic recursor itself. -/
noncomputable def clubFairResolutionLimitCanonical
    (D : DynamicResolutionRecursor
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := clubPersistent L) (B := Gamma.target)
      (slice := clubSlice L Sigma)
      (closure := clubClosure Sigma closedStage))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) :
    letI : Nonempty (RegularCardinal.Stage kappa) := ⟨D.zeroStage⟩
    ResolutionChain.FairResolutionLimit D.dynamicChain D.seed := by
  letI : Nonempty (RegularCardinal.Stage kappa) := ⟨D.zeroStage⟩
  exact D.clubFairResolutionLimit hL hHit hSigma hGamma hYwarp hYfinite hclosed

#print axioms ofMovingClub
#print axioms clubFinalBoundary
#print axioms clubFairResolutionLimit
#print axioms clubFairResolutionLimitCanonical

end DynamicResolutionRecursor
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599

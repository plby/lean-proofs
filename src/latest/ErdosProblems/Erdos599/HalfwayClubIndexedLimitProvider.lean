/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClubIndexedLimit
import ErdosProblems.Erdos599.HalfwayClubRangeSup

/-!
# The bounded club-indexed proper-limit compiler

The supremum club stage is constructed from the actual history. Its attained
and genuine-limit cases both use the proved geometric constructors. The
result is the complete proper-limit compiler for a run of length `kappa.ord`,
with no result-producing limit hypothesis.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}
variable {Sigma : Set (Ladder.Stage (succ kappa))}
variable {closedStage : Ladder.Stage (succ kappa) → Set V}

namespace ResolutionChain

variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- The proper boundary at the actual club-valued supremum of an arbitrary
coherent history with at most `kappa` stages. -/
noncomputable def properRelationLimitBoundaryOfClub
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage)
    (hkappa : aleph0 ≤ kappa)
    (hindexCard : lift.{u} #I ≤ lift.{v} kappa) :
    ProperRelationLimitBoundary C := by
  let idx : I → Ladder.Stage (succ kappa) :=
    fun i ↦ (C.stage i).stageIndex.1
  have hmono : Monotone idx := by
    intro i j hij
    exact (C.refiningExtends hij).stage_mono
  let D : HalfwayClubRangeSup.Data Sigma idx :=
    (HalfwayClubRangeSup.exists_data hkappa hindexCard hSigma idx hmono
      (fun i ↦ (C.stage i).stageIndex.2)).some
  let a : Sigma := ⟨D.supIndex, D.supIndex_mem⟩
  apply Classical.choice
  rcases D.attained_or_genuineLimit with hattained | ⟨hstrict, hlimit⟩
  · exact ⟨properRelationLimitBoundaryOfClubAttained C hL hGamma
      hYwarp hYfinite hclosed hkappa hindexCard a D.range_isLUB hattained⟩
  · exact ⟨properRelationLimitBoundaryOfClubLimit C hL hHit hGamma
      hYwarp hYfinite hclosed hkappa hindexCard a hlimit hstrict D.range_isLUB⟩

end ResolutionChain

/-- A proper ordinal initial history below an infinite initial ordinal
has at most the run cardinal, with universe lifts kept explicit. -/
theorem initialHistory_card_le {o : Ordinal.{u}} (ho : o < kappa.ord) :
    lift.{u} #(Set.Iio o) ≤ lift.{u + 1} kappa := by
  have hcard : o.card ≤ kappa := by
    simpa only [Cardinal.card_ord] using Ordinal.card_le_card ho.le
  simpa only [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift] using
    (Cardinal.lift_le.{u + 1}.2 hcard)

/-- All proper-limit boundaries for the actual kappa-sized club-indexed
run. The history itself supplies the monotonicity of its ladder indices. -/
theorem properRelationLimitBoundaryProviderOfClub
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) (hkappa : aleph0 ≤ kappa) :
    ProperRelationLimitBoundaryProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := L.limitRoof \ L.limitStrictRoof) (B := Gamma.target)
      (slice := fun s : Sigma ↦ L.frontier s.1)
      (closure := fun s : Sigma ↦ closedStage s.1) kappa.ord := by
  intro o hoLength ho prior hcoherent
  let : Nonempty (Set.Iio o) := ho.nonempty_Iio.to_subtype
  change Nonempty (ResolutionChain.ProperRelationLimitBoundary
    (ResolutionChain.ofPrior prior hcoherent))
  exact ⟨ResolutionChain.properRelationLimitBoundaryOfClub
    (ResolutionChain.ofPrior prior hcoherent) hL hHit hSigma hGamma
    hYwarp hYfinite hclosed hkappa (initialHistory_card_le hoLength)⟩

/-- The source-faithful bounded proper-limit compiler, derived from the
canonical relation and concrete club/ladder geometry. -/
theorem properLimitCompilerOfClub
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage) (hkappa : aleph0 ≤ kappa) :
    ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := L.limitRoof \ L.limitStrictRoof) (B := Gamma.target)
      (fun s : Sigma ↦ L.frontier s.1)
      (fun s : Sigma ↦ closedStage s.1) kappa.ord :=
  properLimitCompilerOfBoundaryProvider
    (properRelationLimitBoundaryProviderOfClub hL hHit hSigma hGamma
      hYwarp hYfinite hclosed hkappa)

#print axioms ResolutionChain.properRelationLimitBoundaryOfClub
#print axioms properRelationLimitBoundaryProviderOfClub
#print axioms properLimitCompilerOfClub

end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599

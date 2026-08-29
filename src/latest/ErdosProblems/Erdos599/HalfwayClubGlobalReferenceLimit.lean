/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClubIndexedLimitProvider
import ErdosProblems.Erdos599.IndexedRelationLimitHitSource

/-!
# Club-indexed proper limits with the global reference warp

The imaginary-edge reference may contain infinite paths.  Source coverage
therefore comes from the ladder's proved hit-stage closure, not from finite
support compactness.  This file constructs the complete bounded proper-limit
compiler for any reference subwarp of the actual limiting ladder warp.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v

namespace IndexedRealExtensionChain

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {B persistent : Set V}

/-- The five geometric fields combine with a separately proved source-cover
field.  No finiteness assumption on the reference family is necessary. -/
theorem eventualRelationBlueprint_isLinkageBlueprint_of_covers_source
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice closed : I → Set V) (T Z : Set V)
    (hstage : ∀ i, (C.stage i).IsLinkageBlueprint
      (slice i) (closed i) persistent)
    (hstable : ∀ i, (C.stage i).Stable (slice i) persistent)
    (hcover : Gamma.source ⊆ C.eventualRelationBlueprint.initialSet ∪
      C.eventualRelationBlueprint.retainedReferenceInitials T)
    (hroof : ∀ i, Gamma.roof (slice i) ⊆ Gamma.roof T)
    (hclosed : ∀ i, closed i ⊆ Z)
    (hkappa : aleph0 ≤ kappa)
    (hindex : lift.{u} #I ≤ lift.{v} kappa)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target)
    (hB : B ∩ C.realVertexLimit ⊆ persistent) :
    C.eventualRelationBlueprint.IsLinkageBlueprint T Z persistent where
  vertices_roofed := by
    intro x hx
    rw [C.eventualRelationBlueprint_vertexSet] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact hroof i ((hstage i).vertices_roofed hxi)
  covers_source := hcover
  vertices_closed := by
    intro x hx
    rw [C.eventualRelationBlueprint_vertexSet] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact hclosed i ((hstage i).vertices_closed hxi)
  card_paths := C.eventualRelationBlueprint_card_paths_le
    (C.mk_realVertexLimit_le hkappa hindex (fun i ↦ (hstage i).card_paths))
  infinitely_many_strong := C.eventualRelationBlueprint_infinitelyManyStrong
    (fun i ↦ (hstage i).infinitely_many_strong) hGamma hBtarget
  terminals_popular := by
    intro x hx
    apply Or.inl
    rcases C.eventualTerminal_popular_or_persistent slice closed
        hstage hstable hB hx with hxpop | hxpersistent
    · exact hxpop
    · exact Or.inl hxpersistent

end IndexedRealExtensionChain

namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder (succ kappa)}
variable {Sigma : Set (Ladder.Stage (succ kappa))}
variable {closedStage : Ladder.Stage (succ kappa) → Set V}

namespace ResolutionChain

variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- Every proper-limit boundary field at the actual supremum of club
indices, using hit-continuity for the possibly infinite global reference. -/
noncomputable def properRelationLimitBoundaryOfClubGlobalReference
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
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
  have hupper : ∀ i, idx i ≤ a.1 :=
    fun i ↦ D.range_isLUB.1 ⟨i, rfl⟩
  have hB := club_target_inter_realVertexLimit_subset_persistent C
  refine
    { limitIndex := a
      isBlueprint := ?_
      stable := ?_
      index_upper := fun i ↦ hupper i
      index_least := ?_ }
  · apply C.toIndexedRealExtensionChain.eventualRelationBlueprint_isLinkageBlueprint_of_covers_source
      (fun i ↦ L.frontier (idx i)) (fun i ↦ closedStage (idx i))
      (L.frontier a.1) (closedStage a.1)
      (fun i ↦ (C.stage i).isBlueprint) (fun i ↦ (C.stage i).stable)
      ?_ (fun i ↦ roof_frontier_mono_of_deferredLegal hL (hupper i))
      (fun i ↦ hclosed (hupper i)) hkappa hindexCard hGamma Set.Subset.rfl hB
    exact C.toIndexedRealExtensionChain.eventualRelationBlueprint_covers_source_of_limitHitClosure
      L hHit idx hmono D.range_isLUB
      (fun i ↦ (C.stage i).stageIndex.2)
      (fun i ↦ (C.stage i).isBlueprint.covers_source) hYwarp hYlimit
  · exact C.toIndexedRealExtensionChain.eventualRelationBlueprint_stable
      (fun i ↦ L.frontier (idx i)) (fun i ↦ closedStage (idx i))
      (L.frontier a.1) (fun i ↦ (C.stage i).isBlueprint)
      (fun i ↦ (C.stage i).stable)
      (fun i ↦ oldRoof_inter_laterFrontier_subset hL (hupper i)) hB
  · intro b hb
    exact D.range_isLUB.2 (by rintro _ ⟨i, rfl⟩; exact hb i)

end ResolutionChain

/-- Proper boundaries for the actual bounded run with a global reference;
only membership in the limit warp replaces the earlier finite-character
premise. -/
theorem properRelationLimitBoundaryProviderOfClubGlobalReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
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
  exact ⟨ResolutionChain.properRelationLimitBoundaryOfClubGlobalReference
    (ResolutionChain.ofPrior prior hcoherent) hL hHit hSigma hGamma
    hYwarp hYlimit hclosed hkappa (initialHistory_card_le hoLength)⟩

/-- The bounded proper-limit compiler for the source's global imaginary
reference.  All boundary fields are constructed above. -/
theorem properLimitCompilerOfClubGlobalReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hSigma : Stationary.IsClubBelow (succ kappa) Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYlimit : Y ⊆ L.limitWarp)
    (hclosed : Monotone closedStage) (hkappa : aleph0 ≤ kappa) :
    ProperLimitCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      (persistent := L.limitRoof \ L.limitStrictRoof) (B := Gamma.target)
      (fun s : Sigma ↦ L.frontier s.1)
      (fun s : Sigma ↦ closedStage s.1) kappa.ord :=
  properLimitCompilerOfBoundaryProvider
    (properRelationLimitBoundaryProviderOfClubGlobalReference hL hHit hSigma hGamma
      hYwarp hYlimit hclosed hkappa)

#print axioms ResolutionChain.properRelationLimitBoundaryOfClubGlobalReference
#print axioms properRelationLimitBoundaryProviderOfClubGlobalReference
#print axioms properLimitCompilerOfClubGlobalReference

end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599

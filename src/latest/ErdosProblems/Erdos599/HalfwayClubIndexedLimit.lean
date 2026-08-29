/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedLadderBoundary
import ErdosProblems.Erdos599.DeferredLadderLimitFrontierContinuity
import ErdosProblems.Erdos599.IndexedFinalRelationGeometry

/-!
# Concrete proper limits with the club retained in the index type

The state index is a member of the chosen club, so an arbitrary coherent
prior history cannot silently leave that club. At a genuine cofinal limit,
deferred-ladder continuity and finite reference supports construct every
blueprint boundary field. The target and stability fields are consequences
of actual ladder roofs. No limit blueprint certificate is a premise.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedTerminalResolutionState
namespace ReachableResolutionRecursor
namespace ResolutionChain

universe u v

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}
variable {L : Gamma.KappaLadder theta}
variable {Sigma : Set (Ladder.Stage theta)}
variable {closedStage : Ladder.Stage theta → Set V}

abbrev ClubChain := ResolutionChain
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := L.limitRoof \ L.limitStrictRoof) (B := Gamma.target)
  (slice := fun s : Sigma ↦ L.frontier s.1)
  (closure := fun s : Sigma ↦ closedStage s.1) I

/-- Target geometry for a chain whose actual indices are club members. -/
theorem club_target_inter_realVertexLimit_subset_persistent
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I)) :
    Gamma.target ∩ C.toIndexedRealExtensionChain.realVertexLimit ⊆
      L.limitRoof \ L.limitStrictRoof := by
  rintro x ⟨hxB, hxLimit⟩
  change x ∈ ⋃ i, (C.stage i).blueprint.realPart.vertices at hxLimit
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxLimit
  refine ⟨?_, ?_⟩
  · exact Set.mem_iUnion.2 ⟨(C.stage i).stageIndex.1,
      (C.stage i).isBlueprint.vertices_roofed hxi⟩
  · intro hxStrict
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hxStrict
    exact target_not_mem_strictRoof hxB hxa

/-- Every essential frontier is its roof minus its strict roof. -/
theorem frontier_eq_roof_sdiff_strictRoof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (a : Ladder.Stage theta) :
    L.frontier a = Gamma.roof (L.frontier a) \ Gamma.strictRoof (L.frontier a) := by
  ext x
  constructor
  · intro hx
    refine ⟨Gamma.subset_roof _ hx, ?_⟩
    rintro ⟨_, hnotEssential⟩
    apply hnotEssential
    rw [hL.frontiersEssential a]
    exact hx
  · rintro ⟨hxRoof, hxNotStrict⟩
    by_contra hx
    exact hxNotStrict ⟨hxRoof, fun he ↦ hx (Gamma.essential_subset _ he)⟩

/-- Construct every proper-limit field from a proved frontier inclusion. -/
noncomputable def properRelationLimitBoundaryOfClubBoundary
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage)
    (hkappa : aleph0 ≤ kappa)
    (hindexCard : lift.{u} #I ≤ lift.{v} kappa)
    (a : Sigma)
    (hLUB : IsLUB (Set.range (fun i ↦ (C.stage i).stageIndex.1)) a.1)
    (hboundary : ((⋃ i, Gamma.roof (L.frontier (C.stage i).stageIndex.1)) \
      ⋃ i, Gamma.strictRoof (L.frontier (C.stage i).stageIndex.1)) ⊆ L.frontier a.1) :
    ProperRelationLimitBoundary C := by
  let idx : I → Ladder.Stage theta := fun i ↦ (C.stage i).stageIndex.1
  have hmono : Monotone idx := by
    intro i j hij
    exact (C.refiningExtends hij).stage_mono
  have hupper : ∀ i, idx i ≤ a.1 := fun i ↦ hLUB.1 ⟨i, rfl⟩
  have hB := club_target_inter_realVertexLimit_subset_persistent C
  refine
    { limitIndex := a
      isBlueprint := ?_
      stable := ?_
      index_upper := fun i ↦ hupper i
      index_least := ?_ }
  · exact C.toIndexedRealExtensionChain.eventualRelationBlueprint_isLinkageBlueprint
      (fun i ↦ L.frontier (idx i)) (fun i ↦ closedStage (idx i))
      (fun i ↦ Gamma.roof (L.frontier (idx i)))
      (fun i ↦ Gamma.strictRoof (L.frontier (idx i)))
      (L.frontier a.1) (closedStage a.1)
      (fun i ↦ (C.stage i).isBlueprint) (fun i ↦ (C.stage i).stable)
      hYwarp hYfinite (fun i ↦ frontier_eq_roof_sdiff_strictRoof hL (idx i))
      (fun i j hij ↦ hL.strictRoof_frontier_mono (hmono hij)) hboundary
      (fun i ↦ roof_frontier_mono_of_deferredLegal hL (hupper i))
      (fun i ↦ hclosed (hupper i)) hkappa hindexCard hGamma Set.Subset.rfl hB
  · exact C.toIndexedRealExtensionChain.eventualRelationBlueprint_stable
      (fun i ↦ L.frontier (idx i)) (fun i ↦ closedStage (idx i))
      (L.frontier a.1) (fun i ↦ (C.stage i).isBlueprint)
      (fun i ↦ (C.stage i).stable)
      (fun i ↦ oldRoof_inter_laterFrontier_subset hL (hupper i)) hB
  · intro b hb
    exact hLUB.2 (by rintro _ ⟨i, rfl⟩; exact hb i)

/-- The genuine-limit constructor discharges the frontier inclusion with
the actual deferred-ladder continuity theorem. -/
noncomputable def properRelationLimitBoundaryOfClubLimit
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage)
    (hkappa : aleph0 ≤ kappa)
    (hindexCard : lift.{u} #I ≤ lift.{v} kappa)
    (a : Sigma) (haLimit : IsSuccLimit a.1.1)
    (hindex : ∀ i, (C.stage i).stageIndex.1 < a.1)
    (hLUB : IsLUB (Set.range (fun i ↦ (C.stage i).stageIndex.1)) a.1) :
    ProperRelationLimitBoundary C := by
  apply properRelationLimitBoundaryOfClubBoundary C hL hGamma
    hYwarp hYfinite hclosed hkappa hindexCard a hLUB
  exact DWeb.KappaLadder.Deferred.iUnion_roof_sdiff_iUnion_strictRoof_subset_frontier
    hL hHit (fun i ↦ (C.stage i).stageIndex.1)
    (fun _ _ hij ↦ (C.refiningExtends hij).stage_mono)
    haLimit hindex hLUB (fun i ↦ (C.stage i).stageIndex.2)

/-- If the supremum index is attained, source retention uses the actual
maximum frontier and needs no genuine-limit premise. -/
noncomputable def properRelationLimitBoundaryOfClubAttained
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I))
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hclosed : Monotone closedStage)
    (hkappa : aleph0 ≤ kappa)
    (hindexCard : lift.{u} #I ≤ lift.{v} kappa)
    (a : Sigma)
    (hLUB : IsLUB (Set.range (fun i ↦ (C.stage i).stageIndex.1)) a.1)
    (hattained : ∃ i, (C.stage i).stageIndex.1 = a.1) :
    ProperRelationLimitBoundary C := by
  apply properRelationLimitBoundaryOfClubBoundary C hL hGamma
    hYwarp hYfinite hclosed hkappa hindexCard a hLUB
  rintro x ⟨hxRoofUnion, hxNotStrictUnion⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxRoofUnion
  have hxRoof : x ∈ Gamma.roof (L.frontier a.1) :=
    roof_frontier_mono_of_deferredLegal hL (hLUB.1 ⟨i, rfl⟩) hxi
  obtain ⟨j, hj⟩ := hattained
  have hxNotStrict : x ∉ Gamma.strictRoof (L.frontier a.1) := by
    intro hxStrict
    apply hxNotStrictUnion
    exact Set.mem_iUnion.2 ⟨j, by simpa only [hj] using hxStrict⟩
  by_contra hxNotFrontier
  exact hxNotStrict ⟨hxRoof,
    fun hxEssential ↦ hxNotFrontier (Gamma.essential_subset _ hxEssential)⟩

/-- Final all-real geometry is derived from the proper geometry and fair
terminal completion, at the same actual supremum club index. -/
noncomputable def finalRelationLimitBoundaryOfClubCompletion
    (C : ClubChain (L := L) (Sigma := Sigma) (closedStage := closedStage)
      (Y := Y) (kappa := kappa) (I := I))
    (D : ProperRelationLimitBoundary C)
    (hGamma : Gamma.IsNormalized) (hkappa : aleph0 ≤ kappa)
    (hcompleted : ∀ i x, x ∈ (C.stage i).blueprint.realPart.terminals →
      ∃ j, x ∈ (C.stage j).blueprint.completedRealVertices Gamma.target) :
    FinalRelationLimitBoundary C where
  limitIndex := D.limitIndex
  isBlueprint := C.toIndexedRealExtensionChain.realRelationBlueprint_isLinkageBlueprint
    D.isBlueprint hkappa (fun i ↦ (C.stage i).isBlueprint.infinitely_many_strong)
    hGamma Set.Subset.rfl hcompleted
    (club_target_inter_realVertexLimit_subset_persistent C)
  stable := C.toIndexedRealExtensionChain.realRelationBlueprint_stable
    (L.frontier D.limitIndex.1) hcompleted
    (club_target_inter_realVertexLimit_subset_persistent C)
  index_upper := D.index_upper
  index_least := D.index_least

#print axioms properRelationLimitBoundaryOfClubLimit
#print axioms finalRelationLimitBoundaryOfClubCompletion

end ResolutionChain
end ReachableResolutionRecursor
end IndexedTerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599


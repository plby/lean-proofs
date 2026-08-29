/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointPostClosureAttachment
import ErdosProblems.Erdos599.ColouredSafeActivatedPrefixes
import ErdosProblems.Erdos599.ColouredSafeAugmentedRealReach

/-!
# Source-covered attachment with the actual scheduled real front

The activated finite prefixes and the old-priority relation are assembled for
the actual endpoint assignment. The same output retains the old carrier and
edges, satisfies full-reference source coverage at the later stage, and contains
the selected real front ending at a full terminal. The ambient-target suffix
and the final blueprint accounting are not conflated with this front.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction
namespace EndpointReferenceAssignment

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint ColouredSafeMovingStages ColouredSafeGraphLift
open ColouredSafeActivatedPrefixes
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}
variable {T : NativePostClosureIntervalTransaction C seed z R}
variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}
variable (A : NativePostClosureIntervalTransaction.EndpointReferenceAssignment T F)

/-- Full-reference source coverage is restored in the same actual output
which retains the old warp and the scheduled real front. -/
theorem exists_sourceCoveredAttachment {W : Set (web C).DPath}
    (hW : IsBlueprint C C.newStage W)
    (hWseed : (web C).vertexSet W ⊆ seed)
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet)
    (hz : z ∈ (web C).terminalFrontier W) :
    let K := seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet
    ∃ U : Set (web C).DPath, (web C).IsWarp U ∧
      familyEdges U = RootReachableRelation.edges (A.attachedEdges K) ((web C).initialSet K) ∧
      (web C).vertexSet U =
        RootReachableRelation.carrier (A.attachedEdges K) ((web C).initialSet K) ∧
      (web C).initialSet U = (web C).initialSet K ∧
      (web C).terminalFrontier U =
        {x | x ∈ (web C).vertexSet U ∧ ¬HasOutgoing (A.attachedEdges K) x} ∧
      (web C).vertexSet W ⊆ (web C).vertexSet U ∧
      familyEdges W ⊆ familyEdges U ∧
      (web C).initialSet W ⊆ (web C).initialSet U ∧
      (web C).vertexSet U ⊆ R.closedSet ∧
      Gamma.source ⊆ (web C).initialSet U ∪ Gamma.initialSet
        (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier R.later.stage) \
          referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet U)) ∧
      T.interval.front.support ⊆ (web C).vertexSet U ∧
      T.interval.front.edgeSet ⊆ familyEdges U ∧
      T.interval.front.finish ∈ (web C).terminalFrontier U ∧
      RealReach Gamma (web C) U z T.interval.front.finish ∧
      (∀ {x y}, y ∈ (web C).vertexSet W → (x, y) ∈ familyEdges U →
        (x, y) ∈ familyEdges W) := by
  dsimp only
  let K := seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet
  have hKV : (web C).vertexSet K = (web C).vertexSet W ∪ Gamma.vertexSet
      (prefixes C.ladder C.newStage ((web C).vertexSet W) R.closedSet) :=
    seedFamily_vertices _
  have hKI : (web C).initialSet K = (web C).initialSet W ∪ Gamma.initialSet
      (prefixes C.ladder C.newStage ((web C).vertexSet W) R.closedSet) :=
    seedFamily_initials _
  have hKE : familyEdges K = familyEdges W ∪ familyEdges
      (prefixes C.ladder C.newStage ((web C).vertexSet W) R.closedSet) :=
    seedFamily_edges _
  have hKW : (web C).IsWarp K := seedFamily_isWarp _ C.legal hW.isWarp
  have hKR : (web C).vertexSet K ⊆ Gamma.roof C.newSlice := by
    rw [hKV]
    exact Set.union_subset hW.vertices_roofed (vertices_roofed C.legal)
  have hKX : (web C).vertexSet K ⊆ R.closedSet := by
    rw [hKV]
    exact Set.union_subset (hWseed.trans R.seed_subset)
      (vertices_subset_closed C.legal R.reference_closed)
  have hWK : (web C).vertexSet W ⊆ (web C).vertexSet K := by
    rw [hKV]
    exact Set.subset_union_left
  have hWKE : familyEdges W ⊆ familyEdges K := by
    rw [hKE]
    exact Set.subset_union_left
  have hzK : z ∈ (web C).terminalFrontier K := by
    rw [seedFamily_terminals]
    exact Or.inl hz
  obtain ⟨U, hU, hUE, hUV, hUI, hUT, hkeepV, hkeepE, hcarrier, hfresh⟩ :=
    A.exists_attachedWarp hKW hKR hclosed
  have hUX : (web C).vertexSet U ⊆ R.closedSet :=
    hcarrier.trans (Set.union_subset hKX (fun _ hx ↦ hx.2))
  have hWI : (web C).initialSet W ⊆ (web C).initialSet U := by
    rw [hUI, hKI]
    exact Set.subset_union_left
  have hPI : Gamma.initialSet
      (prefixes C.ladder C.newStage ((web C).vertexSet W) R.closedSet) ⊆
        (web C).initialSet U := by
    rw [hUI, hKI]
    exact Set.subset_union_right
  have hlost : referencePathsMeeting C.ladder.limitWarp C.newSlice \
      referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier R.later.stage) ⊆
        referencePathsMeeting C.ladder.limitWarp R.closedSet := by
    intro p hp
    refine ⟨hp.1.1, p.initial, p.initial_mem_support, ?_⟩
    exact R.difference_subset ⟨p, Or.inl hp, p.initial_mem_support⟩
  have hcover := source_coverage C.legal R.reference_closed hW.covers_source hWI hPI
    (hUX.trans Set.subset_union_right) hlost
  have hfrontE := A.front_edgeSet_subset_attached hKW hKR hzK
  have hzV : z ∈ (web C).vertexSet K := by
    obtain ⟨p, hp, hpz⟩ := hzK
    exact ⟨p, hp, (web C).terminal_mem_support hpz⟩
  have hfrontStart : T.interval.front.start ∈
      RootReachableRelation.carrier (A.attachedEdges K) ((web C).initialSet K) := by
    rw [T.interval.front_start, ← hUV]
    exact hkeepV hzV
  have hpV : T.interval.front.support ⊆ (web C).vertexSet U := by
    rw [hUV]
    exact RootReachableRelation.path_support_subset_carrier _ _
      (Gamma := Gamma) (.inl T.interval.front) hfrontE hfrontStart
  have hpE : T.interval.front.edgeSet ⊆ familyEdges U := by
    rw [hUE]
    exact RootReachableRelation.path_edgeSet_subset_edges _ _
      (Gamma := Gamma) (.inl T.interval.front) hfrontE hfrontStart
  refine ⟨U, hU, hUE, hUV, hUI, hUT, hWK.trans hkeepV, hWKE.trans hkeepE,
    hWI, hUX, hcover, hpV, hpE, ?_, ?_, ?_⟩
  · rw [hUT]
    exact ⟨hpV T.interval.front.finish_mem_support,
      A.front_finish_noOutgoing_attached hKW hKR hzK⟩
  · simpa only [T.interval.front_start] using RealReach.of_path T.interval.front hpV hpE
  · intro x y hy he
    have hk := hfresh (hWK hy) he
    rw [hKE] at hk
    rcases hk with hk | hk
    · exact hk
    · exact False.elim (Set.disjoint_left.mp vertices_disjoint
        (familyEdges_subset_vertexSet_prod _ hk).2 hy)

#print axioms exists_sourceCoveredAttachment

end EndpointReferenceAssignment
end Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction

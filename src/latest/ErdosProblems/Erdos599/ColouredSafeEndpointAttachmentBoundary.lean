/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointSourceCoveredAttachment
import ErdosProblems.Erdos599.MarkedRaySubset

/-!
# Marked rays and popular sinks of the actual endpoint attachment

Fresh edges never enter the seed roof. Every ray therefore stays in the seed
or has a fresh-only tail. Sinks are popular by the actual interval assignment
and the exact seed boundary, not by a hypothesized completed blueprint.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction
namespace EndpointReferenceAssignment

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint ColouredSafeMovingStages
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
variable {W : Set (web C).DPath}

theorem attachedCarrier_subset :
    RootReachableRelation.carrier (A.attachedEdges W) ((web C).initialSet W) ⊆
      (web C).vertexSet W ∪ sourceInsideCarrier T.interval.ambientInterval R.closedSet := by
  apply RootReachableRelation.carrier_subset
  · rintro x ⟨p, hp, hpx⟩
    exact Or.inl ⟨p, hp, hpx.symm ▸ p.initial_mem_support⟩
  · intro e he
    rcases he with he | he
    · have h := familyEdges_subset_vertexSet_prod _ he
      exact ⟨Or.inl h.1, Or.inl h.2⟩
    · have h := A.closedEdges_subset_insideCarrier he.1
      exact ⟨Or.inr h.1, Or.inr h.2⟩

theorem attached_sink_popular (hW : (web C).IsWarp W)
    (hWX : (web C).vertexSet W ⊆ R.closedSet)
    (hterm : (web C).terminalFrontier W ⊆ popular C ∪ C.newSlice)
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet)
    {x : V}
    (hx : x ∈ RootReachableRelation.carrier (A.attachedEdges W) ((web C).initialSet W))
    (hno : ¬HasOutgoing (A.attachedEdges W) x) : x ∈ popular C := by
  have hnoW : ¬HasOutgoing (familyEdges W) x := fun ⟨y, hy⟩ ↦ hno ⟨y, Or.inl hy⟩
  have hnoH : ¬HasOutgoing A.closedEdges x :=
    fun ⟨y, hy⟩ ↦ hno ⟨y, Or.inr ⟨hy, hnoW⟩⟩
  rcases A.attachedCarrier_subset hx with hxW | hxRow
  · have hxT : x ∈ (web C).terminalFrontier W := by
      rw [isWarp_terminalFrontier_eq_noOutgoing hW]
      exact ⟨hxW, hnoW⟩
    rcases hterm hxT with hxPop | hxFront
    · exact hxPop
    · have hxI : x ∈ Gamma.initialSet T.interval.ambientInterval :=
        T.interval.ambientInterval_linkage.initialSet_eq.symm ▸ hxFront
      obtain ⟨p, hp, hpx⟩ := hxI
      exact A.sink_isPopular hclosed
        ⟨⟨p, hp, hpx.symm ▸ p.initial_mem_support⟩, hWX hxW⟩ hnoH
  · exact A.sink_isPopular hclosed hxRow hnoH

theorem attached_ray_marked (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof C.newSlice)
    (hmarked : (web C).InfinitelyManyMarkedEdges W (marked C))
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet)
    (r : Ray (web C).graph) (hr : r.edgeSet ⊆ A.attachedEdges W) :
    {n : Nat | marked C (r n) (r (n + 1))}.Infinite := by
  by_cases hold : ∀ n : Nat, (r n, r (n + 1)) ∈ familyEdges W
  · apply hW.markedIndices_infinite_of_edgeSet_subset hmarked r
    rintro e ⟨n, rfl⟩
    exact hold n
  · push Not at hold
    obtain ⟨m, hm⟩ := hold
    have hmfresh : (r m, r (m + 1)) ∈ A.closedEdges := by
      rcases hr ⟨m, rfl⟩ with h | h
      · exact False.elim (hm h)
      · exact h.1
    have htail : ∀ n : Nat,
        (r.tail m n, r.tail m (n + 1)) ∈ A.closedEdges := by
      intro n
      induction n with
      | zero => simpa only [Ray.tail_apply, Nat.add_zero] using hmfresh
      | succ n ih =>
          have hn : (r.tail m (n + 1), r.tail m (n + 1 + 1)) ∈ A.attachedEdges W := by
            simpa only [Ray.tail_apply, Nat.add_assoc] using hr ⟨m + (n + 1), rfl⟩
          rcases hn with hn | hn
          · exact False.elim (A.closedEdge_head_not_roof ih
              (hroof (familyEdges_subset_vertexSet_prod _ hn).1))
          · exact hn.1
    have htailE : (r.tail m).edgeSet ⊆ A.closedEdges := by
      rintro e ⟨n, rfl⟩
      exact htail n
    have hmarks := A.markedIndices_infinite hclosed (r.tail m) htailE
    apply (r.tail m).markedIndices_infinite_of_cofinite_edges (marked C) r hmarks Set.finite_empty
    rintro e ⟨⟨n, rfl⟩, _⟩
    exact ⟨m + n, by simp only [Ray.tail_apply, Nat.add_assoc]⟩

/-- The same source-covered attachment is an actual stable later-stage
endpoint blueprint. It still ends the scheduled real front at the frontier. -/
theorem exists_sourceCoveredBlueprint {W : Set (web C).DPath}
    (hW : IsBlueprint C C.newStage W)
    (hWseed : (web C).vertexSet W ⊆ seed)
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet)
    (hz : z ∈ (web C).terminalFrontier W) :
    let K := seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet
    ∃ U : Set (web C).DPath, IsBlueprint C R.later.stage U ∧
      familyEdges U = RootReachableRelation.edges (A.attachedEdges K) ((web C).initialSet K) ∧
      (web C).vertexSet U =
        RootReachableRelation.carrier (A.attachedEdges K) ((web C).initialSet K) ∧
      (web C).initialSet U = (web C).initialSet K ∧
      (web C).vertexSet W ⊆ (web C).vertexSet U ∧
      familyEdges W ⊆ familyEdges U ∧
      (web C).initialSet W ⊆ (web C).initialSet U ∧
      (web C).vertexSet U ⊆ R.closedSet ∧
      (web C).terminalFrontier U ⊆ popular C ∧
      (web C).terminalFrontier U ∩ C.ladder.frontier R.later.stage ⊆ C.persistent ∧
      T.interval.front.support ⊆ (web C).vertexSet U ∧
      T.interval.front.edgeSet ⊆ familyEdges U ∧
      T.interval.front.finish ∈ (web C).terminalFrontier U ∧
      RealReach Gamma (web C) U z T.interval.front.finish ∧
      (∀ {x y}, y ∈ (web C).vertexSet W → (x, y) ∈ familyEdges U →
        (x, y) ∈ familyEdges W) := by
  dsimp only
  let K := seedFamily C.ladder C.newStage (real_adj (C := C)) W R.closedSet
  have hKW : (web C).IsWarp K := seedFamily_isWarp _ C.legal hW.isWarp
  have hKR : (web C).vertexSet K ⊆ Gamma.roof C.newSlice := by
    rw [seedFamily_vertices]
    exact Set.union_subset hW.vertices_roofed (vertices_roofed C.legal)
  have hKX : (web C).vertexSet K ⊆ R.closedSet := by
    rw [seedFamily_vertices]
    exact Set.union_subset (hWseed.trans R.seed_subset)
      (vertices_subset_closed C.legal R.reference_closed)
  have hKT : (web C).terminalFrontier K ⊆ popular C ∪ C.newSlice := by
    rw [seedFamily_terminals]
    exact Set.union_subset hW.terminals_popular
      ((terminals_subset C.legal).trans Set.subset_union_right)
  have hKM : (web C).InfinitelyManyMarkedEdges K (marked C) :=
    seedFamily_marked _ hW.infinitely_many_marked
  obtain ⟨U, hU, hE, hV, hI, hT, hkeepV, hkeepE, hkeepI, hUX, hsource,
      hpV, hpE, hpT, hpReach, hfresh⟩ := A.exists_sourceCoveredAttachment hW hWseed hclosed hz
  have hPop : (web C).terminalFrontier U ⊆ popular C := by
    intro x hx
    rw [hT] at hx
    exact A.attached_sink_popular hKW hKX hKT hclosed (hV ▸ hx.1) hx.2
  have hUM : (web C).InfinitelyManyMarkedEdges U (marked C) := by
    intro r hr
    apply A.attached_ray_marked hKW hKR hKM hclosed r
    intro e he
    have heU : e ∈ familyEdges U := Set.mem_iUnion.mpr ⟨.inr r,
      Set.mem_iUnion.mpr ⟨hr, he⟩⟩
    rw [hE] at heU
    exact heU.1
  have hBlue : IsBlueprint C R.later.stage U :=
    of_roofed_fields hU (hUX.trans R.later.subset_roof) hsource
      ((Cardinal.mk_subtype_mono hUX).trans R.card_le) hUM
      (hPop.trans Set.subset_union_left)
  refine ⟨U, hBlue, hE, hV, hI, hkeepV, hkeepE, hkeepI, hUX, hPop, ?_,
    hpV, hpE, hpT, hpReach, hfresh⟩
  rintro x ⟨hx, hxF⟩
  have hxU : x ∈ (web C).vertexSet U := by
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hp, (web C).terminal_mem_support hpx⟩
  exact (R.frontier_inter ▸ (show x ∈ R.closedSet ∩ C.ladder.frontier R.later.stage from
    ⟨hUX hxU, hxF⟩)).2

#print axioms attached_sink_popular
#print axioms attached_ray_marked
#print axioms exists_sourceCoveredBlueprint

end EndpointReferenceAssignment
end Erdos599.Blueprint.LinkageBlueprint.NativePostClosureIntervalTransaction

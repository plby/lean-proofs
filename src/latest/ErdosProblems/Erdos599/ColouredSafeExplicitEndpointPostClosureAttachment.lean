/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointBlueprint
import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureEndpointClassification
import ErdosProblems.Erdos599.HalfwayOldStageSourceDiamond
import ErdosProblems.Erdos599.RootReachableWarp

/-!
# Rooted old-priority attachment of the actual endpoint-classified interval

The closed relation comes from the unchanged simultaneous assignment over the
native moving closure. Every fresh head is outside the current roof. Filtering
fresh edges at old outgoing tails therefore gives a biunique relation retaining
the old warp. Its rooted part has an exact actual warp realization.

The result is not yet called a blueprint: activated-reference source coverage,
the terminal ledger and the target suffix are separate obligations.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.StagePostClosureIntervalTransaction

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open ColouredSafeEndpointBlueprint ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Stage (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}
variable {T : StagePostClosureIntervalTransaction C alpha seed z R}
variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}

theorem intervalEdge_head_not_roof {x y : V}
    (he : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    y ∉ Gamma.roof (C.ladder.frontier alpha) := by
  intro hy
  have hyV := (familyEdges_subset_vertexSet_prod _ he).2
  have hyFront : y ∈ (C.ladder.frontier alpha) := by
    rw [← T.interval.ambientInterval_vertexSet_inter_oldRoof]
    exact ⟨hyV, hy⟩
  have hyI : y ∈ Gamma.initialSet T.interval.ambientInterval :=
    T.interval.ambientInterval_linkage.initialSet_eq.symm ▸ hyFront
  exact isWarp_noIncoming_familyEdges_of_mem_initialSet
    T.interval.ambientInterval_linkage.isWarp hyI ⟨x, he⟩

namespace EndpointReferenceAssignment

variable (A : StagePostClosureIntervalTransaction.EndpointReferenceAssignment T F)

theorem closedEdges_subset_insideCarrier : A.closedEdges ⊆
    sourceInsideCarrier T.interval.ambientInterval R.closedSet ×ˢ
      sourceInsideCarrier T.interval.ambientInterval R.closedSet := by
  intro e he
  have hX := A.closedEdges_subset_closed he
  rcases he with he | he
  · have hV := familyEdges_subset_vertexSet_prod _ he.1
    exact ⟨⟨hV.1, hX.1⟩, hV.2, hX.2⟩
  · obtain ⟨s, hs, hsource⟩ := he
    obtain ⟨v, hsv⟩ := A.toClassified.source_hasOutgoing_outside s
    obtain ⟨u, hue⟩ := A.toClassified.finiteEdge_head_hasIncoming_outside ⟨s, hs, hsource⟩
    have htail : e.1 ∈ Gamma.vertexSet T.interval.ambientInterval := by
      rw [← hsource]
      exact (familyEdges_subset_vertexSet_prod _ hsv.1).1
    exact ⟨⟨htail, hX.1⟩,
      (familyEdges_subset_vertexSet_prod _ hue.1).2, hX.2⟩

theorem closedEdge_head_not_roof {x y : V} (he : (x, y) ∈ A.closedEdges) :
    y ∉ Gamma.roof (C.ladder.frontier alpha) := by
  rcases he with he | he
  · exact intervalEdge_head_not_roof he.1
  · obtain ⟨v, hvy⟩ := A.toClassified.finiteEdge_head_hasIncoming_outside he
    exact intervalEdge_head_not_roof hvy.1

theorem noOutgoing_closedEdges_of_row_terminal {x : V}
    (hx : x ∈ Gamma.terminalFrontier T.interval.ambientInterval) :
    ¬HasOutgoing A.closedEdges x := by
  have hno := isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
    T.interval.ambientInterval_linkage.isWarp hx
  rintro ⟨y, he | he⟩
  · exact hno ⟨y, he.1⟩
  · obtain ⟨s, _hs, hsource⟩ := he
    obtain ⟨v, hsv⟩ := A.toClassified.source_hasOutgoing_outside s
    have he : (x, v) ∈ familyEdges T.interval.ambientInterval := by
      change s.1 = x at hsource
      rw [← hsource]
      exact hsv.1
    exact hno ⟨v, he⟩

def attachedEdges (W : Set (web C).DPath) : Set (V × V) :=
  familyEdges W ∪ {e | e ∈ A.closedEdges ∧ ¬HasOutgoing (familyEdges W) e.1}

variable {W : Set (web C).DPath}

theorem attachedEdges_biUnique (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha)) :
    Relator.BiUnique fun x y ↦ (x, y) ∈ A.attachedEdges W := by
  have ho := IsWarp.familyEdges_biUnique hW
  have hf := A.closedEdges_biUnique
  have hcross {x v y : V} (hxy : (x, y) ∈ familyEdges W)
      (hvy : (v, y) ∈ A.closedEdges) : False :=
    A.closedEdge_head_not_roof hvy
      (hroof (familyEdges_subset_vertexSet_prod _ hxy).2)
  constructor
  · intro x v y hxy hvy
    rcases hxy with hxy | hxy <;> rcases hvy with hvy | hvy
    · exact ho.1 hxy hvy
    · exact False.elim (hcross hxy hvy.1)
    · exact False.elim (hcross hvy hxy.1)
    · exact hf.1 hxy.1 hvy.1
  · intro x y v hxy hxv
    rcases hxy with hxy | hxy <;> rcases hxv with hxv | hxv
    · exact ho.2 hxy hxv
    · exact False.elim (hxv.2 ⟨y, hxy⟩)
    · exact False.elim (hxy.2 ⟨v, hxv⟩)
    · exact hf.2 hxy.1 hxv.1

theorem attachedEdge_into_old
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha))
    {x y : V} (hy : y ∈ (web C).vertexSet W)
    (he : (x, y) ∈ A.attachedEdges W) : (x, y) ∈ familyEdges W := by
  rcases he with he | he
  · exact he
  · exact False.elim (A.closedEdge_head_not_roof he.1 (hroof hy))

theorem old_initial_noIncoming_attached (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha))
    {x : V} (hx : x ∈ (web C).initialSet W) :
    ¬HasIncoming (A.attachedEdges W) x := by
  have hxV : x ∈ (web C).vertexSet W := by
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hp, hpx.symm ▸ p.initial_mem_support⟩
  rintro ⟨y, hyx⟩
  exact isWarp_noIncoming_familyEdges_of_mem_initialSet hW hx
    ⟨y, A.attachedEdge_into_old hroof hxV hyx⟩

theorem attachedEdges_subset_graph
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet) :
    A.attachedEdges W ⊆ {e | (web C).graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact familyEdges_subset_adj W he
  · exact A.closedEdge_original_or_imaginary hclosed he.1

/-- Construct the actual rooted attachment, retaining old carrier, edges,
initials and all predecessor incidences. Source coverage is not assumed. -/
theorem exists_attachedWarp (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha))
    (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet) :
    ∃ U : Set (web C).DPath, (web C).IsWarp U ∧
      familyEdges U = RootReachableRelation.edges (A.attachedEdges W) ((web C).initialSet W) ∧
      (web C).vertexSet U =
        RootReachableRelation.carrier (A.attachedEdges W) ((web C).initialSet W) ∧
      (web C).initialSet U = (web C).initialSet W ∧
      (web C).terminalFrontier U =
        {x | x ∈ (web C).vertexSet U ∧ ¬HasOutgoing (A.attachedEdges W) x} ∧
      (web C).vertexSet W ⊆ (web C).vertexSet U ∧
      familyEdges W ⊆ familyEdges U ∧
      (web C).vertexSet U ⊆ (web C).vertexSet W ∪
        sourceInsideCarrier T.interval.ambientInterval R.closedSet ∧
      (∀ {x y}, y ∈ (web C).vertexSet W → (x, y) ∈ familyEdges U →
        (x, y) ∈ familyEdges W) := by
  obtain ⟨U, hU, hE, hV, hI, hT, hkeepV, hkeepE, _hkeepI⟩ :=
    RootReachableRelation.exists_warp_extending (web C) (A.attachedEdges W)
      ((web C).initialSet W) W (A.attachedEdges_subset_graph hclosed)
      (A.attachedEdges_biUnique hW hroof)
      (fun _ hx ↦ A.old_initial_noIncoming_attached hW hroof hx)
      Set.subset_union_left Set.Subset.rfl
  refine ⟨U, hU, hE, hV, hI, ?_, hkeepV, hkeepE, ?_, ?_⟩
  · simpa only [hV, HasOutgoing] using hT
  · rw [hV]
    apply RootReachableRelation.carrier_subset
    · rintro x ⟨p, hp, hpx⟩
      exact Or.inl ⟨p, hp, hpx.symm ▸ p.initial_mem_support⟩
    · intro e he
      rcases he with he | he
      · have hv := familyEdges_subset_vertexSet_prod W he
        exact ⟨Or.inl hv.1, Or.inl hv.2⟩
      · have hv := A.closedEdges_subset_insideCarrier he.1
        exact ⟨Or.inr hv.1, Or.inr hv.2⟩
  · intro x y hy he
    rw [hE] at he
    exact A.attachedEdge_into_old hroof hy he.1

theorem safe_path_mem : (Sum.inl T.interval.path : Gamma.DPath) ∈ T.safe.ambientFamily := by
  have h := T.interval.path_mem_safe
  rw [T.interval_safe_eq] at h
  exact h

theorem front_support_subset_closed : T.interval.front.support ⊆ R.closedSet := by
  intro x hx
  exact T.safe_vertices_closed
    ⟨.inl T.interval.path, safe_path_mem, T.interval.front_support_subset_path hx⟩

theorem front_edgeSet_subset_closedEdges : T.interval.front.edgeSet ⊆ A.closedEdges := by
  intro e he
  exact Or.inl ⟨Set.mem_iUnion.mpr ⟨.inl T.interval.front,
    Set.mem_iUnion.mpr ⟨T.interval.front_mem_interval, he⟩⟩,
    front_support_subset_closed (T.interval.front.edgeSet_subset_support_prod he).1,
    front_support_subset_closed (T.interval.front.edgeSet_subset_support_prod he).2⟩

theorem front_no_oldOutgoing (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha))
    (hz : z ∈ (web C).terminalFrontier W) {x : V}
    (hx : x ∈ T.interval.front.support) : ¬HasOutgoing (familyEdges W) x := by
  by_cases hxz : x = z
  · subst x
    exact isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier hW hz
  · have hxstart : x ≠ T.interval.front.start := by rwa [T.interval.front_start]
    obtain ⟨v, hvx⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start T.interval.front hx hxstart
    have hrow : (v, x) ∈ familyEdges T.interval.ambientInterval :=
      Set.mem_iUnion.mpr ⟨.inl T.interval.front,
        Set.mem_iUnion.mpr ⟨T.interval.front_mem_interval, hvx⟩⟩
    rintro ⟨y, hxy⟩
    exact intervalEdge_head_not_roof hrow
      (hroof (familyEdges_subset_vertexSet_prod _ hxy).1)

theorem front_edgeSet_subset_attached (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha))
    (hz : z ∈ (web C).terminalFrontier W) :
    T.interval.front.edgeSet ⊆ A.attachedEdges W := by
  intro e he
  exact Or.inr ⟨A.front_edgeSet_subset_closedEdges he,
    front_no_oldOutgoing hW hroof hz (T.interval.front.edgeSet_subset_support_prod he).1⟩

theorem front_finish_noOutgoing_attached (hW : (web C).IsWarp W)
    (hroof : (web C).vertexSet W ⊆ Gamma.roof (C.ladder.frontier alpha))
    (hz : z ∈ (web C).terminalFrontier W) :
    ¬HasOutgoing (A.attachedEdges W) T.interval.front.finish := by
  rintro ⟨y, he | he⟩
  · exact front_no_oldOutgoing hW hroof hz T.interval.front.finish_mem_support ⟨y, he⟩
  · exact A.noOutgoing_closedEdges_of_row_terminal
      ⟨.inl T.interval.front, T.interval.front_mem_interval, rfl⟩ ⟨y, he.1⟩

#print axioms closedEdge_head_not_roof
#print axioms exists_attachedWarp
#print axioms front_edgeSet_subset_attached
#print axioms front_finish_noOutgoing_attached

end EndpointReferenceAssignment

end Erdos599.Blueprint.LinkageBlueprint.StagePostClosureIntervalTransaction

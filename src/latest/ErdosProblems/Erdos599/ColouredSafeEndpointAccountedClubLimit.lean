/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointSourceLimit
import ErdosProblems.Erdos599.AugmentedAccountedChainBoundary
import ErdosProblems.Erdos599.HalfwayClubRangeSup
import ErdosProblems.Erdos599.HalfwayIndexedLadderBoundary

/-!
# Stable accounted proper limits in the actual endpoint graph

The exact relation-limit warp has all endpoint-blueprint fields at the
bounded club supremum, on the same union carrier and with the actual marks.
Every old stage retains its accounting and predecessor invariants. This is
a limit producer from a supplied history, not a construction of that history.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach
open LinkageBlueprint.IndexedTerminalResolutionState.ReachableResolutionRecursor.ResolutionChain

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {I : Type v} [LinearOrder I] {index : I → Stage (succ kappa)}

theorem mk_vertexUnion_le (R : AugmentedAccountedChain Gamma (web C) I)
    (hindex : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    (hstage : ∀ i, IsBlueprint C (index i) (R.stage i)) : #R.vertexUnion ≤ kappa := by
  have hbound : Cardinal.lift.{v} #R.vertexUnion ≤ Cardinal.lift.{v} kappa := by
    refine (Cardinal.mk_iUnion_le_lift (fun i ↦ (web C).vertexSet (R.stage i))).trans ?_
    exact Cardinal.mul_le_of_le (Cardinal.aleph0_le_lift.mpr C.capacity_infinite) hindex
      (ciSup_le' fun i ↦ Cardinal.lift_le.mpr (hstage i).card_vertices)
  exact Cardinal.lift_le.mp hbound

theorem target_inter_vertexUnion_subset_persistent
    (R : AugmentedAccountedChain Gamma (web C) I)
    (hstage : ∀ i, IsBlueprint C (index i) (R.stage i)) :
    Gamma.target ∩ R.vertexUnion ⊆ C.persistent := by
  rintro x ⟨hxB, hxV⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxV
  refine ⟨Set.mem_iUnion.mpr ⟨index i, (hstage i).vertices_roofed hxi⟩, ?_⟩
  intro hxStrict
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxStrict
  exact target_not_mem_strictRoof hxB hxa

theorem eventualWarp_terminals_popular
    (R : AugmentedAccountedChain Gamma (web C) I)
    (hstage : ∀ i, IsBlueprint C (index i) (R.stage i))
    (hstable : ∀ i, (web C).terminalFrontier (R.stage i) ∩
      C.ladder.frontier (index i) ⊆ C.persistent)
    {U : Set (web C).DPath} (hU : (web C).IsWarp U)
    (hUV : (web C).vertexSet U = R.vertexUnion) (hUE : familyEdges U = R.eventualEdges) :
    (web C).terminalFrontier U ⊆ popular C := by
  intro x hx
  have hxV : x ∈ R.vertexUnion := hUV ▸ terminalFrontier_subset_vertexSet U hx
  have hsink := hx
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU, hUE]
    at hsink
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxV
  rcases R.eventual_sink_mem_target_or_stage_terminal hsink.2 i hxi with hxB | hxT
  · exact Or.inl (target_inter_vertexUnion_subset_persistent R hstage ⟨hxB, hxV⟩)
  · rcases (hstage i).terminals_popular hxT with hpop | hfrontier
    · exact hpop
    · exact Or.inl (hstable i ⟨hxT, hfrontier⟩)

/-- All proper-limit invariants hold in the unchanged endpoint augmentation.
The index type may lie in a different universe from the vertices. -/
theorem exists_stableAccountedLimit_at_clubSup [Nonempty I]
    (index : I → Stage (succ kappa)) (hmono : Monotone index)
    (hclub : ∀ i, index i ∈ C.club)
    (R : AugmentedAccountedChain Gamma (web C) I)
    (hindex : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa)
    (hstage : ∀ i, IsBlueprint C (index i) (R.stage i))
    (hstable : ∀ i, (web C).terminalFrontier (R.stage i) ∩
      C.ladder.frontier (index i) ⊆ C.persistent)
    {Z : Set V} (hcontained : ∀ i, (web C).vertexSet (R.stage i) ⊆ Z) :
    ∃ a ∈ C.club, IsLUB (Set.range index) a ∧
      ∃ U : Set (web C).DPath, IsBlueprint C a U ∧
        ((web C).terminalFrontier U ∩ C.ladder.frontier a ⊆ C.persistent) ∧
        (web C).vertexSet U = R.vertexUnion ∧ familyEdges U = R.eventualEdges ∧
        (web C).vertexSet U ⊆ Z ∧ (web C).terminalFrontier U ⊆ popular C ∧
        ∀ i, (web C).vertexSet (R.stage i) ⊆ (web C).vertexSet U ∧
          RealEdges (Gamma := web C) Gamma.graph.Adj (R.stage i) ⊆
            RealEdges (Gamma := web C) Gamma.graph.Adj U ∧
          (web C).initialSet (R.stage i) ⊆ (web C).initialSet U ∧
          SourcePredecessorRefines Gamma (web C) (R.stage i) U ∧
          FullAccount Gamma (web C) (R.stage i) U Gamma.target := by
  obtain ⟨D⟩ := HalfwayClubRangeSup.exists_data C.capacity_infinite hindex
    C.club_isClub index hmono hclub
  obtain ⟨U, hU, hUV, hUE⟩ := R.exists_eventualWarp
  have hcover : CoversSource C U (C.ladder.frontier D.supIndex) :=
    coversSource_at_lub index hmono D.range_isLUB hclub
      (coversSource_of_exact_eventualWarp R hstage hU hUV hUE)
  have hroof : (web C).vertexSet U ⊆ Gamma.roof (C.ladder.frontier D.supIndex) := by
    rw [hUV]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rcases (D.previous_le i).lt_or_eq with hlt | heq
    · exact Gamma.roof_cut (C.legal.frontierChronology hlt) ((hstage i).vertices_roofed hi)
    · exact heq ▸ (hstage i).vertices_roofed hi
  have hUZ : (web C).vertexSet U ⊆ Z := by
    rw [hUV]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hcontained i hi
  have hUcard : #((web C).vertexSet U) ≤ kappa := by
    rw [hUV]
    exact mk_vertexUnion_le R hindex hstage
  have hmarked := R.eventualWarp_infinitelyManyMarked
    (ray_not_mem_target (C := C)) (fun i ↦ (hstage i).infinitely_many_marked) hUE
  have hpop := eventualWarp_terminals_popular R hstage hstable hU hUV hUE
  have hBlueprint : IsBlueprint C D.supIndex U :=
    of_roofed_fields hU hroof hcover hUcard hmarked (hpop.trans Set.subset_union_left)
  refine ⟨D.supIndex, D.supIndex_mem, D.range_isLUB, U, hBlueprint, ?_,
    hUV, hUE, hUZ, hpop, ?_⟩
  · rintro x ⟨hxT, hxa⟩
    have hxV : x ∈ R.vertexUnion := hUV ▸ terminalFrontier_subset_vertexSet U hxT
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxV
    have hno := hxT
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU, hUE]
      at hno
    rcases R.eventual_sink_mem_target_or_stage_terminal hno.2 i hxi with hxB | hxOld
    · exact target_inter_vertexUnion_subset_persistent R hstage ⟨hxB, hxV⟩
    · exact hstable i ⟨hxOld, oldRoof_inter_laterFrontier_subset C.legal
        (D.previous_le i) ⟨(hstage i).vertices_roofed hxi, hxa⟩⟩
  · intro i
    refine ⟨?_, ?_, R.initials_subset_of_exact_eventualWarp hU hUV hUE i,
      R.sourcePredecessorRefines_eventualWarp hUV hUE i,
      R.fullAccount_eventualWarp hU hUV hUE i⟩
    · rw [hUV]
      exact R.stage_vertices_subset i
    · intro e he
      exact ⟨hUE.symm ▸ R.stage_realEdges_subset i he, he.2⟩

#print axioms mk_vertexUnion_le
#print axioms target_inter_vertexUnion_subset_persistent
#print axioms eventualWarp_terminals_popular
#print axioms exists_stableAccountedLimit_at_clubSup

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint

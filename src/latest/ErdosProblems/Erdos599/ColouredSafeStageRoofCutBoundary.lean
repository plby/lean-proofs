/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutRelation
import ErdosProblems.Erdos599.ColouredSafeReferenceTransport
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Boundary accounting for a fixed-stage roof cut

The global safe occurrence may leave and re-enter the selected stage roof.
After its carrier is chosen disjoint from the inessential stage carrier,
however, every limiting-reference incidence at a retained occurrence point
belongs to the finite touched essential reference.  This file records that
incidence completeness and the resulting one-sided balance comparison.

No simultaneous or global coverage statement is assumed here.  The final
theorems retain the old reference roots and the occurrence source, and show
that a realized component can acquire a new terminal only at the cutting
frontier or at the finite occurrence endpoint.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open Alternating.SwitchingCore
open Alternating.SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}} {L : Gamma.KappaLadder kappa}
variable {a : Stage kappa} {s : V}

namespace ColouredSafeStageRoofCutBoundary

open ColouredSafeStageRoofCutRelation

local notation "Y" =>
  stageTouchedReference (L := L) (a := a) (s := s)

private theorem occurrence_backwardEdges_subset
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    A.backwardEdges ⊆ familyEdges L.limitWarp := by
  cases A with
  | infinite Q => exact Q.backwardEdges_subset_familyEdges
  | finite t Q => exact Q.backwardEdges_subset_familyEdges

private theorem occurrence_forward_endpoints
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {e : V × V} (he : e ∈ A.forwardEdges) :
    e.1 ∈ A.vertexSet ∧ e.2 ∈ A.vertexSet := by
  cases A with
  | infinite Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
  | finite t Q => exact Q.forwardEdges_endpoints_mem_vertexSet he

private theorem occurrence_backward_endpoints
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {e : V × V} (he : e ∈ A.backwardEdges) :
    e.1 ∈ A.vertexSet ∧ e.2 ∈ A.vertexSet := by
  cases A with
  | infinite Q => exact Q.backwardEdges_endpoints_mem_vertexSet he
  | finite t Q => exact Q.backwardEdges_endpoints_mem_vertexSet he

private theorem exists_outgoing_familyEdge_of_mem_not_terminal
    {W : Set Gamma.DPath} {x : V} (hx : x ∈ Gamma.vertexSet W)
    (hterminal : x ∉ Gamma.terminalFrontier W) :
    ∃ y, (x, y) ∈ familyEdges W := by
  obtain ⟨p, hpW, hxp⟩ := hx
  have hpterminal : Gamma.terminal? p ≠ some x := by
    intro hp
    exact hterminal ⟨p, hpW, hp⟩
  rcases p with p | r
  · have hxfinish : x ≠ p.finish := by
      intro hx
      apply hpterminal
      simp [hx]
    obtain ⟨y, hxy⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        p hxp hxfinish
    exact ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
      Set.mem_iUnion.2 ⟨hpW, hxy⟩⟩⟩
  · obtain ⟨n, rfl⟩ := hxp
    refine ⟨r (n + 1), Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hpW, ?_⟩⟩⟩
    exact ⟨n, rfl⟩

/-- A stage-reference edge incident with the occurrence belongs to the
finite touched essential reference, once inessential stage carriers were
excluded at the fixed stage. -/
theorem stageEdge_mem_touchedReference_of_endpoint
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {e : V × V} (he : e ∈ familyEdges (L.warpAt a))
    (hend : e.1 ∈ A.vertexSet ∨ e.2 ∈ A.vertexSet) :
    e ∈ familyEdges (Y A) := by
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  have hsupport : e.1 ∈ p.support ∧ e.2 ∈ p.support :=
    p.edgeSet_subset_support_prod hep
  have hpEssential : p ∈ Gamma.essentialWarpPart (L.warpAt a) := by
    by_contra hpnot
    have hpBad : p ∈ Gamma.inessentialPaths (L.warpAt a) :=
      Gamma.mem_inessentialPaths.2 ⟨hp, hpnot⟩
    rcases hend with hend | hend
    · exact Set.disjoint_left.1 havoid hend ⟨p, hpBad, hsupport.1⟩
    · exact Set.disjoint_left.1 havoid hend ⟨p, hpBad, hsupport.2⟩
  refine ⟨p, ⟨?_, ?_⟩, hep⟩
  · simpa only [LinkageBlueprint.ladderReference] using hpEssential
  · rcases hend with hend | hend
    · exact ⟨e.1, hsupport.1, hend⟩
    · exact ⟨e.2, hsupport.2, hend⟩

/-- At a roofed occurrence point, every incoming erased limiting-reference
edge is present in the cropped erased relation. -/
theorem incoming_backwardEdges_iff
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {x y : V} (hxA : x ∈ A.vertexSet)
    (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    (y, x) ∈ backwardEdges A (Y A) ↔ (y, x) ∈ A.backwardEdges := by
  constructor
  · exact fun h ↦ h.1
  · intro hyx
    refine ⟨hyx, stageEdge_mem_touchedReference_of_endpoint A havoid ?_
      (Or.inr hxA)⟩
    apply ColouredSafeReferenceTransport.incoming_referenceEdge_reflect hL
      (occurrence_backwardEdges_subset A hyx) hxRoof

/-- At a strictly roofed occurrence point, every outgoing erased
limiting-reference edge is present in the cropped erased relation.  The
strictness rules out a terminal of the essential stage owner. -/
theorem outgoing_backwardEdges_iff
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {x y : V} (hxA : x ∈ A.vertexSet)
    (hxStrict : x ∈ Gamma.strictRoof (L.frontier a)) :
    (x, y) ∈ backwardEdges A (Y A) ↔ (x, y) ∈ A.backwardEdges := by
  constructor
  · exact fun h ↦ h.1
  · intro hxy
    have hxyLimit : (x, y) ∈ familyEdges L.limitWarp :=
      occurrence_backwardEdges_subset A hxy
    have hxLimit : x ∈ Gamma.vertexSet L.limitWarp :=
      (familyEdges_subset_vertexSet_prod L.limitWarp hxyLimit).1
    have hxCases :=
      DWeb.KappaLadder.Deferred.vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
        hL a ⟨hxLimit, hxStrict.1⟩
    have hxEssential : x ∈
        Gamma.vertexSet (Gamma.essentialWarpPart (L.warpAt a)) := by
      rcases hxCases with hxEssential | hxBad
      · exact hxEssential
      · exact (Set.disjoint_left.1 havoid hxA hxBad).elim
    obtain ⟨p, hpEssential, hxp⟩ := hxEssential
    have hxNotTerminal : x ∉ Gamma.terminalFrontier (L.warpAt a) := by
      rintro ⟨q, hq, hqx⟩
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support
          (hL.warpStages (Stage.toExtended a)) hpEssential.1 hq
        · exact hxp
        · exact Gamma.terminal_mem_support hqx
      subst q
      obtain ⟨t, hpt, htEssential⟩ := hpEssential.2
      have htx : t = x := Option.some.inj (hpt.symm.trans hqx)
      have htFrontier : t ∈ L.frontier a := by
        rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages]
        exact htEssential
      apply hxStrict.2
      rw [L.frontiersAreEssential_of_roofsSourceAtStages
        hL.roofsSourceAtStages a]
      exact htx ▸ htFrontier
    obtain ⟨z, hxzStage⟩ :=
      exists_outgoing_familyEdge_of_mem_not_terminal
        ⟨p, hpEssential.1, hxp⟩ hxNotTerminal
    have hxzLimit :=
      (hL.stageReferenceEmbedding a).familyEdges_subset hxzStage
    have hzy : z = y :=
      (IsWarp.familyEdges_biUnique
        (hL.warpStages (Ladder.finalStage kappa))).2 hxzLimit hxyLimit
    refine ⟨hxy, stageEdge_mem_touchedReference_of_endpoint A havoid ?_
      (Or.inl hxA)⟩
    simpa only [hzy] using hxzStage

/-- Cropping at a strict roof point preserves every outgoing inserted
incidence and can only discard incoming inserted incidences. -/
theorem edgeBalance_forwardEdges_le
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (T : Set V) {x : V} (hx : x ∈ Gamma.strictRoof T) :
    edgeBalance A.forwardEdges x ≤ edgeBalance (forwardEdges A T) x := by
  have hout : HasOutgoing (forwardEdges A T) x ↔
      HasOutgoing A.forwardEdges x := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.1⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy, hx⟩
  have hin : HasIncoming (forwardEdges A T) x →
      HasIncoming A.forwardEdges x := by
    rintro ⟨y, hy⟩
    exact ⟨y, hy.1⟩
  classical
  simp only [edgeBalance]
  by_cases hgo : HasOutgoing A.forwardEdges x <;>
    by_cases hgi : HasIncoming A.forwardEdges x <;>
      by_cases hli : HasIncoming (forwardEdges A T) x <;>
        simp [propInt, hout, hgo, hgi, hli] at *

/-- Under fixed-stage inessential-carrier avoidance, the cropped erased
relation has exactly the global erased balance at every strict-roof
occurrence point. -/
theorem edgeBalance_backwardEdges_eq
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {x : V} (hxA : x ∈ A.vertexSet)
    (hxStrict : x ∈ Gamma.strictRoof (L.frontier a)) :
    edgeBalance (backwardEdges A (Y A)) x =
      edgeBalance A.backwardEdges x := by
  classical
  simp only [edgeBalance]
  congr 2
  · apply propext
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, (outgoing_backwardEdges_iff hL A havoid hxA hxStrict).1 hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (outgoing_backwardEdges_iff hL A havoid hxA hxStrict).2 hy⟩
  · apply propext
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, (incoming_backwardEdges_iff hL A havoid hxA hxStrict.1).1 hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (incoming_backwardEdges_iff hL A havoid hxA hxStrict.1).2 hy⟩

/-- Away from the literal occurrence carrier the cropped relation has
exactly the old touched-reference incidence. -/
theorem edgeBalance_edges_eq_reference_of_not_mem_occurrence
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (T : Set V) {x : V} (hx : x ∉ A.vertexSet) :
    edgeBalance (edges A (Y A) T) x =
      edgeBalance (familyEdges (Y A)) x := by
  have hout : HasOutgoing (edges A (Y A) T) x ↔
      HasOutgoing (familyEdges (Y A)) x := by
    constructor
    · rintro ⟨y, hy⟩
      rcases hy with hy | hy
      · exact ⟨y, hy.1⟩
      · exact (hx (occurrence_forward_endpoints A hy.1).1).elim
    · rintro ⟨y, hy⟩
      refine ⟨y, Or.inl ⟨hy, ?_⟩⟩
      rintro ⟨hback, _⟩
      exact hx (occurrence_backward_endpoints A hback).1
  have hin : HasIncoming (edges A (Y A) T) x ↔
      HasIncoming (familyEdges (Y A)) x := by
    constructor
    · rintro ⟨y, hy⟩
      rcases hy with hy | hy
      · exact ⟨y, hy.1⟩
      · exact (hx (occurrence_forward_endpoints A hy.1).2).elim
    · rintro ⟨y, hy⟩
      refine ⟨y, Or.inl ⟨hy, ?_⟩⟩
      rintro ⟨hback, _⟩
      exact hx (occurrence_backward_endpoints A hback).2
  simp only [edgeBalance]
  rw [show HasOutgoing (edges A (Y A) T) x =
      HasOutgoing (familyEdges (Y A)) x from propext hout,
    show HasIncoming (edges A (Y A) T) x =
      HasIncoming (familyEdges (Y A)) x from propext hin]

/-- Exact incidence accounting for the literal roof-cut relation. -/
theorem edgeBalance_edges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (T : Set V) (x : V) :
    edgeBalance (edges A (Y A) T) x =
      edgeBalance (familyEdges (Y A)) x +
        edgeBalance (forwardEdges A T) x -
          edgeBalance (backwardEdges A (Y A)) x := by
  obtain ⟨W, hW, _hWfinite, hforward⟩ := hA
  exact edgeBalance_eq_of_incidence hW
    (stageTouchedReference_isWarp hL A)
    (backwardEdges_subset A (Y A))
    ((forwardEdges_subset A T).trans hforward)
    (incoming_removed hL A (Y A) (fun p hp ↦ hp.1.1) T)
    (outgoing_removed hL A (Y A) (fun p hp ↦ hp.1.1) T) x

/-- At a strict-roof occurrence point, localization can only increase the
signed balance: all outgoing inserted incidences and all erased reference
incidences remain, while an incoming inserted incidence may have been cut
away at the roof boundary. -/
theorem stageEndpoint_balance_lower
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {x : V} (hxA : x ∈ A.vertexSet)
    (hxStrict : x ∈ Gamma.strictRoof (L.frontier a)) :
    edgeBalance (familyEdges (Y A)) x + propInt (x = s) -
        terminalDefect A x ≤
      edgeBalance (edges A (Y A) (L.frontier a)) x := by
  rw [edgeBalance_edges hL A hA (L.frontier a) x,
    edgeBalance_backwardEdges_eq hL A havoid hxA hxStrict]
  have hforward := edgeBalance_forwardEdges_le A (L.frontier a) hxStrict
  have hglobal := edgeBalance_forward_sub_backward A hA
    (hL.warpStages (Ladder.finalStage kappa)) x
  omega

private theorem terminalDefect_zero_or_one
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) (x : V) :
    terminalDefect A x = 0 ∨ terminalDefect A x = 1 := by
  cases A with
  | infinite Q => simp [terminalDefect, CurrentSafeOccurrence.terminal?]
  | finite t Q =>
      by_cases hxt : x = t
      · simp [terminalDefect, CurrentSafeOccurrence.terminal?, propInt, hxt]
      · simp [terminalDefect, CurrentSafeOccurrence.terminal?, propInt, hxt]

theorem terminalDefect_eq_one_iff
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) (x : V) :
    terminalDefect A x = 1 ↔ A.terminal? = some x := by
  cases A with
  | infinite Q => simp [terminalDefect, CurrentSafeOccurrence.terminal?]
  | finite t Q =>
      simp [terminalDefect, CurrentSafeOccurrence.terminal?, propInt,
        eq_comm]

private theorem terminalDefect_eq_zero_of_ne_terminal
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) (x : V)
    (hne : ∀ t, A.terminal? = some t → x ≠ t) :
    terminalDefect A x = 0 := by
  cases A with
  | infinite Q => simp [terminalDefect, CurrentSafeOccurrence.terminal?]
  | finite t Q hQ hfirst hlast =>
      have hxt : x ≠ t := hne t rfl
      simp [terminalDefect, CurrentSafeOccurrence.terminal?, propInt, hxt]

private theorem edgeBalance_le_one (E : Set (V × V)) (x : V) :
    edgeBalance E x ≤ 1 := by
  classical
  simp only [edgeBalance]
  by_cases hout : HasOutgoing E x <;>
    by_cases hin : HasIncoming E x <;>
      simp [propInt, hout, hin]

private theorem reference_balance_nonnegative_off_frontier
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {x : V} (hx : x ∉ L.frontier a) :
    0 ≤ edgeBalance (familyEdges (Y A)) x := by
  have hxTerminal : x ∉ Gamma.terminalFrontier (Y A) :=
    fun h ↦ hx (stageTouchedReference_terminal_subset hL A h)
  have hnot : edgeBalance (familyEdges (Y A)) x ≠ -1 := by
    intro hneg
    apply hxTerminal
    exact (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      (stageTouchedReference_isWarp hL A)
      (stageTouchedReference_finiteCharacter A)).2 (Or.inr hneg)
  classical
  simp only [edgeBalance] at hnot ⊢
  by_cases hout : HasOutgoing (familyEdges (Y A)) x <;>
    by_cases hin : HasIncoming (familyEdges (Y A)) x <;>
      simp [propInt, hout, hin] at hnot ⊢

private theorem endpoint_mem_occurrence_of_new_terminal
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (hUE : familyEdges U = edges A (Y A) (L.frontier a))
    (hcarrier : Gamma.vertexSet U ⊆ Gamma.vertexSet (Y A) ∪ A.vertexSet)
    {x : V} (hxU : x ∈ Gamma.vertexSet U)
    (hxSink : ¬ HasOutgoing (familyEdges U) x)
    (hxFrontier : x ∉ L.frontier a) : x ∈ A.vertexSet := by
  rcases hcarrier hxU with hxY | hxA
  · by_contra hxnotA
    have hxYTerminal : x ∈ Gamma.terminalFrontier (Y A) := by
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (stageTouchedReference_isWarp hL A)]
      refine ⟨hxY, ?_⟩
      rintro ⟨y, hxy⟩
      apply hxSink
      refine ⟨y, hUE.symm ▸ Or.inl ⟨hxy, ?_⟩⟩
      rintro ⟨hback, _hlocal⟩
      apply hxnotA
      cases A with
      | infinite Q => exact (Q.backwardEdges_endpoints_mem_vertexSet hback).1
      | finite t Q => exact (Q.backwardEdges_endpoints_mem_vertexSet hback).1
    exact (hxFrontier (stageTouchedReference_terminal_subset hL A
      hxYTerminal)).elim
  · exact hxA

/-- A realized roof-cut component has no new terminal away from the stage
frontier except the finite endpoint of the original occurrence.  The
statement uses `terminalDefect = 1`, so it applies uniformly to finite and
infinite occurrences. -/
theorem terminalFrontier_subset_frontier_or_terminalDefect
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (hUfinite : Gamma.HasFiniteCharacter U)
    (hUE : familyEdges U = edges A (Y A) (L.frontier a))
    (hUI : isolatedVertices U = isolatedVertices (Y A))
    (hUroof : Gamma.vertexSet U ⊆ Gamma.roof (L.frontier a))
    (hcarrier : Gamma.vertexSet U ⊆ Gamma.vertexSet (Y A) ∪ A.vertexSet) :
    Gamma.terminalFrontier U ⊆
      L.frontier a ∪ {x | terminalDefect A x = 1} := by
  intro x hxTerminal
  by_cases hxFrontier : x ∈ L.frontier a
  · exact Or.inl hxFrontier
  · right
    have hxU : x ∈ Gamma.vertexSet U := by
      obtain ⟨p, hpU, hpx⟩ := hxTerminal
      exact ⟨p, hpU, Gamma.terminal_mem_support hpx⟩
    rcases (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hU hUfinite).1 hxTerminal with hxIsolated | hxBalance
    · have hxYTerminal : x ∈ Gamma.terminalFrontier (Y A) := by
        have hxIsoY : x ∈ isolatedVertices (Y A) := by
          rw [← hUI]
          exact hxIsolated
        exact ⟨Gamma.trivialPath x, hxIsoY, by simp⟩
      exact (hxFrontier (stageTouchedReference_terminal_subset hL A
        hxYTerminal)).elim
    · have hxSink : ¬ HasOutgoing (familyEdges U) x :=
        (edgeBalance_eq_neg_one_iff.mp hxBalance).2
      have hxA := endpoint_mem_occurrence_of_new_terminal hL A hU hUE
        hcarrier hxU hxSink hxFrontier
      have hxStrict : x ∈ Gamma.strictRoof (L.frontier a) := by
        refine ⟨hUroof hxU, ?_⟩
        intro hxEssential
        exact hxFrontier (Gamma.essential_subset (L.frontier a) hxEssential)
      have hlower := stageEndpoint_balance_lower hL A hA havoid hxA hxStrict
      have hreference := reference_balance_nonnegative_off_frontier hL A hxFrontier
      rcases terminalDefect_zero_or_one A x with hzero | hone
      · have hxBalanceE :
            edgeBalance (edges A (Y A) (L.frontier a)) x = -1 := by
          rw [← hUE]
          exact hxBalance
        rw [hzero, hxBalanceE] at hlower
        have hsource : 0 ≤ propInt (x = s) := by
          classical
          simp only [propInt]
          split <;> omega
        omega
      · exact hone

theorem terminalFrontier_subset_frontier_or_endpoint
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (hUfinite : Gamma.HasFiniteCharacter U)
    (hUE : familyEdges U = edges A (Y A) (L.frontier a))
    (hUI : isolatedVertices U = isolatedVertices (Y A))
    (hUroof : Gamma.vertexSet U ⊆ Gamma.roof (L.frontier a))
    (hcarrier : Gamma.vertexSet U ⊆ Gamma.vertexSet (Y A) ∪ A.vertexSet) :
    Gamma.terminalFrontier U ⊆
      L.frontier a ∪ {x | A.terminal? = some x} := by
  intro x hx
  rcases terminalFrontier_subset_frontier_or_terminalDefect hL A hA havoid
      hU hUfinite hUE hUI hUroof hcarrier hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr ((terminalDefect_eq_one_iff A x).1 hx)

/-- Every original initial of the touched essential stage reference remains
an initial of the realized roof-cut warp.  The finite endpoint is required
to lie outside the touched reference; this is the exact endpoint condition
supplied by the ambient occurrence selection. -/
theorem touchedReference_initialSet_subset
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    (hterminalOff : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet (Y A))
    {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (hUfinite : Gamma.HasFiniteCharacter U)
    (hUE : familyEdges U = edges A (Y A) (L.frontier a))
    (hUI : isolatedVertices U = isolatedVertices (Y A)) :
    Gamma.initialSet (Y A) ⊆ Gamma.initialSet U := by
  intro x hxInitial
  have hxY : x ∈ Gamma.vertexSet (Y A) := by
    obtain ⟨p, hp, hpx⟩ := hxInitial
    exact ⟨p, hp, hpx ▸ p.initial_mem_support⟩
  rcases (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
      (stageTouchedReference_isWarp hL A)
      (stageTouchedReference_finiteCharacter A)).1 hxInitial with
      hxIsolated | hxBalance
  · apply (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
      hU hUfinite).2
    left
    rw [hUI]
    exact hxIsolated
  · by_cases hxA : x ∈ A.vertexSet
    · have hxNotFrontier : x ∉ L.frontier a := by
        intro hxFrontier
        have hxFullTerminal : x ∈ Gamma.terminalFrontier
            (LinkageBlueprint.ladderReference L a) := by
          rw [LinkageBlueprint.ladderReference.terminalFrontier_eq hL]
          exact hxFrontier
        obtain ⟨p, hpY, hpxInitial⟩ := hxInitial
        obtain ⟨q, hqFull, hqxTerminal⟩ := hxFullTerminal
        have hpq : p = q := by
          apply DWeb.IsWarp.eq_of_mem_support
            (LinkageBlueprint.ladderReference.isWarp hL) hpY.1 hqFull
          · simpa only [hpxInitial] using p.initial_mem_support
          · exact Gamma.terminal_mem_support hqxTerminal
        subst q
        have hxYTerminal : x ∈ Gamma.terminalFrontier (Y A) :=
          ⟨p, hpY, hqxTerminal⟩
        rcases (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
            (stageTouchedReference_isWarp hL A)
            (stageTouchedReference_finiteCharacter A)).1 hxYTerminal with
            hxIso | hxNeg
        · exact (not_hasOutgoing_of_mem_isolatedVertices
            (stageTouchedReference_isWarp hL A) hxIso)
            (edgeBalance_eq_one_iff.mp hxBalance).1
        · omega
      have hxStrict : x ∈ Gamma.strictRoof (L.frontier a) := by
        refine ⟨stageTouchedReference_vertexSet_subset_roof hL A hxY, ?_⟩
        intro hxEssential
        exact hxNotFrontier
          (Gamma.essential_subset (L.frontier a) hxEssential)
      have hdefect : terminalDefect A x = 0 := by
        apply terminalDefect_eq_zero_of_ne_terminal A x
        intro t ht hxt
        apply hterminalOff t ht
        rwa [← hxt]
      have hlower := stageEndpoint_balance_lower hL A hA havoid hxA hxStrict
      rw [hxBalance, hdefect] at hlower
      have hupper := edgeBalance_le_one
        (edges A (Y A) (L.frontier a)) x
      have hbalanceE : edgeBalance (edges A (Y A) (L.frontier a)) x = 1 := by
        have hsource : 0 ≤ propInt (x = s) := by
          classical
          simp only [propInt]
          split <;> omega
        omega
      apply (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
        hU hUfinite).2
      right
      rw [hUE]
      exact hbalanceE
    · apply (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
        hU hUfinite).2
      right
      rw [hUE, edgeBalance_edges_eq_reference_of_not_mem_occurrence A
        (L.frontier a) hxA]
      exact hxBalance

/-- The exposed occurrence source remains an initial after the roof cut.
Its strict-roof position and separation from the touched reference are kept
explicit; no uniform roof confinement of the whole occurrence is used. -/
theorem occurrenceSource_mem_initialSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    (hsStrict : s ∈ Gamma.strictRoof (L.frontier a))
    (hsOff : s ∉ Gamma.vertexSet (Y A))
    (hsTerminal : ∀ t, A.terminal? = some t → s ≠ t)
    {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (hUfinite : Gamma.HasFiniteCharacter U)
    (hUE : familyEdges U = edges A (Y A) (L.frontier a)) :
    s ∈ Gamma.initialSet U := by
  have hsA : s ∈ A.vertexSet := A.source_mem_vertexSet
  have hdefect : terminalDefect A s = 0 :=
    terminalDefect_eq_zero_of_ne_terminal A s hsTerminal
  have hreference : edgeBalance (familyEdges (Y A)) s = 0 := by
    have hout : ¬ HasOutgoing (familyEdges (Y A)) s := by
      rintro ⟨y, hsy⟩
      exact hsOff (familyEdges_subset_vertexSet_prod (Y A) hsy).1
    have hin : ¬ HasIncoming (familyEdges (Y A)) s := by
      rintro ⟨y, hys⟩
      exact hsOff (familyEdges_subset_vertexSet_prod (Y A) hys).2
    simp [edgeBalance, propInt, hout, hin]
  have hlower := stageEndpoint_balance_lower hL A hA havoid hsA hsStrict
  rw [hreference, hdefect] at hlower
  have hsource : propInt (s = s) = 1 := by simp [propInt]
  rw [hsource] at hlower
  have hupper := edgeBalance_le_one
    (edges A (Y A) (L.frontier a)) s
  have hbalanceE : edgeBalance (edges A (Y A) (L.frontier a)) s = 1 := by
    omega
  apply (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
    hU hUfinite).2
  right
  rw [hUE]
  exact hbalanceE

/-- Keep exactly the realized components rooted at one of the prescribed
old initials or at the exposed occurrence source. -/
def rootedPruning (U : Set Gamma.DPath) (I : Set V) : Set Gamma.DPath :=
  {p | p ∈ U ∧ p.initial ∈ I}

theorem rootedPruning_isWarp {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (I : Set V) : Gamma.IsWarp (rootedPruning U I) := by
  intro p hp q hq hpq
  exact hU hp.1 hq.1 hpq

theorem rootedPruning_finiteCharacter {U : Set Gamma.DPath}
    (hU : Gamma.HasFiniteCharacter U) (I : Set V) :
    Gamma.HasFiniteCharacter (rootedPruning U I) := fun hp ↦ hU hp.1

theorem rootedPruning_vertexSet_subset (U : Set Gamma.DPath) (I : Set V) :
    Gamma.vertexSet (rootedPruning U I) ⊆ Gamma.vertexSet U := by
  rintro x ⟨p, hp, hxp⟩
  exact ⟨p, hp.1, hxp⟩

theorem rootedPruning_familyEdges_subset (U : Set Gamma.DPath) (I : Set V) :
    familyEdges (rootedPruning U I) ⊆ familyEdges U := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, hp.1, hep⟩

theorem rootedPruning_terminalFrontier_subset (U : Set Gamma.DPath)
    (I : Set V) :
    Gamma.terminalFrontier (rootedPruning U I) ⊆
      Gamma.terminalFrontier U := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp.1, hpx⟩

theorem rootedPruning_initialSet_eq {U : Set Gamma.DPath} {I : Set V}
    (hI : I ⊆ Gamma.initialSet U) :
    Gamma.initialSet (rootedPruning U I) = I := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    exact hpx ▸ hp.2
  · intro hxI
    obtain ⟨p, hpU, hpx⟩ := hI hxI
    refine ⟨p, ⟨hpU, ?_⟩, hpx⟩
    exact hpx.symm ▸ hxI

/-- Complete fixed-stage output: realize the roof-cut relation, retain all
old touched-reference initials and the exposed source, and discard every
component with a reentry initial.  The pruned warp stays countable and in
the stage roof.  Its only possible terminals are stage-frontier points and
the finite occurrence endpoint.  The carrier-union bound is retained for
the subsequent source-coverage bridge. -/
theorem exists_pruned_stageRoofCut
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (havoid : Disjoint A.vertexSet
      (Gamma.vertexSet (Gamma.inessentialPaths (L.warpAt a))))
    (hterminalOff : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet (Y A))
    (hsStrict : s ∈ Gamma.strictRoof (L.frontier a))
    (hsOff : s ∉ Gamma.vertexSet (Y A))
    (hsTerminal : ∀ t, A.terminal? = some t → s ≠ t) :
    ∃ P : Set Gamma.DPath,
      Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      Gamma.initialSet P = Gamma.initialSet (Y A) ∪ {s} ∧
      Gamma.terminalFrontier P ⊆
        L.frontier a ∪ {x | terminalDefect A x = 1} ∧
      Gamma.vertexSet P ⊆ Gamma.roof (L.frontier a) ∧
      Gamma.vertexSet P ⊆ Gamma.vertexSet (Y A) ∪ A.vertexSet ∧
      (Gamma.vertexSet P).Countable ∧
      familyEdges P ⊆ edges A (Y A) (L.frontier a) := by
  let I : Set V := Gamma.initialSet (Y A) ∪ {s}
  obtain ⟨U, hU, hUfinite, hUE, hUI, hUroof, hUcarrier⟩ :=
    exists_finiteWarp_roofed hL A hA (Y A)
      (stageTouchedReference_isWarp hL A)
      (stageTouchedReference_finiteCharacter A)
      (fun p hp ↦ hp.1.1) (L.frontier a)
      (L.frontiersAreEssential_of_roofsSourceAtStages
        hL.roofsSourceAtStages a)
      (stageTouchedReference_terminal_subset hL A)
      (stageTouchedReference_vertexSet_subset_roof hL A)
  have hOld := touchedReference_initialSet_subset hL A hA havoid
    hterminalOff hU hUfinite hUE hUI
  have hSource := occurrenceSource_mem_initialSet hL A hA havoid
    hsStrict hsOff hsTerminal hU hUfinite hUE
  have hI : I ⊆ Gamma.initialSet U := by
    rintro x (hx | hx)
    · exact hOld hx
    · simpa only [Set.mem_singleton_iff] using hx ▸ hSource
  have hUTerminal := terminalFrontier_subset_frontier_or_terminalDefect
    hL A hA havoid hU hUfinite hUE hUI hUroof hUcarrier
  let P := rootedPruning U I
  refine ⟨P, rootedPruning_isWarp hU I,
    rootedPruning_finiteCharacter hUfinite I, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rootedPruning_initialSet_eq hI
  · exact (rootedPruning_terminalFrontier_subset U I).trans hUTerminal
  · exact (rootedPruning_vertexSet_subset U I).trans hUroof
  · exact (rootedPruning_vertexSet_subset U I).trans hUcarrier
  · exact ((vertexSet_stageTouchedReference_countable hL A).union
      A.vertexSet_countable).mono
      ((rootedPruning_vertexSet_subset U I).trans hUcarrier)
  · exact (rootedPruning_familyEdges_subset U I).trans (by
      rw [hUE])

#print axioms terminalFrontier_subset_frontier_or_endpoint
#print axioms exists_pruned_stageRoofCut

end ColouredSafeStageRoofCutBoundary

end Erdos599

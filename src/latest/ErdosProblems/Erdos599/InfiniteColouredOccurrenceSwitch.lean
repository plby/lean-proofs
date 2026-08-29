/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.InfiniteColouredOccurrenceBalance
import ErdosProblems.Erdos599.SafeSwitchingRelationalBalance

/-!
# Finite-character realization of an infinite coloured switch

An interval-safe omega word has one unit of excess outgoing balance at its
first vertex and no terminal deficit.  The relational interval realization
therefore gives a finite-character warp with exactly one added initial and
no added terminal.  No existence or scheduling hypothesis for the prefix
chain is used here.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

private theorem edgeBalance_zero_of_not_mem_vertexSet_oneSided
    {Y : Set Gamma.DPath} {x : V} (hx : x ∉ Gamma.vertexSet Y) :
    edgeBalance (familyEdges Y) x = 0 := by
  have hout : ¬HasOutgoing (familyEdges Y) x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y hy).1
  have hin : ¬HasIncoming (familyEdges Y) x := by
    rintro ⟨y, hy⟩
    exact hx (familyEdges_subset_vertexSet_prod Y hy).2
  simp [edgeBalance, propInt, hout, hin]

/-- A finite-character warp realization with one positive balance defect has
exactly one new initial and no new terminal. -/
theorem boundary_eq_of_one_initial_balance
    {Y U : Set Gamma.DPath} (hY : Gamma.IsWarp Y) (hU : Gamma.IsWarp U)
    (hYfin : Gamma.HasFiniteCharacter Y) (hUfin : Gamma.HasFiniteCharacter U)
    (hiso : isolatedVertices U = isolatedVertices Y)
    {s : V} (hs : s ∉ Gamma.vertexSet Y)
    (hbal : ∀ x, edgeBalance (familyEdges U) x =
      edgeBalance (familyEdges Y) x + propInt (x = s)) :
    Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y := by
  have hsbal := edgeBalance_zero_of_not_mem_vertexSet_oneSided hs
  have hsiso : s ∉ isolatedVertices Y :=
    fun h ↦ hs (isolatedVertices_subset_vertexSet Y h)
  constructor
  · ext x
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hU hUfin,
      Set.mem_union, Set.mem_singleton_iff,
      mem_initialSet_iff_isolated_or_edgeBalance_eq_one hY hYfin,
      hiso, hbal]
    by_cases hxs : x = s
    · subst x
      simp [hsbal, hsiso, propInt]
    · simp [propInt, hxs]
  · ext x
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one hU hUfin,
      mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one hY hYfin,
      hiso, hbal]
    by_cases hxs : x = s
    · subst x
      simp [hsbal, hsiso, propInt]
    · simp [propInt, hxs]

#print axioms boundary_eq_of_one_initial_balance

end Erdos599.Alternating.SwitchingCore.RelationalInterval

namespace Erdos599.Alternating.FiniteColouredOccurrencePrefixChain

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Realize the exact infinite interval switch as a finite-character warp.
The output has the reference isolated vertices and terminal frontier, and
adds precisely the first occurrence as an initial. -/
theorem exists_finiteWarp_realizing_limitSwitch
    (C : FiniteColouredOccurrencePrefixChain W Y)
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsafe : C.limit.IsIntervalSafe)
    (hstart : C.limit.vertex 0 ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U =
        (familyEdges Y \ C.limit.backwardEdges) ∪ C.limit.forwardEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {C.limit.vertex 0} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y := by
  let E := (familyEdges Y \ C.limit.backwardEdges) ∪ C.limit.forwardEdges
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) :=
    biUnique_of_incident_reference_edges_removed hW hY
      C.limit.forwardEdges_subset_familyEdges
      hsafe.incoming_removed hsafe.outgoing_removed
  have hiso : ∀ x ∈ isolatedVertices Y, ∀ y,
      (x, y) ∉ E ∧ (y, x) ∉ E := by
    intro x hx y
    have hxInitial : x ∈ Gamma.initialSet Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    have hxTerminal : x ∈ Gamma.terminalFrontier Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    constructor
    · rintro (he | he)
      · exact not_isolated_of_hasOutgoing hY ⟨y, he.1⟩ hx
      · exact (hsafe.endpoint_pure he).2 hxTerminal
    · rintro (he | he)
      · exact not_isolated_of_hasIncoming hY ⟨y, he.1⟩ hx
      · exact (hsafe.endpoint_pure he).1 hxInitial
  obtain ⟨U, hU, hUE, hUI, hUfin⟩ :=
    exists_finiteWarp_realizing_incidence_intervalSwitch hW hY hWfin hYfin
      C.limit.forwardEdges_subset_familyEdges
      hsafe.incoming_removed hsafe.outgoing_removed rfl hbi
      hsafe.intervals hsafe.endpoint_pure (isolatedVertices Y) hiso
  have hbalance : ∀ x, edgeBalance (familyEdges U) x =
      edgeBalance (familyEdges Y) x + propInt (x = C.limit.vertex 0) := by
    intro x
    rw [hUE, edgeBalance_eq_of_incidence hW hY
      C.limit.backwardEdges_subset_familyEdges
      C.limit.forwardEdges_subset_familyEdges
      hsafe.incoming_removed hsafe.outgoing_removed]
    have hd := C.limit_edgeBalance_forward_sub_backward hW hY x
    omega
  have hboundary := boundary_eq_of_one_initial_balance hY hU hYfin hUfin
    hUI hstart hbalance
  exact ⟨U, hU, hUfin, hUE, hUI, hboundary⟩

/-- Stagewise interval safety is sufficient for the same realization. -/
theorem exists_finiteWarp_realizing_limitSwitch_of_stageSafe
    (C : FiniteColouredOccurrencePrefixChain W Y)
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsafe : ∀ n, (C.stage n).IsIntervalSafe)
    (hstart : C.limit.vertex 0 ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U =
        (familyEdges Y \ C.limit.backwardEdges) ∪ C.limit.forwardEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {C.limit.vertex 0} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y :=
  C.exists_finiteWarp_realizing_limitSwitch hW hWfin hY hYfin
    (C.limit_isIntervalSafe hYfin hsafe) hstart

#print axioms exists_finiteWarp_realizing_limitSwitch
#print axioms exists_finiteWarp_realizing_limitSwitch_of_stageSafe

end Erdos599.Alternating.FiniteColouredOccurrencePrefixChain

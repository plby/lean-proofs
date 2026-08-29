/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceRoofCutBoundary

/-!
# Actual finite ports for an arbitrary reference roof cut

An exposed finite occurrence endpoint has no outgoing switched incidence,
even when the reference has infinite members. A rooted finite realization
therefore has a terminal port there whenever that vertex is present. Its
source component ends at the cutting frontier or the original finite end.
-/

noncomputable section

namespace Erdos599.ColouredSafeReferenceRoofCut

open Set DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {G : Set Gamma.DPath} {s t : V}

theorem not_hasOutgoing_switchedEdges_at_terminal
    (hG : Gamma.IsWarp G) (A : Occurrence G s) (hA : Valid A)
    (hend : A.terminal? = some t) (hne : s ≠ t) (ht : t ∉ Gamma.vertexSet G) :
    ¬HasOutgoing A.switchedEdges t := by
  have hback : A.backwardEdges ⊆ familyEdges G := by
    cases A with
    | infinite Q => exact Q.backwardEdges_subset_familyEdges
    | finite t Q => exact Q.backwardEdges_subset_familyEdges
  have hRout : ¬HasOutgoing A.backwardEdges t :=
    fun ⟨y, hy⟩ ↦ ht (familyEdges_subset_vertexSet_prod G (hback hy)).1
  have hRin : ¬HasIncoming A.backwardEdges t :=
    fun ⟨y, hy⟩ ↦ ht (familyEdges_subset_vertexSet_prod G (hback hy)).2
  have hbalance := edgeBalance_forward_sub_backward hG A hA t
  have hFout : ¬HasOutgoing A.forwardEdges t := by
    intro hout
    by_cases hin : HasIncoming A.forwardEdges t
    all_goals simp [edgeBalance, propInt, hRout, hRin, hout, hin,
      terminalDefect, hend, Ne.symm hne] at hbalance
  rintro ⟨y, hy | hy⟩
  · exact ht (familyEdges_subset_vertexSet_prod G hy.1).1
  · exact hFout ⟨y, hy⟩

theorem mem_terminalFrontier_of_mem_carrier_at_terminal
    (hG : Gamma.IsWarp G) (A : Occurrence G s) (hA : Valid A)
    (hend : A.terminal? = some t) (hne : s ≠ t) (ht : t ∉ Gamma.vertexSet G)
    {K : Set Gamma.DPath} (hK : Gamma.IsWarp K)
    (hKE : familyEdges K ⊆ A.switchedEdges) (htK : t ∈ Gamma.vertexSet K) :
    t ∈ Gamma.terminalFrontier K := by
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hK]
  exact ⟨htK, fun ⟨y, hy⟩ ↦
    not_hasOutgoing_switchedEdges_at_terminal hG A hA hend hne ht ⟨y, hKE hy⟩⟩

theorem exists_finite_sourcePort (A : Occurrence G s)
    {K : Set Gamma.DPath} (hKfinite : Gamma.HasFiniteCharacter K)
    (hsource : s ∈ Gamma.initialSet K) {T : Set V}
    (hterminal : Gamma.terminalFrontier K ⊆ T ∪ {t | A.terminal? = some t})
    (hKE : familyEdges K ⊆ A.switchedEdges) (hsT : s ∉ T)
    (hsTerminal : ∀ t, A.terminal? = some t → s ≠ t) :
    ∃ p : FinitePath Gamma.graph, (Sum.inl p : Gamma.DPath) ∈ K ∧
      p.start = s ∧ (p.finish ∈ T ∨ A.terminal? = some p.finish) ∧
      p.start ≠ p.finish ∧ p.edgeSet ⊆ A.switchedEdges ∧
      (∀ t, A.terminal? = some t → ¬A.HasFiniteSwitchedPathTo t → p.finish ≠ t) := by
  obtain ⟨p0, hp0, hp0s⟩ := hsource
  obtain ⟨p, rfl⟩ := hKfinite hp0
  have hps : p.start = s := hp0s
  have hpEnd := hterminal ⟨Sum.inl p, hp0, rfl⟩
  have hpE : p.edgeSet ⊆ A.switchedEdges := by
    intro edge he
    exact hKE (Set.mem_iUnion.mpr ⟨.inl p, Set.mem_iUnion.mpr ⟨hp0, he⟩⟩)
  have hpne : p.start ≠ p.finish := by
    intro hsame
    have hsf : s = p.finish := hps.symm.trans hsame
    rcases hpEnd with hpT | hpEnd
    · exact hsT (hsf ▸ hpT)
    · exact hsTerminal p.finish hpEnd hsf
  refine ⟨p, hp0, hps, hpEnd, hpne, hpE, ?_⟩
  intro t _ht hnondeg hpt
  exact hnondeg ⟨p, hps, hpt, hpE⟩

#print axioms not_hasOutgoing_switchedEdges_at_terminal
#print axioms mem_terminalFrontier_of_mem_carrier_at_terminal
#print axioms exists_finite_sourcePort

end Erdos599.ColouredSafeReferenceRoofCut

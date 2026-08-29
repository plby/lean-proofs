/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRoofCutSourceCoverage

/-!
# Extracting actual ports once roof-cut boundary accounting is available

A finite-character rooted roof-cut warp has a genuine finite source member.
Its endpoint is on the frontier in the infinite or nondegenerate branch.
At a finite exposed occurrence end there is no outgoing switched edge;
thus that vertex is either absent from the rooted warp or is its terminal.
These lemmas do not assert existence of the required rooted warp.
-/

noncomputable section

namespace Erdos599.ColouredSafeStageRoofCutRelation

open Set Cardinal Order DirectedPath Alternating Ladder Blueprint
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s t : V}

/-- An exposed finite endpoint cannot have an outgoing switched edge.
This follows from the actual signed occurrence balance, including for
words with repeated contacts. -/
theorem not_hasOutgoing_switchedEdges_at_terminal
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) (hA : Valid A)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (ht : t ∉ Gamma.vertexSet L.limitWarp) :
    ¬HasOutgoing A.switchedEdges t := by
  have hback : A.backwardEdges ⊆ familyEdges L.limitWarp := by
    cases A with
    | infinite Q => exact Q.backwardEdges_subset_familyEdges
    | finite t Q => exact Q.backwardEdges_subset_familyEdges
  have hRout : ¬HasOutgoing A.backwardEdges t := by
    rintro ⟨y, hy⟩
    exact ht (familyEdges_subset_vertexSet_prod L.limitWarp (hback hy)).1
  have hRin : ¬HasIncoming A.backwardEdges t := by
    rintro ⟨y, hy⟩
    exact ht (familyEdges_subset_vertexSet_prod L.limitWarp (hback hy)).2
  have hbal := edgeBalance_forward_sub_backward A hA
    (hL.warpStages (finalStage rho)) t
  have hFout : ¬HasOutgoing A.forwardEdges t := by
    intro hout
    by_cases hin : HasIncoming A.forwardEdges t
    all_goals simp [edgeBalance, propInt, hRout, hRin, hout, hin,
      terminalDefect, hend, Ne.symm hne] at hbal
  rintro ⟨y, hy | hy⟩
  · exact ht (familyEdges_subset_vertexSet_prod L.limitWarp hy.1).1
  · exact hFout ⟨y, hy⟩

/-- Consequently a finite occurrence endpoint which belongs to a realized
subrelation is an actual terminal, not an interior contact. -/
theorem mem_terminalFrontier_of_mem_carrier_at_terminal
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) (hA : Valid A)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (ht : t ∉ Gamma.vertexSet L.limitWarp)
    {K : Set Gamma.DPath} (hK : Gamma.IsWarp K)
    (hKE : familyEdges K ⊆ A.switchedEdges)
    (htK : t ∈ Gamma.vertexSet K) :
    t ∈ Gamma.terminalFrontier K := by
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hK]
  exact ⟨htK, fun ⟨y, hy⟩ ↦
    not_hasOutgoing_switchedEdges_at_terminal hL A hA hend hne ht ⟨y, hKE hy⟩⟩

/-- Once the source and terminal boundary facts are proved, the actual
finite source component ends at the stage frontier in the infinite or
nondegenerate case. It is a nontrivial real path. -/
theorem exists_source_frontierPath_of_nondegenerate
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) (hs : s ∉ Gamma.vertexSet L.limitWarp)
    {K : Set Gamma.DPath} (hKfinite : Gamma.HasFiniteCharacter K)
    (hsource : s ∈ Gamma.initialSet K)
    (hterminal : Gamma.terminalFrontier K ⊆
      L.frontier a ∪ {t | A.terminal? = some t})
    (hKE : familyEdges K ⊆ A.switchedEdges)
    (hnondeg : ∀ t, A.terminal? = some t → ¬A.HasFiniteSwitchedPathTo t) :
    ∃ p : FinitePath Gamma.graph,
      (Sum.inl p : Gamma.DPath) ∈ K ∧ p.start = s ∧
      p.finish ∈ L.frontier a ∧ p.start ≠ p.finish ∧
      p.edgeSet ⊆ A.switchedEdges := by
  obtain ⟨p0, hp0, hp0s⟩ := hsource
  obtain ⟨p, rfl⟩ := hKfinite hp0
  have hps : p.start = s := hp0s
  have hpE : p.edgeSet ⊆ A.switchedEdges := by
    intro e he
    exact hKE (Set.mem_iUnion.mpr ⟨Sum.inl p, Set.mem_iUnion.mpr ⟨hp0, he⟩⟩)
  have hpt : p.finish ∈ L.frontier a := by
    rcases hterminal ⟨Sum.inl p, hp0, rfl⟩ with htFrontier | htEnd
    · exact htFrontier
    · exact False.elim (hnondeg p.finish htEnd ⟨p, hps, rfl, hpE⟩)
  have hne : p.start ≠ p.finish := by
    intro hsame
    have hsFrontier : s ∈ L.frontier a := hps ▸ hsame ▸ hpt
    rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq hL] at hsFrontier
    obtain ⟨q, hq, hqs⟩ := hsFrontier
    let E := hL.stageReferenceEmbedding a
    exact hs ⟨(E.owner ⟨q, hq.1⟩).1, (E.owner ⟨q, hq.1⟩).2,
      E.support_subset ⟨q, hq.1⟩ (Gamma.terminal_mem_support hqs)⟩
  exact ⟨p, hp0, hps, hpt, hne, hpE⟩

/-- If the exposed finite endpoint is present, its actual component starts
at a retained reference initial, not at the distinguished source. -/
theorem exists_terminalPort_of_mem_carrier
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) (hA : Valid A)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (ht : t ∉ Gamma.vertexSet L.limitWarp)
    {K : Set Gamma.DPath} (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hinitial : Gamma.initialSet K =
      Gamma.initialSet (stageTouchedReference (a := a) A) ∪ {s})
    (hKE : familyEdges K ⊆ A.switchedEdges)
    (hnondeg : ¬A.HasFiniteSwitchedPathTo t)
    (htK : t ∈ Gamma.vertexSet K) :
    ∃ q : FinitePath Gamma.graph,
      (Sum.inl q : Gamma.DPath) ∈ K ∧ q.finish = t ∧
      q.start ∈ Gamma.initialSet (stageTouchedReference (a := a) A) := by
  obtain ⟨q0, hq0, hq0t⟩ :=
    mem_terminalFrontier_of_mem_carrier_at_terminal hL A hA hend hne ht hK hKE htK
  obtain ⟨q, rfl⟩ := hKfinite hq0
  have hqt : q.finish = t := Option.some.inj hq0t
  have hqI : q.start ∈ Gamma.initialSet (stageTouchedReference (a := a) A) ∪ {s} :=
    hinitial ▸ (show q.start ∈ Gamma.initialSet K from ⟨Sum.inl q, hq0, rfl⟩)
  refine ⟨q, hq0, hqt, hqI.resolve_right ?_⟩
  intro hqs
  apply hnondeg
  refine ⟨q, hqs, hqt, ?_⟩
  intro e he
  exact hKE (Set.mem_iUnion.mpr ⟨Sum.inl q, Set.mem_iUnion.mpr ⟨hq0, he⟩⟩)

#print axioms not_hasOutgoing_switchedEdges_at_terminal
#print axioms mem_terminalFrontier_of_mem_carrier_at_terminal
#print axioms exists_source_frontierPath_of_nondegenerate
#print axioms exists_terminalPort_of_mem_carrier

end Erdos599.ColouredSafeStageRoofCutRelation

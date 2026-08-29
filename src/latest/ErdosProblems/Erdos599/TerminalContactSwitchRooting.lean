/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinitePerturbationRooting

/-!
# Rooting the unchanged sinks of a terminal-contact switch

A terminal-contact switch is the endpoint configuration used by the
Section 8 decoder when its final forward link enters an old reference
initial.  Its literal switched relation consumes that initial and one old
terminal.  Every other old terminal is still rooted from an unconsumed old
initial.  This statement uses signed boundary and finite-perturbation
rooting directly; it does not impose interval convexity or endpoint purity
on the switching trace.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating
namespace TerminalContactSwitch

open DirectedPath GroundingFinitePerturbationRooting

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Every old terminal other than the terminal removed by a terminal-contact
switch is rooted, in the literal switched relation, from an old initial
other than the initial consumed by the switch. -/
theorem IsTerminalContactSwitching.oldTerminal_rooted
    {Z : Set Gamma.DPath} {Q : FiniteTrace Gamma.graph} {u v t : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v)
    (ht : t ∈ Gamma.terminalFrontier Z \ {v}) :
    ∃ a ∈ Gamma.initialSet Z \ {u},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ switchedEdges Z (.finite Q)) a t := by
  classical
  let E := switchedEdges Z (.finite Q)
  let F := (AltPath.finite Q).directionEdges .forward
  let A := Gamma.initialSet Z \ {u}
  have hvin : HasIncoming (familyEdges Z) v :=
    start_hasIncoming Q hQ hv hQi
  have hvniso : v ∉ isolatedVertices Z :=
    not_isolated_of_hasIncoming hQ.warp hvin
  have hvbal : edgeBalance (familyEdges Z) v = -1 :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
      hQ.warp).1 hv |>.resolve_left hvniso
  have hvu : v ≠ u := by
    intro h
    subst u
    have hu := hQ.terminal_mem_initialSet
    rw [initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hQ.warp] at hu
    exact hu.2 hvin
  have huv : u ≠ v := hvu.symm
  have hbalance : ∀ x,
      edgeBalance E x = edgeBalance (familyEdges Z) x +
        propInt (x = v) - propInt (x = u) := by
    intro x
    change edgeBalance (switchedEdges Z (.finite Q)) x = _
    rw [FiniteTrace.hasTerminalContactBalanceDelta Q hQ, hQi,
      hQ.terminal_eq]
  have hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
    simpa only [E, Cyclowarp.application_edges] using
      (Cyclowarp.application Z (.finite Q)).edges_in_graph
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    exact ⟨
      fun _ _ _ hxz hyz ↦
        FiniteTrace.switchedEdges_in_unique Q hQ hxz hyz,
      fun _ _ _ hxy hxz ↦
        FiniteTrace.switchedEdges_out_unique Q hQ hxy hxz⟩
  have hfinite : F.Finite := by
    have hedgeFinite : (AltPath.finite Q).edgeSet.Finite := by
      simpa only [AltPath.edgeSet, AltPath.links, FiniteTrace.links] using
        Q.edgeSet_finite
    apply hedgeFinite.subset
    rw [(AltPath.finite Q).edgeSet_eq_directionEdges_union]
    exact Set.subset_union_left
  have hsubset : E ⊆ familyEdges Z ∪ F := by
    change switchedEdges Z (.finite Q) ⊆
      familyEdges Z ∪ (AltPath.finite Q).directionEdges .forward
    rw [FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward Q hQ]
    exact Set.union_subset_union (Set.diff_subset) (Set.Subset.rfl)
  have hboundary : ∀ x, edgeBalance E x = 1 → x ∈ A := by
    intro x hx
    by_cases hxv : x = v
    · subst x
      rw [hbalance] at hx
      simp [propInt, hvbal, hvu] at hx
    by_cases hxu : x = u
    · subst x
      rw [hbalance] at hx
      rcases hQ.terminal_outgoing_or_isolated with huout | huisolated
      · have huniso : u ∉ isolatedVertices Z :=
          not_isolated_of_hasOutgoing hQ.warp huout
        have hubal : edgeBalance (familyEdges Z) u = 1 :=
          (mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
            hQ.warp).1 hQ.terminal_mem_initialSet |>.resolve_left huniso
        simp [propInt, hubal, huv] at hx
      · have huNoIn :=
          not_hasIncoming_of_mem_isolatedVertices hQ.warp huisolated
        have huNoOut :=
          not_hasOutgoing_of_mem_isolatedVertices hQ.warp huisolated
        have hubal : edgeBalance (familyEdges Z) u = 0 := by
          simp [edgeBalance, propInt, huNoIn, huNoOut]
        simp [propInt, hubal, huv] at hx
    · have hxbal : edgeBalance (familyEdges Z) x = 1 := by
        rw [hbalance] at hx
        simp [propInt, hxv, hxu] at hx
        exact hx
      exact ⟨
        (mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
          hQ.warp).2 (Or.inr hxbal),
        by simpa using hxu⟩
  have htarget : t ∈ A ∨ HasIncoming E t := by
    rcases (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
      hQ.warp).1 ht.1 with htiso | htbal
    · by_cases htu : t = u
      · right
        subst t
        have huNoIn :=
          not_hasIncoming_of_mem_isolatedVertices hQ.warp htiso
        have huNoOut :=
          not_hasOutgoing_of_mem_isolatedVertices hQ.warp htiso
        have hubal : edgeBalance (familyEdges Z) u = 0 := by
          simp [edgeBalance, propInt, huNoIn, huNoOut]
        have hubalE : edgeBalance E u = -1 := by
          rw [hbalance]
          simp [propInt, hubal, huv]
        exact (edgeBalance_eq_neg_one_iff.mp hubalE).1
      · left
        exact ⟨
          (mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
            hQ.warp).2 (Or.inl htiso),
          by simpa using htu⟩
    · right
      have htu : t ≠ u := by
        intro htu
        subst t
        rcases hQ.terminal_outgoing_or_isolated with huout | huisolated
        · exact (edgeBalance_eq_neg_one_iff.mp htbal).2 huout
        · exact (not_isolated_of_hasIncoming hQ.warp
            (edgeBalance_eq_neg_one_iff.mp htbal).1) huisolated
      have htbalE : edgeBalance E t = -1 := by
        rw [hbalance]
        have htv : t ≠ v := by simpa using ht.2
        simp [propInt, htbal, htv, htu]
      exact (edgeBalance_eq_neg_one_iff.mp htbalE).1
  have hsink : ¬HasOutgoing E t := by
    rcases (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
      hQ.warp).1 ht.1 with htiso | htbal
    · by_cases htu : t = u
      · subst t
        have huNoIn :=
          not_hasIncoming_of_mem_isolatedVertices hQ.warp htiso
        have huNoOut :=
          not_hasOutgoing_of_mem_isolatedVertices hQ.warp htiso
        have hubal : edgeBalance (familyEdges Z) u = 0 := by
          simp [edgeBalance, propInt, huNoIn, huNoOut]
        have hubalE : edgeBalance E u = -1 := by
          rw [hbalance]
          simp [propInt, hubal, huv]
        exact (edgeBalance_eq_neg_one_iff.mp hubalE).2
      · exact (isolated_not_incident_switched Q hQ htiso htu).2
    · have htu : t ≠ u := by
        intro htu
        subst t
        rcases hQ.terminal_outgoing_or_isolated with huout | huisolated
        · exact (edgeBalance_eq_neg_one_iff.mp htbal).2 huout
        · exact (not_isolated_of_hasIncoming hQ.warp
            (edgeBalance_eq_neg_one_iff.mp htbal).1) huisolated
      have htbalE : edgeBalance E t = -1 := by
        rw [hbalance]
        have htv : t ≠ v := by simpa using ht.2
        simp [propInt, htbal, htv, htu]
      exact (edgeBalance_eq_neg_one_iff.mp htbalE).2
  exact sink_rooted_of_finitePerturbation hQ.warp E F A
    hgraph hbi hfinite hsubset hboundary htarget hsink

#print axioms IsTerminalContactSwitching.oldTerminal_rooted

end TerminalContactSwitch
end Alternating
end Erdos599

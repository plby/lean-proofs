/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Initial and terminal ports of a warp

These existing elementary proofs are factored out of the half-way
construction so the all-marker auxiliary can reuse them without importing
the later cardinal-induction machinery. Their names and statements are
unchanged.
-/

namespace Erdos599.Blueprint.LinkageBlueprint

open Set DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {W : Set Gamma.DPath}

/-- An initial vertex of a warp has no incoming edge in the union of its
member edge sets. -/
theorem isWarp_noIncoming_familyEdges_of_mem_initialSet
    (hW : Gamma.IsWarp W) {x : V} (hx : x ∈ Gamma.initialSet W) :
    ¬ ∃ y, (y, x) ∈ familyEdges W := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hpW, rfl⟩ := hx
  simp only [familyEdges, Set.mem_iUnion] at hyx
  obtain ⟨q, hqW, hyxq⟩ := hyx
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hpW hqW p.initial_mem_support
      (q.edgeSet_subset_support_prod hyxq).2
  subst q
  rcases p with p | r
  · exact FinitePath.no_incoming_edge_at_start p y hyxq
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

/-- A finite terminal of a warp has no outgoing edge in the union of its
member edge sets. -/
theorem isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
    (hW : Gamma.IsWarp W) {x : V} (hx : x ∈ Gamma.terminalFrontier W) :
    ¬ ∃ y, (x, y) ∈ familyEdges W := by
  rintro ⟨y, hxy⟩
  obtain ⟨p, hpW, hpterm⟩ := hx
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨q, hqW, hxyq⟩ := hxy
  have hxp : x ∈ p.support := Gamma.terminal_mem_support hpterm
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hpW hqW hxp
      (q.edgeSet_subset_support_prod hxyq).1
  subst q
  rcases p with p | r
  · have hpfinish : p.finish = x := by
      simpa [DWeb.terminal?, Path.terminal?] using hpterm
    exact FinitePath.no_outgoing_edge_at_finish p y (hpfinish ▸ hxyq)
  · simp [DWeb.terminal?, Path.terminal?] at hpterm

end Erdos599.Blueprint.LinkageBlueprint

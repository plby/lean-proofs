/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawPortIncidence
import ErdosProblems.Erdos599.PopularSwitching

/-!
# Raw exits from a reference owner's auxiliary trace

A backward equality join cannot leave one owner's trace. An actual arc
leaving that trace therefore has a genuine selected forward connector,
whose original tail is on the owner and whose head is outside it.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating PopularSwitching

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

theorem referenceEdge_mem_owner_of_tail {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {x y : V}
    (he : (x, y) ∈ L.familyEdges) (hx : x ∈ H.support) :
    (x, y) ∈ H.edgeSet := by
  obtain ⟨P, hP, heP⟩ := he
  have hPH : P = H := DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint hP hH
    (P.edgeSet_subset_support_prod heP).1 hx
  exact hPH ▸ heP

theorem referenceEdge_mem_owner_of_head {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {x y : V}
    (he : (x, y) ∈ L.familyEdges) (hy : y ∈ H.support) :
    (x, y) ∈ H.edgeSet := by
  obtain ⟨P, hP, heP⟩ := he
  have hPH : P = H := DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint hP hH
    (P.edgeSet_subset_support_prod heP).2 hy
  exact hPH ▸ heP

theorem gadgetExit_mem_owner_of_trace {H : Gamma.DPath} {a : L.LV} {x : V}
    (ha : a ∈ ladderTrace L H) (hx : L.gadgetExit a = some x) : x ∈ H.support := by
  cases a with
  | old z =>
      have hzx : z = x := Option.some.inj hx
      exact hzx ▸ (old_mem_ladderTrace_iff L H z).1 ha
  | edge z w =>
      have hzx : z = x := Option.some.inj hx
      exact hzx ▸ (H.edgeSet_subset_support_prod
        ((edge_mem_ladderTrace_iff L H z w).1 ha)).1
  | proxy i => simp at hx

/-- An entered gadget with an original entry on an owner belongs to that
owner's full trace. -/
theorem mem_trace_of_gadgetEntry_mem_owner {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {a b : L.LV} {y : V}
    (hab : L.lambda.graph.Adj a b) (hentry : L.gadgetEntry b = some y)
    (hy : y ∈ H.support) : b ∈ ladderTrace L H := by
  cases b with
  | old z =>
      have hzy : z = y := Option.some.inj hentry
      exact (old_mem_ladderTrace_iff L H z).2 (hzy.symm ▸ hy)
  | edge x z =>
      have hzy : z = y := Option.some.inj hentry
      apply (edge_mem_ladderTrace_iff L H x z).2
      exact L.referenceEdge_mem_owner_of_head hH
        (L.familyEdge_of_adj_to_edge hab) (hzy.symm ▸ hy)
  | proxy i => simp at hentry

variable {L}

/-- Zero-length reversed joins stay on the same reference owner. -/
theorem BackwardJoin.trace_closed {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {a b : L.LV}
    (h : L.BackwardJoin a b) (ha : a ∈ ladderTrace L H) : b ∈ ladderTrace L H := by
  rcases h with h | h | h
  · obtain ⟨x, y, rfl, rfl, _hxy⟩ := h
    apply (old_mem_ladderTrace_iff L H x).2
    exact (H.edgeSet_subset_support_prod ((edge_mem_ladderTrace_iff L H x y).1 ha)).1
  · obtain ⟨x, y, rfl, rfl, hxy⟩ := h
    apply (edge_mem_ladderTrace_iff L H x y).2
    exact L.referenceEdge_mem_owner_of_head hH hxy ((old_mem_ladderTrace_iff L H y).1 ha)
  · obtain ⟨x, y, z, rfl, rfl, _hxy, hzx⟩ := h
    apply (edge_mem_ladderTrace_iff L H z x).2
    exact L.referenceEdge_mem_owner_of_head hH hzx
      (H.edgeSet_subset_support_prod ((edge_mem_ladderTrace_iff L H x y).1 ha)).1

variable (L)

/-- An actual departure from the trace selects a proper forward edge with
one endpoint on the owner and the other strictly outside it. -/
theorem chosenConnector_leaves_owner {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {a b : L.LV}
    (hab : L.lambda.graph.Adj a b) (ha : a ∈ ladderTrace L H)
    (hb : b ∉ ladderTrace L H) :
    ∃ x y, L.chosenConnector? a b = some (x, y) ∧
      L.ForwardConnector a b x y ∧ x ∈ H.support ∧ y ∉ H.support := by
  cases hc : L.chosenConnector? a b with
  | none =>
      exact False.elim (hb ((L.chosenConnector?_eq_none_of_adj hab hc).trace_closed hH ha))
  | some e =>
      have hforward := L.chosenConnector?_eq_some hc
      have hx : e.1 ∈ H.support := by
        rcases hforward.1 with hexit | ⟨i, rfl, _hi⟩
        · exact L.gadgetExit_mem_owner_of_trace ha hexit
        · exact False.elim (proxy_not_mem_ladderTrace L H i ha)
      have hy : e.2 ∉ H.support := fun hy ↦
        hb (L.mem_trace_of_gadgetEntry_mem_owner hH hab hforward.2.1 hy)
      exact ⟨e.1, e.2, rfl, hforward, hx, hy⟩

/-- The first proxy arc selects an actual attachment on its represented
record; if the next gadget avoids that record, the head is outside it. -/
theorem chosenConnector_proxy_to_outside_owner {H : Gamma.DPath}
    (hH : H ∈ L.ladder.paths) {i : I} (hi : H = L.proxyPath i)
    {b : L.LV} (hab : L.lambda.graph.Adj (.proxy i) b)
    (hb : b ∉ ladderTrace L H) :
    ∃ x y, L.chosenConnector? (.proxy i) b = some (x, y) ∧
      L.ForwardConnector (.proxy i) b x y ∧ x ∈ H.support ∧ y ∉ H.support := by
  cases hc : L.chosenConnector? (.proxy i) b with
  | none =>
      have hjoin := L.chosenConnector?_eq_none_of_adj hab hc
      simp [BackwardJoin] at hjoin
  | some e =>
      have hforward := L.chosenConnector?_eq_some hc
      have hx : e.1 ∈ H.support := by
        rw [hi]
        simpa using hforward.1
      have hy : e.2 ∉ H.support := fun hy ↦
        hb (L.mem_trace_of_gadgetEntry_mem_owner hH hab hforward.2.1 hy)
      exact ⟨e.1, e.2, rfl, hforward, hx, hy⟩

/-- A path entered by an auxiliary arc cannot contain any proxy. -/
theorem no_proxy_of_incoming_arc (p : FinitePath L.lambda.graph) {a : L.LV}
    (ha : L.lambda.graph.Adj a p.start) : ∀ i : I, LambdaVertex.proxy i ∉ p.support := by
  intro i hi
  by_cases hstart : p.start = .proxy i
  · exact L.lambda_not_adj_to_proxy a i (hstart ▸ ha)
  · obtain ⟨b, hb⟩ := Alternating.Walk.exists_edge_to_of_mem_of_ne_start
      p.walk hi (fun h ↦ hstart h.symm)
    exact L.lambda_not_adj_to_proxy b i (p.edgeSet_subset_adj hb)

end PopularAuxiliary.Input
end Erdos599

#print axioms Erdos599.PopularAuxiliary.Input.chosenConnector_leaves_owner
#print axioms Erdos599.PopularAuxiliary.Input.chosenConnector_proxy_to_outside_owner

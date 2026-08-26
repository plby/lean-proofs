/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The definitions `IsArm`, `ArmsDisj`, and the indexed-arc proof below are
adapted from `ListColoring.RubinCases` at commit
80a728c86f28222a58b11a777f9d22419fd2fb69 of
https://github.com/rkirov/list-color-function, released under Apache 2.0.
-/
import ErdosProblems.Erdos556.Basic

namespace Erdos556

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem exists_path_arcs_of_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {a b : V} (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b) :
    ∃ (p q : G.Walk a b), p.IsPath ∧ q.IsPath ∧
      1 ≤ p.length ∧ 1 ≤ q.length ∧ p.length + q.length = c.length ∧
      (∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b) ∧
      (∀ x, x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ e, e ∈ p.edges → e ∈ c.edges) ∧
      (∀ e, e ∈ q.edges → e ∈ c.edges) := by
  classical
  let c' : G.Walk a a := c.rotate a ha
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hb' : b ∈ c'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  let p : G.Walk a b := c'.takeUntil b hb'
  let r : G.Walk b a := c'.dropUntil b hb'
  let q : G.Walk a b := r.reverse
  have hdecomp : p.append r = c' := by
    exact c'.take_spec hb'
  have hpPath : p.IsPath := hc'.isPath_takeUntil hb'
  have happCycle : (p.append r).IsCycle := by
    rw [hdecomp]
    exact hc'
  have hrPath : r.IsPath := by
    exact happCycle.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne hab)
  have hqPath : q.IsPath := hrPath.reverse
  have hpPos : 1 ≤ p.length := by
    have : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab)
    omega
  have hqPos : 1 ≤ q.length := by
    have : 0 < r.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
      (SimpleGraph.Walk.not_nil_of_ne hab.symm)
    have : 1 ≤ r.length := by omega
    simpa [q] using this
  have hlen : p.length + q.length = c.length := by
    have := congrArg SimpleGraph.Walk.length hdecomp
    simpa [q, c', SimpleGraph.Walk.length_rotate] using this
  have htailNodup : (p.support.tail ++ r.support.tail).Nodup := by
    rw [← SimpleGraph.Walk.tail_support_append]
    rw [hdecomp]
    exact hc'.support_nodup
  have hmeet : ∀ x ∈ p.support, x ∈ q.support → x = a ∨ x = b := by
    intro x hxp hxq
    by_contra h
    push Not at h
    have hxpt : x ∈ p.support.tail :=
      (SimpleGraph.Walk.mem_support_iff p).mp hxp |>.resolve_left h.1
    have hxr : x ∈ r.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hxq
    have hxrt : x ∈ r.support.tail :=
      (SimpleGraph.Walk.mem_support_iff r).mp hxr |>.resolve_left h.2
    exact (List.disjoint_of_nodup_append htailNodup hxpt hxrt)
  have hsupp : ∀ x, x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support := by
    intro x
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c a ha]
    change x ∈ c'.support ↔ x ∈ p.support ∨ x ∈ q.support
    rw [← hdecomp, SimpleGraph.Walk.mem_support_append_iff]
    simp only [q, SimpleGraph.Walk.support_reverse, List.mem_reverse]
  have hedg : ∀ e : Sym2 V, e ∈ c'.edges ↔ e ∈ c.edges := fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  have hpEdges : ∀ e, e ∈ p.edges → e ∈ c.edges := by
    intro e he
    apply (hedg e).mp
    exact SimpleGraph.Walk.edges_takeUntil_subset_edges c' hb' he
  have hqEdges : ∀ e, e ∈ q.edges → e ∈ c.edges := by
    intro e he
    apply (hedg e).mp
    apply SimpleGraph.Walk.edges_dropUntil_subset_edges c' hb'
    simpa [q, SimpleGraph.Walk.edges_reverse] using he
  exact ⟨p, q, hpPath, hqPath, hpPos, hqPos, hlen, hmeet, hsupp, hpEdges, hqEdges⟩

end Erdos556

